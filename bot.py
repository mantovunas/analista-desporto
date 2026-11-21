"""Analista diário de futebol -> Telegram (versão 7).

Fluxo:
 1. Resultados da época atual (football-data.org) + épocas anteriores (ficheiros CSV da
    football-data.co.uk, descarregados uma vez e guardados em "dados/").
 2. Modelo de Poisson com peso decrescente no tempo (meia-vida de 1 ano).
 3. Odds de várias casas (The Odds API) -> probabilidades do "mercado" (consenso).
 4. Previsão final = mistura de mercado (maior parte) e modelo. Testes retroativos mostraram
    que o mercado sozinho é o melhor previsor e que o modelo não o bate.
 5. Mostra favoritos claros, os jogos, e onde as odds pagam acima do consenso.
 6. Histórico (CSV em "historico/") para medir o desempenho real ao longo do tempo.
"""
import os
import re
import sys
import csv
import math
import time
import html
import difflib
import unicodedata
import datetime as dt
from zoneinfo import ZoneInfo
import requests

FD_KEY = os.environ["FOOTBALL_DATA_KEY"]
ODDS_KEY = os.environ["ODDS_API_KEY"]
TG_TOKEN = os.environ["TELEGRAM_TOKEN"]
TG_CHAT = os.environ["TELEGRAM_CHAT_ID"]
GEMINI_KEY = os.getenv("GEMINI_API_KEY", "")
AF_KEY = os.getenv("APIFOOTBALL_KEY", "")  # opcional: lesões (api-football.com, plano grátis)
GEMINI_MODEL = os.getenv("GEMINI_MODEL", "gemini-3.8-flash")
BOOKMAKER = os.getenv("BOOKMAKER", "betclic_fr")
ODDS_REGIONS = os.getenv("ODDS_REGIONS", "fr")

# código football-data.org: (nome, chave The Odds API)
LEAGUES = {
    "PPL": ("Liga Portugal", "soccer_portugal_primeira_liga"),
    "PL": ("Premier League", "soccer_epl"),
    "PD": ("La Liga", "soccer_spain_la_liga"),
    "ELC": ("Championship", "soccer_efl_champ"),
    "DED": ("Eredivisie", "soccer_netherlands_eredivisie"),
    "SA": ("Serie A", "soccer_italy_serie_a"),
    "BL1": ("Bundesliga", "soccer_germany_bundesliga"),
    "FL1": ("Ligue 1", "soccer_france_ligue_one"),
    "CL": ("Champions League", "soccer_uefa_champs_league"),
    "UNL": ("Liga das Nações", "soccer_uefa_nations_league"),
}
# Competições sem histórico gratuito (seleções): só mostra o consenso do mercado, sem modelo.
# Pedir só o resultado (1 crédito em vez de 2) nas competições menores; pedidos sem jogos não gastam créditos.
H2H_ONLY = {"CL", "UNL", "ELC", "DED"}
MARKET_ONLY = {"UNL", "CL"}  # CL: equipas de ligas diferentes e poucos jogos, o modelo não é fiável
# código na football-data.co.uk (épocas anteriores). A Champions não tem.
CO_UK = {"PPL": "P1", "PL": "E0", "PD": "SP1", "SA": "I1", "BL1": "D1", "FL1": "F1", "ELC": "E1", "DED": "N1"}

HOURS_AHEAD = 48       # jogos nas próximas X horas
FALLBACK_HOURS = 240   # se não houver jogos perto, mostra os próximos (10 dias)
FALLBACK_PER_LEAGUE = 3
MIN_GAMES = 4          # jogos (ponderados) mínimos por equipa para confiar
SHRINK = 3             # "jogos fictícios" na média, evita extremos
MAX_GOALS = 10

HALF_LIFE_DAYS = 365   # um jogo de há 1 ano conta metade (melhor valor no teste retroativo)
PRIOR_SEASONS = 2      # épocas anteriores a usar
DATA_DIR = "dados"

# previsão final = peso_modelo * modelo + (1 - peso_modelo) * mercado
def model_weight(n_books):
    if n_books >= 3: return 0.20
    if n_books == 2: return 0.35
    if n_books == 1: return 0.50
    return 1.00

# "odds acima do consenso": vantagem = prob_final * odd - 1
MIN_EDGE = 0.04
MAX_EDGE = 0.15        # acima disto desconfia-se (erro do modelo ou odd errada)
WARN_EDGE = 0.10
MIN_ODD, MAX_ODD = 1.40, 6.00
MIN_ODD_TIP = 1.15     # palpites mais prováveis: odds abaixo disto não pagam quase nada
CLEAR_FAV = 0.60       # "favorito claro" (nos testes acertou ~72-75% das vezes)

# histórico
HIST_DIR = "historico"
PICKS_FILE = f"{HIST_DIR}/sugestoes.csv"
PREDS_FILE = f"{HIST_DIR}/previsoes.csv"
STALE_DAYS = 7
MATCH_WINDOW_H = 36
MIN_SAMPLE = 100
PICK_FIELDS = [
    "id", "enviado_em", "liga", "casa", "fora", "fd_casa", "fd_fora", "inicio_utc",
    "sugestao", "selecao", "odd", "prob_modelo", "prob_mercado", "prob_final", "vantagem",
    "confianca", "casa_apostas", "estado", "golos_casa", "golos_fora", "lucro",
]
PRED_FIELDS = [
    "id", "enviado_em", "liga", "casa", "fora", "fd_casa", "fd_fora", "inicio_utc",
    "pH", "pD", "pA", "pO25", "pBTTS", "mH", "mD", "mA", "fH", "fD", "fA", "nb",
    "xg_casa", "xg_fora", "confianca", "estado", "golos_casa", "golos_fora", "m0H", "m0D", "m0A", "baixas_casa", "baixas_fora", "spread",
]

LISBON = ZoneInfo("Europe/Lisbon")
DIAS = ["Segunda", "Terça", "Quarta", "Quinta", "Sexta", "Sábado", "Domingo"]
DIAS_C = ["Seg", "Ter", "Qua", "Qui", "Sex", "Sáb", "Dom"]
NUMS = ["1️⃣", "2️⃣", "3️⃣", "4️⃣", "5️⃣", "6️⃣"]


def parse_iso(s):
    return dt.datetime.fromisoformat(s.replace("Z", "+00:00"))


def fnum(x):
    try:
        return float(x)
    except (TypeError, ValueError):
        return None


# ---------- nomes de equipas ----------
# Chaves já normalizadas (ver norm). Só o que a comparação aproximada não resolve sozinha.
ALIASES = {
    "man city": "manchester city", "man united": "manchester united", "man utd": "manchester united",
    "nottm forest": "nottingham forest", "wolves": "wolverhampton wanderers",
    "brighton hove albion": "brighton", "brighton and hove albion": "brighton",
    "espanol": "espanyol",
    "ath bilbao": "athletic", "athletic bilbao": "athletic",
    "ath madrid": "atletico madrid",
    "sp lisbon": "sporting", "sporting lisbon": "sporting", "sporting portugal": "sporting",
    "sp braga": "braga", "sporting braga": "braga",
    "guimaraes": "vitoria", "vitoria guimaraes": "vitoria",
    "bayern munich": "bayern", "bayern munchen": "bayern",
    "ein frankfurt": "eintracht frankfurt", "mgladbach": "borussia monchengladbach",
    "paris sg": "paris saint germain", "st etienne": "saint etienne", "rennes": "stade rennais 1901",
    "inter": "inter", "internazionale milano": "inter",
}


def norm(s):
    s = unicodedata.normalize("NFKD", s).encode("ascii", "ignore").decode("ascii").lower()
    s = re.sub(r"[^a-z0-9 ]", " ", s.replace("'", ""))
    s = re.sub(r"\b(fc|cf|sc|cd|afc|sad|club|clube|de|futebol|ac|ud|rc|rcd|ca|sl|gd|cp|and)\b", " ", s)
    return re.sub(r"\s+", " ", s).strip()


def canon(name):
    k = norm(name)
    return ALIASES.get(k, k)


def match_team(name, candidates, min_score=0.6):
    nn = canon(name)
    best, score = None, 0.0
    for c in candidates:
        cn = canon(c)
        if nn and nn == cn:
            return c
        r = difflib.SequenceMatcher(None, nn, cn).ratio()
        if min(len(nn), len(cn)) >= 4 and (nn in cn or cn in nn):
            r = max(r, 0.85)
        if r > score:
            best, score = c, r
    return best if score >= min_score else None


# ---------- dados ----------
def fd_matches(code, status="FINISHED"):
    r = requests.get(
        f"https://api.football-data.org/v4/competitions/{code}/matches",
        headers={"X-Auth-Token": FD_KEY},
        params={"status": status},
        timeout=30,
    )
    r.raise_for_status()
    time.sleep(7)  # limite grátis: 10 pedidos/min
    return r.json().get("matches", [])


def score90(m):
    """Golos aos 90 minutos (regularTime se houve prolongamento, senão fullTime)."""
    s = m.get("score", {})
    for key in ("regularTime", "fullTime"):
        v = s.get(key) or {}
        if v.get("home") is not None and v.get("away") is not None:
            return v["home"], v["away"]
    return None


def org_hist(matches):
    out = []
    for m in matches:
        sc = score90(m)
        if sc is None:
            continue
        out.append({"date": parse_iso(m["utcDate"]).date(), "home": m["homeTeam"]["name"],
                    "away": m["awayTeam"]["name"], "hg": sc[0], "ag": sc[1]})
    return out


def season_start(d):
    return d.year if d.month >= 7 else d.year - 1


def co_url(code, year):
    return f"https://www.football-data.co.uk/mmz4281/{year % 100:02d}{(year + 1) % 100:02d}/{code}.csv"


def fetch_season_csv(code, year):
    """Devolve o caminho do CSV da época (descarrega e guarda em dados/ se ainda não existir)."""
    path = f"{DATA_DIR}/{code}_{year}.csv"
    if os.path.exists(path):
        return path
    try:
        r = requests.get(co_url(code, year), timeout=30,
                         headers={"User-Agent": "Mozilla/5.0 (analista-futebol)"})
        head = r.content[:1500]
        if r.status_code == 200 and b"HomeTeam" in head and b"FTHG" in head:
            os.makedirs(DATA_DIR, exist_ok=True)
            with open(path, "wb") as f:
                f.write(r.content)
            print(f"Descarregado: {path}", file=sys.stderr)
            return path
        print(f"Não consegui descarregar {path} (HTTP {r.status_code})", file=sys.stderr)
    except Exception as e:  # noqa: BLE001
        print(f"Não consegui descarregar {path}: {e}", file=sys.stderr)
    return None


def parse_co_date(s):
    for fmt in ("%d/%m/%Y", "%d/%m/%y"):
        try:
            return dt.datetime.strptime(s.strip(), fmt).date()
        except ValueError:
            pass
    return None


def load_prior(code, today):
    """Jogos das épocas anteriores (nomes da football-data.co.uk)."""
    out = []
    cur = season_start(today)
    for year in range(cur - 1, cur - 1 - PRIOR_SEASONS, -1):
        path = fetch_season_csv(code, year)
        if not path:
            continue
        with open(path, newline="", encoding="utf-8-sig", errors="replace") as f:
            for r in csv.DictReader(f):
                d = parse_co_date(r.get("Date", ""))
                try:
                    hg, ag = int(r["FTHG"]), int(r["FTAG"])
                except (KeyError, ValueError, TypeError):
                    continue
                if d is None:
                    continue
                out.append({"date": d, "home": r["HomeTeam"].strip(), "away": r["AwayTeam"].strip(),
                            "hg": hg, "ag": ag})
    return out


def map_prior(prior, org_names):
    """Traduz os nomes das equipas dos CSV para os nomes da football-data.org."""
    cache = {}

    def mp(n):
        if n not in cache:
            cache[n] = match_team(n, org_names, min_score=0.72) or n
        return cache[n]

    mapped = [{**m, "home": mp(m["home"]), "away": mp(m["away"])} for m in prior]
    seen = {m["home"] for m in mapped} | {m["away"] for m in mapped}
    return mapped, sorted(t for t in org_names if t not in seen)


def build_strengths(hist, today):
    gf, ga, n = {}, {}, {}
    th = ta = ws = 0.0
    cnt = 0
    for m in hist:
        w = 0.5 ** (max(0, (today - m["date"]).days) / HALF_LIFE_DAYS)
        h, a = m["home"], m["away"]
        for t in (h, a):
            gf.setdefault(t, 0.0); ga.setdefault(t, 0.0); n.setdefault(t, 0.0)
        gf[h] += w * m["hg"]; ga[h] += w * m["ag"]; n[h] += w
        gf[a] += w * m["ag"]; ga[a] += w * m["hg"]; n[a] += w
        th += w * m["hg"]; ta += w * m["ag"]; ws += w; cnt += 1
    if cnt < 10 or ws <= 0:
        return None
    avg_h, avg_a = th / ws, ta / ws
    avg_team = (avg_h + avg_a) / 2
    att = {t: ((gf[t] + SHRINK * avg_team) / (n[t] + SHRINK)) / avg_team for t in n}
    dfn = {t: ((ga[t] + SHRINK * avg_team) / (n[t] + SHRINK)) / avg_team for t in n}
    return {"att": att, "def": dfn, "n": n, "avg_h": avg_h, "avg_a": avg_a}


def odds_events(sport, markets="h2h,totals"):
    r = requests.get(
        f"https://api.the-odds-api.com/v4/sports/{sport}/odds",
        params={
            "apiKey": ODDS_KEY, "regions": ODDS_REGIONS,
            "markets": markets, "oddsFormat": "decimal",
        },
        timeout=30,
    )
    if r.status_code != 200:
        print("Odds erro", sport, r.status_code, r.text[:200], file=sys.stderr)
        return []
    return r.json()


# ---------- modelo ----------
def pois(k, lam):
    return math.exp(-lam) * lam ** k / math.factorial(k)


def predict(st, home, away):
    lh = st["att"][home] * st["def"][away] * st["avg_h"]
    la = st["att"][away] * st["def"][home] * st["avg_a"]
    p = {"H": 0, "D": 0, "A": 0, "O25": 0, "BTTS": 0}
    for i in range(MAX_GOALS + 1):
        for j in range(MAX_GOALS + 1):
            pr = pois(i, lh) * pois(j, la)
            if i > j: p["H"] += pr
            elif i == j: p["D"] += pr
            else: p["A"] += pr
            if i + j > 2: p["O25"] += pr
            if i > 0 and j > 0: p["BTTS"] += pr
    tot = p["H"] + p["D"] + p["A"]
    for k in ("H", "D", "A", "O25", "BTTS"):
        p[k] /= tot
    p["lh"], p["la"] = lh, la
    return p


# ---------- mercado ----------
def devig(odds):
    q = [1 / o for o in odds]
    s = sum(q)
    return tuple(x / s for x in q)


def consensus(ev):
    """Média, entre casas, das probabilidades sem a margem (1X2 e +2.5 golos)."""
    h2h, tot = [], []
    for b in ev.get("bookmakers", []):
        for mk in b["markets"]:
            if mk["key"] == "h2h":
                d = {o["name"]: o["price"] for o in mk["outcomes"]}
                ph, pa, pd_ = d.get(ev["home_team"]), d.get(ev["away_team"]), d.get("Draw")
                if ph and pa and pd_:
                    h2h.append(devig((ph, pd_, pa)))
            elif mk["key"] == "totals":
                ov = un = None
                for o in mk["outcomes"]:
                    if o.get("point") == 2.5:
                        if o["name"] == "Over": ov = o["price"]
                        elif o["name"] == "Under": un = o["price"]
                if ov and un:
                    tot.append(devig((ov, un))[0])
    res = {"h2h": None, "o25": None, "n": len(h2h), "nt": len(tot), "spread": 0.0}
    if len(h2h) >= 3:
        res["spread"] = max(max(x[i] for x in h2h) - min(x[i] for x in h2h) for i in range(3))
    if h2h:
        res["h2h"] = tuple(sum(x[i] for x in h2h) / len(h2h) for i in range(3))  # H, D, A
    if tot:
        res["o25"] = sum(tot) / len(tot)
    return res


def pick_odds(ev):
    """Melhor odd por seleção, dando prioridade à casa preferida (Betclic) quando existe."""
    pref, best = {}, {}

    def upd(sel, price, b):
        if sel not in best or price > best[sel][0]:
            best[sel] = (price, b["title"])
        if b["key"] == BOOKMAKER:
            pref[sel] = (price, b["title"])

    for b in ev.get("bookmakers", []):
        for mk in b["markets"]:
            if mk["key"] == "h2h":
                for o in mk["outcomes"]:
                    sel = "H" if o["name"] == ev["home_team"] else "A" if o["name"] == ev["away_team"] else "D"
                    upd(sel, o["price"], b)
            elif mk["key"] == "totals":
                for o in mk["outcomes"]:
                    if o.get("point") == 2.5:
                        upd("O" if o["name"] == "Over" else "U", o["price"], b)
    return {sel: pref.get(sel) or best[sel] for sel in best}


def analyse_market_only(ev):
    mk = consensus(ev)
    if not mk["h2h"]:
        return None
    return {
        "id": ev.get("id") or f"{ev['home_team']}|{ev['away_team']}|{ev['commence_time']}",
        "home": ev["home_team"], "away": ev["away_team"], "time": ev["commence_time"],
        "fd_home": ev["home_team"], "fd_away": ev["away_team"],
        "p": None, "model": None, "market": mk["h2h"], "final": mk["h2h"],
        "final_o": mk["o25"], "nb": mk["n"], "conf": "baixa", "picks": [], "market_only": True,
        "books": sorted({b["title"] for b in ev.get("bookmakers", [])}),
        "has_pref": any(b["key"] == BOOKMAKER for b in ev.get("bookmakers", [])),
        "odds": pick_odds(ev),
    }


def analyse_event(ev, st):
    home = match_team(ev["home_team"], st["att"].keys())
    away = match_team(ev["away_team"], st["att"].keys())
    if not home or not away or not ev.get("bookmakers"):
        return None
    p = predict(st, home, away)
    model = (p["H"], p["D"], p["A"])
    mk = consensus(ev)
    w = model_weight(mk["n"])
    if mk["h2h"]:
        final = tuple(w * a + (1 - w) * b for a, b in zip(model, mk["h2h"]))
    else:
        final = model
    wt = model_weight(mk["nt"])
    final_o = wt * p["O25"] + (1 - wt) * mk["o25"] if mk["o25"] is not None else p["O25"]
    nmin = min(st["n"][home], st["n"][away])
    conf = "alta" if nmin >= 10 else ("média" if nmin >= MIN_GAMES else "baixa")
    spread_warn = mk["spread"] >= SPREAD_WARN
    if spread_warn:
        conf = {"alta": "média", "média": "baixa"}.get(conf, conf)

    labels = {"H": f"Vitória {ev['home_team']}", "D": "Empate", "A": f"Vitória {ev['away_team']}",
              "O": "Mais de 2.5 golos", "U": "Menos de 2.5 golos"}
    prob = {"H": (final[0], model[0], mk["h2h"][0] if mk["h2h"] else None),
            "D": (final[1], model[1], mk["h2h"][1] if mk["h2h"] else None),
            "A": (final[2], model[2], mk["h2h"][2] if mk["h2h"] else None),
            "O": (final_o, p["O25"], mk["o25"]),
            "U": (1 - final_o, 1 - p["O25"], 1 - mk["o25"] if mk["o25"] is not None else None)}
    picks = []
    for sel, (odd, book) in pick_odds(ev).items():
        if sel in ("O", "U") and mk["nt"] < 2:
            continue  # mais/menos 2.5 só com 2+ casas: com uma só, o "consenso" é essa casa
        pf, pm, pk = prob[sel]
        edge = pf * odd - 1
        if MIN_EDGE <= edge <= MAX_EDGE and MIN_ODD <= odd <= MAX_ODD:
            picks.append({"label": labels[sel], "sel": sel, "odd": odd, "book": book,
                          "prob": pf, "p_model": pm, "p_market": pk, "edge": edge})
    return {
        "id": ev.get("id") or f"{ev['home_team']}|{ev['away_team']}|{ev['commence_time']}",
        "home": ev["home_team"], "away": ev["away_team"], "time": ev["commence_time"],
        "fd_home": home, "fd_away": away,
        "p": p, "model": model, "market": mk["h2h"], "final": final, "final_o": final_o,
        "why": {"att_h": st["att"][home], "def_h": st["def"][home], "att_a": st["att"][away], "def_a": st["def"][away]},
        "nb": mk["n"], "conf": conf, "picks": picks,
        "spread": mk["spread"], "spread_warn": spread_warn,
        "books": sorted({b["title"] for b in ev.get("bookmakers", [])}),
        "has_pref": any(b["key"] == BOOKMAKER for b in ev.get("bookmakers", [])),
        "odds": pick_odds(ev),
    }


# ---------- histórico ----------
def read_csv(path):
    if not os.path.exists(path):
        return []
    with open(path, newline="", encoding="utf-8") as f:
        return list(csv.DictReader(f))


def write_csv(path, fields, rows):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=fields, restval="", extrasaction="ignore")
        w.writeheader()
        w.writerows(rows)


def add_index(idx, matches):
    for m in matches:
        sc = score90(m)
        if sc is None:
            continue
        key = (m["homeTeam"]["name"], m["awayTeam"]["name"])
        idx.setdefault(key, []).append((parse_iso(m["utcDate"]), sc[0], sc[1]))


def find_result(idx, home, away, kickoff):
    for t, gh, ga in idx.get((home, away), []):
        if abs((t - kickoff).total_seconds()) <= MATCH_WINDOW_H * 3600:
            return gh, ga
    return None


def outcome(sel, gh, ga):
    if sel == "H": return gh > ga
    if sel == "D": return gh == ga
    if sel == "A": return gh < ga
    if sel == "O": return gh + ga > 2
    if sel == "U": return gh + ga < 3
    return False


def settle(picks, preds, idx, now):
    newly = []
    for r in picks:
        if r["estado"] != "pendente":
            continue
        ko = parse_iso(r["inicio_utc"])
        if ko > now:
            continue
        res = find_result(idx, r["fd_casa"], r["fd_fora"], ko)
        if res:
            gh, ga = res
            won = outcome(r["selecao"], gh, ga)
            r["golos_casa"], r["golos_fora"] = gh, ga
            r["estado"] = "ganha" if won else "perdida"
            r["lucro"] = f"{(float(r['odd']) - 1) if won else -1:.2f}"
            newly.append(r)
        elif (now - ko).days >= STALE_DAYS:
            r["estado"] = "sem_resultado"
    for r in preds:
        if r["estado"] != "pendente":
            continue
        ko = parse_iso(r["inicio_utc"])
        if ko > now:
            continue
        res = find_result(idx, r["fd_casa"], r["fd_fora"], ko)
        if res:
            r["golos_casa"], r["golos_fora"] = res
            r["estado"] = "resolvida"
        elif (now - ko).days >= STALE_DAYS:
            r["estado"] = "sem_resultado"
    return newly


def log_new(picks, preds, all_results, shown, now):
    stamp = now.strftime("%Y-%m-%dT%H:%M:%SZ")
    by_id = {r["id"]: r for r in preds}
    for league, games in all_results.items():
        for g in games:
            if g.get("market_only"):
                continue  # sem modelo e sem resultados gratuitos para avaliar
            p = g["p"]
            vals = {
                "pH": f"{p['H']:.4f}", "pD": f"{p['D']:.4f}", "pA": f"{p['A']:.4f}",
                "pO25": f"{p['O25']:.4f}", "pBTTS": f"{p['BTTS']:.4f}",
                "fH": f"{g['final'][0]:.4f}", "fD": f"{g['final'][1]:.4f}", "fA": f"{g['final'][2]:.4f}",
                "mH": f"{g['market'][0]:.4f}" if g["market"] else "",
                "mD": f"{g['market'][1]:.4f}" if g["market"] else "",
                "mA": f"{g['market'][2]:.4f}" if g["market"] else "",
                "nb": g["nb"], "xg_casa": f"{p['lh']:.2f}", "xg_fora": f"{p['la']:.2f}",
                "confianca": g["conf"], "inicio_utc": g["time"],
                "baixas_casa": len(g["inj"]["home"]) if g.get("inj") else "",
                "baixas_fora": len(g["inj"]["away"]) if g.get("inj") else "",
                "spread": f"{g.get('spread', 0):.3f}",
            }
            old = by_id.get(g["id"])
            if old is None:
                first = {f"m0{k}": vals[f"m{k}"] for k in "HDA"}  # 1.ª leitura do mercado (nunca é atualizada)
                row = {"id": g["id"], "enviado_em": stamp, "liga": league,
                       "casa": g["home"], "fora": g["away"],
                       "fd_casa": g["fd_home"], "fd_fora": g["fd_away"],
                       "estado": "pendente", **vals, **first}
                preds.append(row)
                by_id[g["id"]] = row
            elif old["estado"] == "pendente":
                old.update(vals)
    have = {(r["id"], r["selecao"]) for r in picks}
    for league, games in shown.items():
        for g in games:
            for pk in g["picks"]:
                if (g["id"], pk["sel"]) in have:
                    continue
                picks.append({
                    "id": g["id"], "enviado_em": stamp, "liga": league,
                    "casa": g["home"], "fora": g["away"],
                    "fd_casa": g["fd_home"], "fd_fora": g["fd_away"],
                    "inicio_utc": g["time"], "sugestao": pk["label"], "selecao": pk["sel"],
                    "odd": f"{pk['odd']:.2f}", "prob_modelo": f"{pk['p_model']:.4f}",
                    "prob_mercado": f"{pk['p_market']:.4f}" if pk["p_market"] is not None else "",
                    "prob_final": f"{pk['prob']:.4f}", "vantagem": f"{pk['edge']:.4f}",
                    "confianca": g["conf"], "casa_apostas": pk["book"], "estado": "pendente",
                })
                have.add((g["id"], pk["sel"]))


# ---------- saída (Telegram em HTML) ----------
def esc(s):
    return html.escape(str(s))


def fmt_time(iso):
    t = parse_iso(iso).astimezone(LISBON)
    return f"{DIAS_C[t.weekday()]} {t:%d/%m} · {t:%H:%M}"


def bar(p, n=10):
    f = round(p * n)
    return "▰" * f + "▱" * (n - f)


def conf_txt(c):
    return {"alta": "🟢 alta", "média": "🟡 média", "baixa": "🔴 baixa"}[c]


def pct3(t):
    return "/".join(f"{x:.0%}".rstrip("%") for x in t) + "%"


# ---------- extras: resultados exatos, porquê, lesões ----------
def top_scores(lh, la, k=3):
    """Os k resultados exatos mais prováveis, segundo o modelo de Poisson."""
    sc = [((i, j), pois(i, lh) * pois(j, la)) for i in range(7) for j in range(7)]
    return sorted(sc, key=lambda x: -x[1])[:k]


def why_line(g):
    w = g.get("why")
    if not w:
        return ""
    def tag(x):  # >1 = acima da média da liga
        return f"{x:.2f}×"
    return (f"🔬 Ataque/defesa (1.00 = média da liga): {esc(g['home'])} {tag(w['att_h'])} / {tag(w['def_h'])} · "
            f"{esc(g['away'])} {tag(w['att_a'])} / {tag(w['def_a'])} (defesa acima de 1 = sofre mais)")


INJ_WARN = 3
SPREAD_WARN = 0.07     # casas discordam >= 7 pontos num resultado: confiança desce
DUEL_GAP = 0.08        # 'grande desacordo' modelo vs mercado (diferença máx. numa probabilidade)  # 3+ baixas numa equipa: a confiança desce um nível
AF_LEAGUES = {"PL": 39, "ELC": 40, "PD": 140, "SA": 135, "BL1": 78, "FL1": 61, "PPL": 94, "DED": 88, "CL": 2}


def af_injuries(league_id, season, day):
    """Lesionados/suspensos de uma liga num dia (API-Football). Devolve [(equipa, jogador, motivo)]."""
    r = requests.get("https://v3.football.api-sports.io/injuries",
                     headers={"x-apisports-key": AF_KEY},
                     params={"league": league_id, "season": season, "date": day}, timeout=30)
    data = r.json()
    if r.status_code != 200 or data.get("errors"):
        print("API-Football:", r.status_code, str(data.get("errors"))[:200], file=sys.stderr)
        return []
    out = []
    for it in data.get("response", []):
        out.append((it.get("team", {}).get("name", ""), it.get("player", {}).get("name", ""),
                    it.get("player", {}).get("reason") or it.get("player", {}).get("type") or ""))
    return out


def attach_injuries(shown, league_codes, today):
    """Junta a cada jogo mostrado a lista de baixas (só se houver chave da API-Football)."""
    if not AF_KEY:
        return
    season = season_start(today)
    cache = {}
    for name, games in shown.items():
        code = league_codes.get(name)
        if not code or code not in AF_LEAGUES:
            continue
        for g in games:
            day = parse_iso(g["time"]).date().isoformat()
            key = (code, day)
            try:
                if key not in cache:
                    cache[key] = af_injuries(AF_LEAGUES[code], season, day)
                rows = cache[key]
                if not rows:
                    continue
                teams = sorted({r[0] for r in rows})
                th = match_team(g["home"], teams, 0.72)
                ta = match_team(g["away"], teams, 0.72)
                g["inj"] = {"home": [(p, m) for t, p, m in rows if t == th] if th else [],
                            "away": [(p, m) for t, p, m in rows if t == ta] if ta else []}
                if max(len(g["inj"]["home"]), len(g["inj"]["away"])) >= INJ_WARN and not g.get("market_only"):
                    g["conf"] = {"alta": "média", "média": "baixa"}.get(g["conf"], g["conf"])
                    g["inj_warn"] = True
            except Exception as e:  # noqa: BLE001
                print("Lesões falharam:", e, file=sys.stderr)


def inj_line(g):
    inj = g.get("inj")
    if not inj or not (inj["home"] or inj["away"]):
        return ""
    def fmt(lst):
        shown = ", ".join(f"{esc(p)} ({esc(m)})" if m else esc(p) for p, m in lst[:4])
        return shown + (f" +{len(lst) - 4}" if len(lst) > 4 else "")
    parts = []
    if inj["home"]: parts.append(f"{esc(g['home'])}: {fmt(inj['home'])}")
    if inj["away"]: parts.append(f"{esc(g['away'])}: {fmt(inj['away'])}")
    warn = "⚠️ Muitas baixas: confiança reduzida. " if g.get("inj_warn") else ""
    return "🚑 Baixas — " + " · ".join(parts) + "\n<i>" + warn + "(o modelo não conta lesões)</i>"


LEAGUE_ICON = {"Championship": "🏴\U000e0067\U000e0062\U000e0065\U000e006e\U000e0067\U000e007f", "Eredivisie": "🇳🇱", "Liga Portugal": "🇵🇹", "Premier League": "🏴\U000e0067\U000e0062\U000e0065\U000e006e\U000e0067\U000e007f",
               "La Liga": "🇪🇸", "Serie A": "🇮🇹", "Bundesliga": "🇩🇪", "Ligue 1": "🇫🇷",
               "Champions League": "⭐", "Liga das Nações": "🌍"}


def probs_line(f):
    """Barra de 10 quadrados dividida pelas 3 probabilidades: 🟩 casa · 🟨 empate · 🟦 fora."""
    raw = [x * 10 for x in f]
    n = [int(x) for x in raw]
    for i in sorted(range(3), key=lambda i: raw[i] - n[i], reverse=True)[: 10 - sum(n)]:
        n[i] += 1
    return f"{'🟩' * n[0]}{'🟨' * n[1]}{'🟦' * n[2]}\n🏠 {f[0]:.0%}  🤝 {f[1]:.0%}  ✈️ {f[2]:.0%}"


def game_block(g):
    f = g["final"]
    head = [f"🕗 <i>{fmt_time(g['time'])}</i>", f"<b>{esc(g['home'])}</b> vs <b>{esc(g['away'])}</b>", probs_line(f)]
    pref = "✅ Betclic" if g["has_pref"] else "➖ sem Betclic"
    if g.get("market_only"):
        extra = f" · +2.5: {g['final_o']:.0%}" if g["final_o"] is not None else ""
        head.append(f"🏦 Só mercado{extra}")
        detail = f"📚 {g['nb']} casa(s) · {pref}\n(sem modelo fiável nesta competição)"
    else:
        p = g["p"]
        head.append(f"⚽ {p['lh']:.1f}–{p['la']:.1f} · +2.5: {g['final_o']:.0%} · {conf_txt(g['conf'])}")
        mk = pct3(g["market"]) if g["market"] else "sem mercado"
        scores = " · ".join(f"{i}–{j} ({pr:.0%})" for (i, j), pr in top_scores(p["lh"], p["la"]))
        detail = (f"🧠 Modelo {pct3(g['model'])} · 🏦 Mercado {mk}\n"
                  f"🎯 Resultados mais prováveis: {scores}\n"
                  f"Ambas marcam: {p['BTTS']:.0%} · 📚 {g['nb']} casa(s) · {pref}")
        spread_note = (f"⚠️ As casas discordam entre si ({g['spread'] * 100:.0f} pontos): confiança reduzida."
                       if g.get("spread_warn") else "")
        for extra_line in (why_line(g), spread_note, inj_line(g)):
            if extra_line:
                detail += "\n" + extra_line
    # os detalhes ficam escondidos: toca para abrir
    head.append(f"<blockquote expandable>{detail}</blockquote>")
    return "\n".join(head)



def fav_label(g):
    f = g["final"]
    i = max(range(3), key=lambda k: f[k])
    name = (g["home"], "Empate", g["away"])[i]
    return name, f[i]


def _trio(r, a, b, c):
    v = (fnum(r.get(a)), fnum(r.get(b)), fnum(r.get(c)))
    return v if None not in v else None


def _final_probs(r):
    return _trio(r, "fH", "fD", "fA") or _trio(r, "pH", "pD", "pA")


def _result_idx(r):
    gh, ga = int(r["golos_casa"]), int(r["golos_fora"])
    return 0 if gh > ga else (1 if gh == ga else 2)


def _brier(rows, keys):
    tot = n = 0
    for r in rows:
        p = _trio(r, *keys)
        if p is None:
            continue
        y = [0.0, 0.0, 0.0]
        y[_result_idx(r)] = 1.0
        tot += sum((a - b) ** 2 for a, b in zip(p, y))
        n += 1
    return (tot / n) if n else None


def favourite_streaks(preds):
    """Sequência atual e melhor sequência de favoritos claros (>= CLEAR_FAV) acertados."""
    rows = []
    for r in preds:
        if r.get("estado") != "resolvida":
            continue
        p = _final_probs(r)
        if p and max(p) >= CLEAR_FAV:
            rows.append((r["inicio_utc"], p.index(max(p)) == _result_idx(r)))
    rows.sort()
    best = cur = 0
    for _, ok in rows:
        cur = cur + 1 if ok else 0
        best = max(best, cur)
    return cur, best, len(rows)


def duel(rows):
    """Nos jogos com grande desacordo modelo vs mercado, quem esteve mais perto do resultado (erro de Brier por jogo)."""
    m = k = n = 0
    for r in rows:
        if r.get("estado") != "resolvida":
            continue
        a, b = _trio(r, "pH", "pD", "pA"), _trio(r, "mH", "mD", "mA")
        if a is None or b is None or max(abs(x - y) for x, y in zip(a, b)) < DUEL_GAP:
            continue
        y = [0.0, 0.0, 0.0]
        y[_result_idx(r)] = 1.0
        ea, eb = sum((p - q) ** 2 for p, q in zip(a, y)), sum((p - q) ** 2 for p, q in zip(b, y))
        n += 1
        if ea < eb: m += 1
        elif eb < ea: k += 1
    return m, k, n


def duel_line(rows, label):
    m, k, n = duel(rows)
    if n < 3:
        return None
    return f"🥊 {label} (modelo e mercado discordavam muito, {n} jogos): Modelo {m} – Mercado {k}"


def weekly_block(picks, preds, now):
    """Resumo dos últimos 7 dias (enviado às segundas-feiras)."""
    lo = now - dt.timedelta(days=7)
    rp = [r for r in preds if r.get("estado") == "resolvida" and lo <= parse_iso(r["inicio_utc"]) <= now]
    if not rp:
        return None
    lines = ["📅 <b>SEMANA PASSADA</b>", ""]
    hit = sum(1 for r in rp if _final_probs(r) and _final_probs(r).index(max(_final_probs(r))) == _result_idx(r))
    lines.append(f"⚽ {len(rp)} jogos avaliados · resultado mais provável acertou {hit}/{len(rp)} ({hit / len(rp):.0%})")
    fav = [r for r in rp if _final_probs(r) and max(_final_probs(r)) >= CLEAR_FAV]
    if fav:
        ok = sum(1 for r in fav if _final_probs(r).index(max(_final_probs(r))) == _result_idx(r))
        lines.append(f"⭐ Favoritos claros: {ok}/{len(fav)} ({ok / len(fav):.0%})")
    bb, bm, bk = _brier(rp, ("fH", "fD", "fA")), _brier(rp, ("pH", "pD", "pA")), _brier(rp, ("mH", "mD", "mA"))
    parts = [f"bot {bb:.3f}" if bb is not None else None, f"modelo {bm:.3f}" if bm is not None else None,
             f"mercado {bk:.3f}" if bk is not None else None]
    parts = [x for x in parts if x]
    if parts:
        lines.append("📐 Erro (mais baixo = melhor): " + " · ".join(parts))
    wk = [r for r in picks if r.get("estado") in ("ganha", "perdida") and lo <= parse_iso(r["inicio_utc"]) <= now]
    if wk:
        profit = sum(float(r["lucro"]) for r in wk)
        lines.append(f"🎯 Sugestões: {len(wk)} resolvidas · {profit:+.2f} unidades (ROI {profit / len(wk):+.0%})")
    for rows_, lab in ((rp, "Semana"), ([r for r in preds], "Desde o início")):
        dl = duel_line(rows_, lab)
        if dl:
            lines.append(dl)
    lines.append("<i>Uma semana é pouco: só dá para tirar conclusões com várias semanas.</i>")
    return "\n".join(lines)


def history_blocks(picks, preds, newly):
    blocks = []
    if newly:
        lines = ["📋 <b>RESULTADOS DAS SUGESTÕES ANTERIORES</b>", ""]
        for r in newly[:8]:
            icon = "✅" if r["estado"] == "ganha" else "❌"
            lines.append(
                f"{icon} <b>{esc(r['sugestao'])}</b> @ {float(r['odd']):.2f} "
                f"({float(r['lucro']):+.2f})\n"
                f"   {esc(r['casa'])} {r['golos_casa']}–{r['golos_fora']} {esc(r['fora'])}"
            )
        if len(newly) > 8:
            lines.append(f"… e mais {len(newly) - 8}.")
        blocks.append("\n".join(lines))

    res = [r for r in picks if r["estado"] in ("ganha", "perdida")]
    pend = [r for r in picks if r["estado"] == "pendente"]
    lost = [r for r in picks if r["estado"] == "sem_resultado"]
    rp = [r for r in preds if r["estado"] == "resolvida"]
    lines = ["📊 <b>DESEMPENHO DO BOT</b>", ""]

    def trio(r, a, b, c):
        v = (fnum(r.get(a)), fnum(r.get(b)), fnum(r.get(c)))
        return v if None not in v else None

    def stats(rows, keys):
        """Brier e acerto do resultado mais provável; keys = ('pH','pD','pA') etc."""
        brier = hit = n = 0
        for r in rows:
            p = trio(r, *keys)
            if p is None:
                continue
            gh, ga = int(r["golos_casa"]), int(r["golos_fora"])
            y = (float(gh > ga), float(gh == ga), float(gh < ga))
            brier += sum((a - b) ** 2 for a, b in zip(p, y))
            hit += y[p.index(max(p))]
            n += 1
        return (brier / n, hit / n, n) if n else None

    if res:
        n = len(res)
        wins = sum(1 for r in res if r["estado"] == "ganha")
        profit = sum(float(r["lucro"]) for r in res)
        lines += [
            f"🎯 Sugestões resolvidas: {n} · acertou {wins} ({wins / n:.0%})",
            f"💶 Com 1 unidade por sugestão: <b>{profit:+.2f}</b> (ROI {profit / n:+.0%})",
        ]
    else:
        lines.append("Ainda sem sugestões resolvidas.")
    if pend:
        lines.append(f"⏳ Por resolver: {len(pend)}")
    if lost:
        lines.append(f"❓ Sem resultado encontrado: {len(lost)} (pode ser nome de equipa por emparelhar)")
    if rp:
        sm = stats(rp, ("pH", "pD", "pA"))
        sk = stats(rp, ("mH", "mD", "mA"))
        sf = stats(rp, ("fH", "fD", "fA"))
        if sf:
            lines.append(f"🔮 Previsões 1X2 avaliadas: {sf[2]} · resultado mais provável acertou {sf[1]:.0%}")
            lines.append(f"📐 Erro de Brier (mais baixo = melhor): bot {sf[0]:.3f}"
                         + (f" · modelo {sm[0]:.3f}" if sm else "")
                         + (f" · mercado {sk[0]:.3f}" if sk else ""))
        elif sm:
            lines.append(f"🔮 Previsões 1X2 avaliadas: {sm[2]} · resultado mais provável acertou {sm[1]:.0%} · Brier {sm[0]:.3f}")
        fav = [r for r in rp if (trio(r, "fH", "fD", "fA") or trio(r, "pH", "pD", "pA")) and
               max(trio(r, "fH", "fD", "fA") or trio(r, "pH", "pD", "pA")) >= CLEAR_FAV]
        if fav:
            ok = 0
            for r in fav:
                p = trio(r, "fH", "fD", "fA") or trio(r, "pH", "pD", "pA")
                gh, ga = int(r["golos_casa"]), int(r["golos_fora"])
                y = (gh > ga, gh == ga, gh < ga)
                ok += 1 if y[p.index(max(p))] else 0
            lines.append(f"⭐ Favoritos claros (≥{CLEAR_FAV:.0%}): {len(fav)} jogos · acertou {ok / len(fav):.0%}")
        cur, best, nfav = favourite_streaks(preds)
        if nfav:
            lines.append(f"🔥 Favoritos claros seguidos certos: {cur} (melhor sequência: {best})")
        lines.append("<i>Brier: 0.667 equivale a chutar; o mercado costuma ficar perto de 0.57.</i>")
    if len(res) < MIN_SAMPLE:
        lines.append(f"⚠️ <i>Amostra pequena ({len(res)} sugestões): só é fiável a partir de {MIN_SAMPLE}+.</i>")
    blocks.append("\n".join(lines))
    return blocks


def build_blocks(results, fallback, extra=None):
    now = dt.datetime.now(LISBON)
    all_games = [g for games in results.values() for g in games]
    club = [g for g in all_games if not g.get("market_only")]
    favs = sorted((g for g in club if fav_label(g)[1] >= CLEAR_FAV), key=lambda g: -fav_label(g)[1])
    all_picks, books = [], set()
    for league, games in results.items():
        for g in games:
            books.update(g["books"])
            for pk in g["picks"]:
                all_picks.append((pk["edge"], g, pk))
    all_picks.sort(key=lambda x: -x[0])

    blocks = [f"⚽ <b>ANALISTA DESPORTO</b>\n📅 {DIAS[now.weekday()]}, {now:%d/%m/%Y}\n━━━━━━━━━━━━━━━"]
    # 1) resumo curto no topo
    n_leagues = sum(1 for gs in results.values() if gs)
    lines = ["📌 <b>RESUMO</b>"]
    if fallback:
        lines.append("ℹ️ <i>Sem jogos nas próximas 48h (pausa?): mostro os próximos.</i>")
    if all_games:
        lines.append(f"🗓 {len(all_games)} jogos em {n_leagues} competição(ões)")
    else:
        lines.append("Sem jogos analisados nos próximos dias.")
    if club:
        eq = min(club, key=lambda g: max(g["final"]))
        gl = max(club, key=lambda g: g["p"]["lh"] + g["p"]["la"])
        lines.append("")
        lines.append(f"⚖️ <b>Mais equilibrado:</b> {esc(eq['home'])} vs {esc(eq['away'])} ({pct3(eq['final'])})")
        lines.append(f"🔥 <b>Mais golos esperados:</b> {esc(gl['home'])} vs {esc(gl['away'])} ({gl['p']['lh'] + gl['p']['la']:.1f})")
    if club:
        top = max(club, key=lambda g: max(g["final"]))
        name, pr = fav_label(top)
        lines.append(f"🏆 <b>Jogo do dia:</b> {esc(top['home'])} vs {esc(top['away'])} · {fmt_time(top['time'])}")
        lines.append(f"   {esc(name)} {pr:.0%} · golos esperados {top['p']['lh']:.1f}–{top['p']['la']:.1f}")
    lines.append("")
    lines.append(f"🔎 Odds acima do consenso: {len(all_picks)}" if all_picks else "🔎 Odds acima do consenso: nenhuma hoje 🧘")
    blocks.append("\n".join(lines))

    # palpites mais prováveis (probabilidade alta; não é o mesmo que bom negócio)
    cands = []
    for g in all_games:
        f = g["final"]
        opts = [("H", f"Vitória {g['home']}", f[0]), ("D", "Empate", f[1]), ("A", f"Vitória {g['away']}", f[2])]
        if g.get("final_o") is not None:
            opts += [("O", "Mais de 2.5 golos", g["final_o"]), ("U", "Menos de 2.5 golos", 1 - g["final_o"])]
        for sel, label, pr in opts:
            if pr >= CLEAR_FAV and sel in g.get("odds", {}) and g["odds"][sel][0] >= MIN_ODD_TIP:
                odd, book = g["odds"][sel]
                cands.append((pr, label, odd, book, g))
    cands.sort(key=lambda x: -x[0])
    seen, chosen = set(), []
    for c in cands:  # no máximo um palpite por jogo
        if c[4]["id"] not in seen:
            seen.add(c[4]["id"])
            chosen.append(c)
    if chosen:
        lines = ["🎯 <b>PALPITES MAIS PROVÁVEIS</b>", ""]
        for pr, label, odd, book, g in chosen[:5]:
            lines.append(f"• <b>{esc(label)}</b> · {pr:.0%} · odd {odd:.2f} ({esc(book)})\n"
                         f"   {esc(g['home'])} vs {esc(g['away'])} · {fmt_time(g['time'])}")
        lines.append("<i>Nos testes, palpites de 60%+ acertaram cerca de 72% das vezes. Mas mais provável não é o mesmo "
                     "que bom negócio: quanto mais provável, mais baixa a odd e menos paga. Não é conselho de aposta.</i>")
        blocks.append("\n".join(lines))

    # 2) jogos por competição (detalhes escondidos em cada jogo)
    for league, games in results.items():
        if not games:
            continue
        blocks.append(f"{LEAGUE_ICON.get(league, '🏆')} <b>{esc(league.upper())}</b>")
        for g in games:
            blocks.append(game_block(g))

    # 3) odds acima do consenso (compacto)
    if all_picks:
        lines = ["🔎 <b>ODDS ACIMA DO CONSENSO</b>"]
        for i, (edge, g, pk) in enumerate(all_picks[:4]):
            warn = " ⚠️" if edge > WARN_EDGE else ""
            lines.append(
                f"{NUMS[i]} <b>{esc(pk['label'])}</b> @ <b>{pk['odd']:.2f}</b> ({esc(pk['book'])}){warn}\n"
                f"   {esc(g['home'])} vs {esc(g['away'])} · {fmt_time(g['time'])} · previsão {pk['prob']:.0%} ({edge:+.0%})"
            )
        lines.append("<i>Nos testes, este tipo de sinal não deu lucro: serve para investigar, não para apostar.</i>")
        blocks.append("\n".join(lines))
    if extra:
        blocks.extend(extra)
    foot = []
    if books:
        nb_pref = sum(1 for g in all_games if g["has_pref"])
        foot.append("📚 Odds: " + esc(", ".join(sorted(books))) + f" · Betclic em {nb_pref}/{len(all_games)} jogos")
    foot.append("ℹ️ <i>Previsão = sobretudo o consenso do mercado + um toque do modelo. Toca na caixa de cada jogo para ver os detalhes.</i>")
    foot.append("⚠️ <i>Estimativa estatística, não garantia. Aposta com responsabilidade.</i>")
    foot.append("— <b>Analista Desporto</b> 🤖")
    blocks.append("\n".join(foot))
    return blocks



def plain_text(blocks):
    return re.sub(r"<[^>]+>", "", "\n\n".join(blocks))


def gemini_summary(text):
    if not GEMINI_KEY:
        return ""
    prompt = (
        "És um analista de futebol. Com base APENAS nestes dados do modelo, escreve em "
        "português de Portugal um resumo curto (máx. 6 linhas) dos jogos mais interessantes "
        "e dos riscos. Não inventes lesões nem notícias.\n\n" + text
    )
    for attempt in (1, 2):  # a Google falha às vezes: tenta duas vezes
        r = None
        try:
            r = requests.post(
                f"https://generativelanguage.googleapis.com/v1beta/models/{GEMINI_MODEL}:generateContent",
                params={"key": GEMINI_KEY},
                json={"contents": [{"parts": [{"text": prompt}]}]},
                timeout=60,
            )
            txt = r.json()["candidates"][0]["content"]["parts"][0]["text"].strip()
            return "🧠 <b>LEITURA DO DIA</b>\n" + esc(txt)
        except Exception as e:  # noqa: BLE001
            print(f"Gemini falhou (tentativa {attempt}):", e, file=sys.stderr)
            if r is not None:
                print("Resposta do Gemini:", r.text[:300], file=sys.stderr)
            if attempt == 1:
                time.sleep(8)
    return ""


def telegram(blocks):
    chunks, cur = [], ""
    for b in blocks:
        if cur and len(cur) + len(b) + 2 > 3800:
            chunks.append(cur)
            cur = b
        else:
            cur = f"{cur}\n\n{b}" if cur else b
    if cur:
        chunks.append(cur)
    url = f"https://api.telegram.org/bot{TG_TOKEN}/sendMessage"
    for c in chunks:
        r = requests.post(url, json={"chat_id": TG_CHAT, "text": c, "parse_mode": "HTML",
                                     "disable_web_page_preview": True}, timeout=30)
        if r.status_code == 400:  # formato não aceite: tenta sem a caixa escondida e, por fim, texto simples
            print("Telegram 400 (HTML):", r.text[:200], file=sys.stderr)
            c2 = c.replace("<blockquote expandable>", "<blockquote>")
            r = requests.post(url, json={"chat_id": TG_CHAT, "text": c2, "parse_mode": "HTML",
                                         "disable_web_page_preview": True}, timeout=30)
            if r.status_code == 400:
                r = requests.post(url, json={"chat_id": TG_CHAT, "text": re.sub(r"<[^>]+>", "", c)}, timeout=30)
        r.raise_for_status()


# ---------- simulador da época ----------
SIM_LEAGUES = {  # código: (nº de lugares "Champions", nº de lugares de descida)
    "PL": (4, 3), "PD": (4, 3), "SA": (4, 3), "BL1": (4, 2), "FL1": (3, 2), "PPL": (2, 2),
}
SIM_RUNS = 4000
SIM_FILE = f"{HIST_DIR}/simulacao.csv"
SIM_FIELDS = ["data", "liga", "equipa", "p_titulo", "p_champions", "p_descida", "pts_esperados"]


def current_table(matches):
    """Pontos, golos marcados e sofridos da época atual (resultados aos 90 minutos)."""
    t = {}
    for m in matches:
        sc = score90(m)
        if sc is None:
            continue
        h, a = m["homeTeam"]["name"], m["awayTeam"]["name"]
        for n in (h, a):
            t.setdefault(n, {"pts": 0, "gf": 0, "ga": 0})
        t[h]["gf"] += sc[0]; t[h]["ga"] += sc[1]; t[a]["gf"] += sc[1]; t[a]["ga"] += sc[0]
        if sc[0] > sc[1]: t[h]["pts"] += 3
        elif sc[0] == sc[1]:
            t[h]["pts"] += 1; t[a]["pts"] += 1
        else: t[a]["pts"] += 3
    return t


def simulate_league(table, fixtures, st, n_top, n_bottom, runs=SIM_RUNS, seed=0):
    """Simula o resto da época `runs` vezes. fixtures = [(casa, fora)] ainda por jogar."""
    import bisect
    import random
    rng = random.Random(seed)
    teams = sorted(set(table) | {x for f in fixtures for x in f})
    ix = {t: i for i, t in enumerate(teams)}
    n = len(teams)
    base_pts = [table.get(t, {}).get("pts", 0) for t in teams]
    base_gd = [table.get(t, {}).get("gf", 0) - table.get(t, {}).get("ga", 0) for t in teams]
    base_gf = [table.get(t, {}).get("gf", 0) for t in teams]
    fx = []
    for h, a in fixtures:
        att_h = st["att"].get(h, 1.0); def_h = st["def"].get(h, 1.0)
        att_a = st["att"].get(a, 1.0); def_a = st["def"].get(a, 1.0)
        lh = att_h * def_a * st["avg_h"]
        la = att_a * def_h * st["avg_a"]
        cum, outs, tot = [], [], 0.0
        for i in range(MAX_GOALS + 1):
            for j in range(MAX_GOALS + 1):
                tot += pois(i, lh) * pois(j, la)
                cum.append(tot); outs.append((i, j))
        cum = [c / tot for c in cum]
        fx.append((ix[h], ix[a], cum, outs))
    title = [0] * n; top = [0] * n; bottom = [0] * n; pts_sum = [0.0] * n
    for _ in range(runs):
        pts = base_pts[:]; gd = base_gd[:]; gf = base_gf[:]
        for hi, ai, cum, outs in fx:
            i, j = outs[min(bisect.bisect_left(cum, rng.random()), len(outs) - 1)]
            gd[hi] += i - j; gd[ai] += j - i; gf[hi] += i; gf[ai] += j
            if i > j: pts[hi] += 3
            elif i == j:
                pts[hi] += 1; pts[ai] += 1
            else: pts[ai] += 3
        order = sorted(range(n), key=lambda k: -(pts[k] * 10**7 + (gd[k] + 1000) * 10**4 + gf[k] * 10 + rng.random() * 5))
        title[order[0]] += 1
        for pos, k in enumerate(order):
            if pos < n_top: top[k] += 1
            if pos >= n - n_bottom: bottom[k] += 1
        for k in range(n):
            pts_sum[k] += pts[k]
    return {t: {"p_titulo": title[ix[t]] / runs, "p_champions": top[ix[t]] / runs,
                "p_descida": bottom[ix[t]] / runs, "pts_esperados": pts_sum[ix[t]] / runs,
                "pts": base_pts[ix[t]]} for t in teams}


def prev_sim(rows, league, today):
    """Última simulação guardada com pelo menos 5 dias."""
    cutoff = (today - dt.timedelta(days=5)).isoformat()
    dates = sorted({r["data"] for r in rows if r["liga"] == league and r["data"] <= cutoff})
    if not dates:
        return {}
    return {r["equipa"]: r for r in rows if r["liga"] == league and r["data"] == dates[-1]}


def arrow(now_p, old_p):
    if old_p is None:
        return ""
    d = (now_p - old_p) * 100
    if d >= 2: return f" ⬆️+{d:.0f}"
    if d <= -2: return f" ⬇️{d:.0f}"
    return ""


def short_name(t):
    t = re.sub(r"^1\.\s*", "", t)
    t = re.sub(r"\b(FC|CF|AFC|SAD|AC|SC|CD|AS|RC|OGC|SS|SSC|US|TSG|VfB|VfL|SV|RB)\b\.?", " ", t)
    return re.sub(r"\s+", " ", t).strip() or t


def sim_block(league, res, prev, n_top, n_bottom, remaining):
    def old(t, k):
        try:
            return float(prev[t][k])
        except (KeyError, ValueError, TypeError):
            return None
    ordered = sorted(res.items(), key=lambda kv: -kv[1]["p_titulo"])
    lines = [f"{LEAGUE_ICON.get(league, '🏆')} <b>{esc(league.upper())}</b> · {remaining} jogos por jogar"]
    cand = [(t, v) for t, v in ordered if v["p_titulo"] >= 0.01][:4]
    if cand:
        lines.append("🏆 <b>Campeão:</b> " + " · ".join(
            f"{esc(short_name(t))} {v['p_titulo']:.0%}{arrow(v['p_titulo'], old(t, 'p_titulo'))}" for t, v in cand))
    fight = sorted(((t, v) for t, v in res.items() if 0.10 <= v["p_champions"] <= 0.90),
                   key=lambda kv: -kv[1]["p_champions"])[:4]
    if fight:
        lines.append(f"⭐ <b>Em luta pelo top {n_top}:</b> " + " · ".join(
            f"{esc(short_name(t))} {v['p_champions']:.0%}{arrow(v['p_champions'], old(t, 'p_champions'))}" for t, v in fight))
    rel = sorted(((t, v) for t, v in res.items() if v["p_descida"] >= 0.10),
                 key=lambda kv: -kv[1]["p_descida"])[:4]
    if rel:
        lines.append("🔻 <b>Risco de descer:</b> " + " · ".join(
            f"{esc(short_name(t))} {v['p_descida']:.0%}{arrow(v['p_descida'], old(t, 'p_descida'))}" for t, v in rel))
    return "\n".join(lines)


def season_sim_blocks(models, today, store=True):
    """models: {código: (nome, st, jogos_terminados)}. Devolve os blocos da mensagem e grava a simulação."""
    rows_old = read_csv(SIM_FILE)
    rows_new, body = [], []
    for code, (name, st, finished) in models.items():
        try:
            fixtures_raw = fd_matches(code, "SCHEDULED,TIMED")
            fixtures = [(m["homeTeam"]["name"], m["awayTeam"]["name"]) for m in fixtures_raw
                        if m.get("homeTeam", {}).get("name") and m.get("awayTeam", {}).get("name")]
            if not fixtures:
                continue
            n_top, n_bottom = SIM_LEAGUES[code]
            res = simulate_league(current_table(finished), fixtures, st, n_top, n_bottom, seed=today.toordinal())
            body.append(sim_block(name, res, prev_sim(rows_old, name, today), n_top, n_bottom, len(fixtures)))
            for t, v in res.items():
                rows_new.append({"data": today.isoformat(), "liga": name, "equipa": t,
                                 "p_titulo": f"{v['p_titulo']:.4f}", "p_champions": f"{v['p_champions']:.4f}",
                                 "p_descida": f"{v['p_descida']:.4f}", "pts_esperados": f"{v['pts_esperados']:.1f}"})
        except Exception as e:  # noqa: BLE001
            print("Simulação falhou em", code, e, file=sys.stderr)
    if not body:
        return []
    if store:
        try:
            keep = [r for r in rows_old if r["data"] != today.isoformat()]
            write_csv(SIM_FILE, SIM_FIELDS, keep + rows_new)
        except Exception as e:  # noqa: BLE001
            print("Não consegui gravar a simulação:", e, file=sys.stderr)
    head = (f"🏁 <b>CORRIDA DA ÉPOCA</b>\n📅 {today:%d/%m/%Y} · simulação de {SIM_RUNS} épocas\n━━━━━━━━━━━━━━━")
    note = ("<i>Cada liga é simulada {n} vezes com as forças do modelo (sem lesões, sem mercado de transferências). "
            "É uma estimativa, não uma previsão garantida. ⬆️⬇️ = mudança desde a semana passada, em pontos percentuais.</i>").format(n=SIM_RUNS)
    return [head] + body + [note, "— <b>Analista Desporto</b> 🤖"]


def build_model(code, name, today, matches):
    """Forças de ataque/defesa: jogos da época atual + épocas anteriores (CSV), com decaimento."""
    cur_hist = org_hist(matches)
    prior = []
    if code in CO_UK:
        try:
            org_names = {m["home"] for m in cur_hist} | {m["away"] for m in cur_hist}
            prior, sem_prior = map_prior(load_prior(CO_UK[code], today), org_names)
            print(f"{name}: {len(cur_hist)} jogos da época + {len(prior)} de épocas anteriores"
                  + (f" | sem histórico anterior: {', '.join(sem_prior)}" if sem_prior else ""),
                  file=sys.stderr)
        except Exception as e:  # noqa: BLE001
            print(f"{name}: épocas anteriores indisponíveis ({e})", file=sys.stderr)
            prior = []
    return build_strengths(prior + cur_hist, today)


SENT_FILE = f"{HIST_DIR}/ultimo_envio.txt"


def already_sent_today(now):
    try:
        with open(SENT_FILE, encoding="utf-8") as f:
            return f.read().strip() == now.astimezone(LISBON).date().isoformat()
    except OSError:
        return False


def mark_sent(now):
    try:
        os.makedirs(HIST_DIR, exist_ok=True)
        with open(SENT_FILE, "w", encoding="utf-8") as f:
            f.write(now.astimezone(LISBON).date().isoformat())
    except OSError as e:
        print("Não consegui gravar ultimo_envio:", e, file=sys.stderr)


def results_night(now):
    """Modo da noite: só resolve jogos terminados (sem gastar créditos de odds) e envia o resumo do dia."""
    idx = {}
    for code in LEAGUES:
        if code in MARKET_ONLY:
            continue
        try:
            add_index(idx, fd_matches(code))
        except Exception as e:  # noqa: BLE001
            print("Resultados: erro em", code, e, file=sys.stderr)
    picks_h, preds_h = read_csv(PICKS_FILE), read_csv(PREDS_FILE)
    before = {r["id"] for r in preds_h if r["estado"] == "pendente"}
    newly = settle(picks_h, preds_h, idx, now)
    write_csv(PICKS_FILE, PICK_FIELDS, picks_h)
    write_csv(PREDS_FILE, PRED_FIELDS, preds_h)
    done = sorted((r for r in preds_h if r["id"] in before and r["estado"] == "resolvida"),
                  key=lambda r: r["inicio_utc"])
    if not done and not newly:
        print("Sem jogos novos terminados; não envio nada.", file=sys.stderr)
        return
    d = now.astimezone(LISBON)
    blocks = [f"🌙 <b>RESULTADOS DE HOJE</b>\n📅 {DIAS[d.weekday()]}, {d:%d/%m/%Y}\n━━━━━━━━━━━━━━━"]
    names = ("casa", "empate", "fora")
    hits = favs = favs_ok = 0
    lines = []
    for r in done:
        p = _final_probs(r)
        res = _result_idx(r)
        if p:
            top = p.index(max(p))
            ok = top == res
            hits += ok
            if max(p) >= CLEAR_FAV:
                favs += 1
                favs_ok += ok
            lines.append(f"{'✅' if ok else '❌'} <b>{esc(r['casa'])} {r['golos_casa']}–{r['golos_fora']} {esc(r['fora'])}</b>\n"
                         f"   previsto: {names[top]} {max(p):.0%}")
        else:
            lines.append(f"▫️ {esc(r['casa'])} {r['golos_casa']}–{r['golos_fora']} {esc(r['fora'])}")
    if lines:
        blocks.append("\n".join(lines[:20]) + (f"\n… e mais {len(lines) - 20}." if len(lines) > 20 else ""))
        sm = [f"⚽ {len(done)} jogos terminados · resultado mais provável acertou {hits}/{len(done)}"]
        if favs:
            sm.append(f"⭐ Favoritos claros: {favs_ok}/{favs}")
        blocks.append("\n".join(sm))
    if newly:
        blocks.append(history_blocks(picks_h, preds_h, newly)[0])
    blocks.append("— <b>Analista Desporto</b> 🤖")
    telegram(blocks)


def main(now=None):
    now = now or dt.datetime.now(dt.timezone.utc)
    if os.getenv("MODO", "").strip().lower() == "simulacao":
        try:
            models = {}
            for code in SIM_LEAGUES:
                name = LEAGUES[code][0]
                matches = fd_matches(code)
                st = build_model(code, name, now.date(), matches)
                if st:
                    models[code] = (name, st, matches)
            sb = season_sim_blocks(models, now.date())
            if sb:
                telegram(sb)
        except Exception as e:  # noqa: BLE001
            print("Modo simulação falhou:", e, file=sys.stderr)
        return
    if os.getenv("MODO", "").strip().lower() == "resultados":
        try:
            results_night(now)
        except Exception as e:  # noqa: BLE001
            print("Modo resultados falhou:", e, file=sys.stderr)
        return
    # Execuções automáticas repetidas (rede de segurança contra atrasos do GitHub): só envia 1x por dia.
    if os.getenv("GITHUB_EVENT_NAME") == "schedule" and already_sent_today(now):
        print("Já enviado hoje; nada a fazer.", file=sys.stderr)
        return
    today = now.date()
    near = now + dt.timedelta(hours=HOURS_AHEAD)
    far = now + dt.timedelta(hours=FALLBACK_HOURS)
    results, idx, sim_models = {}, {}, {}
    want_sim = now.astimezone(LISBON).weekday() == 0  # corrida da época: às segundas-feiras
    for code, (name, sport) in LEAGUES.items():
        try:
            if code in MARKET_ONLY:
                games = []
                for ev in odds_events(sport, "h2h" if code in H2H_ONLY else "h2h,totals"):
                    t = parse_iso(ev["commence_time"])
                    if now <= t <= far:
                        g = analyse_market_only(ev)
                        if g:
                            games.append(g)
                games.sort(key=lambda g: g["time"])
                results[name] = games
                continue
            matches = fd_matches(code)
            add_index(idx, matches)
            st = build_model(code, name, today, matches)
            if not st:
                print("Poucos dados:", name, file=sys.stderr)
                continue
            if want_sim and code in SIM_LEAGUES:
                sim_models[code] = (name, st, matches)
            games = []
            for ev in odds_events(sport, "h2h" if code in H2H_ONLY else "h2h,totals"):
                t = parse_iso(ev["commence_time"])
                if not (now <= t <= far):
                    continue
                g = analyse_event(ev, st)
                if g:
                    games.append(g)
                else:
                    print(f"{name}: jogo sem emparelhar equipas: {ev['home_team']} vs {ev['away_team']}",
                          file=sys.stderr)
            games.sort(key=lambda g: g["time"])
            results[name] = games
        except Exception as e:  # noqa: BLE001
            print("Erro em", name, e, file=sys.stderr)

    def is_near(g):
        return parse_iso(g["time"]) <= near

    near_res = {n: [g for g in gs if is_near(g)] for n, gs in results.items()}
    fallback = not any(near_res.values())
    if fallback:
        shown = {n: gs[:FALLBACK_PER_LEAGUE] for n, gs in results.items()}
    else:
        shown = near_res

    try:
        attach_injuries(shown, {v[0]: k for k, v in LEAGUES.items()}, today)
    except Exception as e:  # noqa: BLE001
        print("Lesões falharam:", e, file=sys.stderr)
    extra = []
    try:  # o histórico nunca pode impedir o envio da mensagem
        picks_h = read_csv(PICKS_FILE)
        preds_h = read_csv(PREDS_FILE)
        newly = settle(picks_h, preds_h, idx, now)
        log_new(picks_h, preds_h, results, shown, now)
        write_csv(PICKS_FILE, PICK_FIELDS, picks_h)
        write_csv(PREDS_FILE, PRED_FIELDS, preds_h)
        extra = history_blocks(picks_h, preds_h, newly)
        if now.astimezone(LISBON).weekday() == 0:
            wb = weekly_block(picks_h, preds_h, now)
            if wb:
                extra.insert(0, wb)
    except Exception as e:  # noqa: BLE001
        print("Histórico falhou:", e, file=sys.stderr)

    blocks = build_blocks(shown, fallback, extra)
    summary = gemini_summary(plain_text(blocks))
    if summary:
        blocks.insert(2, summary)  # logo a seguir ao resumo do topo
    telegram(blocks)
    mark_sent(now)
    if sim_models:  # segunda mensagem, só às segundas-feiras
        try:
            sb = season_sim_blocks(sim_models, now.date())
            if sb:
                telegram(sb)
        except Exception as e:  # noqa: BLE001
            print("Corrida da época falhou:", e, file=sys.stderr)


if __name__ == "__main__":
    main()
