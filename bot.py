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
import json
import math
import time
import html
import difflib
import hashlib
import subprocess
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
ADAPT_FILE = "historico/peso_modelo.json"
ADAPT_MIN_GAMES, ADAPT_STEP, ADAPT_LO, ADAPT_HI, BASE_W = 100, 0.05, 0.10, 0.35, 0.20
_BASE_CACHE = [None]


def base_weight():
    """Peso do modelo com 3+ casas: 20% por defeito; o ajuste semanal pode mexer-lhe (entre 10% e 35%)."""
    if _BASE_CACHE[0] is None:
        w = BASE_W
        try:
            with open(ADAPT_FILE, encoding="utf-8") as f:
                w = min(ADAPT_HI, max(ADAPT_LO, float(json.load(f)["base"])))
        except Exception:  # noqa: BLE001
            pass
        _BASE_CACHE[0] = w
    return _BASE_CACHE[0]


def model_weight(n_books):
    b = base_weight()
    if n_books >= 3: return b
    if n_books == 2: return b + 0.15
    if n_books == 1: return b + 0.30
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

SITE_URL = "https://mantovunas.github.io/analista-desporto/"
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


# ---------- ligas só com resultados (sem odds nem previsões): aparecem no site ----------
EXTRA_LEAGUES = {"BSA": "Brasileirão"}
EXTRA_FILE = f"{HIST_DIR}/outras_ligas.csv"


def extra_leagues(teams_seen):
    """Resultados recentes e próximos jogos de ligas extra (football-data.org grátis). Só informativo."""
    rows = []
    for code, name in EXTRA_LEAGUES.items():
        try:
            fin = fd_matches(code, "FINISHED")
            sch = fd_matches(code, "SCHEDULED,TIMED")
        except Exception as e:  # noqa: BLE001
            print("Liga extra falhou:", name, e, file=sys.stderr)
            continue
        teams = {m[side]["name"] for m in fin + sch for side in ("homeTeam", "awayTeam") if m.get(side, {}).get("name")}
        if teams:
            teams_seen[name] = sorted(teams)
        for m in sorted(fin, key=lambda m: m["utcDate"], reverse=True)[:40]:
            sc = (m.get("score", {}).get("fullTime") or {})
            if m["homeTeam"].get("name") and m["awayTeam"].get("name") and sc.get("home") is not None:
                rows.append({"liga": name, "data": m["utcDate"], "casa": m["homeTeam"]["name"], "fora": m["awayTeam"]["name"],
                             "golos_casa": sc["home"], "golos_fora": sc["away"], "estado": "terminado"})
        for m in sorted(sch, key=lambda m: m["utcDate"])[:20]:
            if m["homeTeam"].get("name") and m["awayTeam"].get("name"):
                rows.append({"liga": name, "data": m["utcDate"], "casa": m["homeTeam"]["name"], "fora": m["awayTeam"]["name"],
                             "golos_casa": "", "golos_fora": "", "estado": "agendado"})
    if rows:
        write_csv(EXTRA_FILE, ["liga", "data", "casa", "fora", "golos_casa", "golos_fora", "estado"], rows)


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


INJ_WARN = 3           # 3+ baixas numa equipa: a confiança desce um nível
SPREAD_WARN = 0.07     # casas discordam >= 7 pontos num resultado: confiança desce
DUEL_GAP = 0.08        # 'grande desacordo' modelo vs mercado (diferença máx. numa probabilidade)
AF_LEAGUES = {"PL": 39, "ELC": 40, "PD": 140, "SA": 135, "BL1": 78, "FL1": 61, "PPL": 94, "DED": 88, "CL": 2}


_AF_BLOCK = [False]


def af_injuries(league_id, season, day):
    """Lesionados/suspensos de uma liga num dia (API-Football). Devolve [(equipa, jogador, motivo)]."""
    r = requests.get("https://v3.football.api-sports.io/injuries",
                     headers={"x-apisports-key": AF_KEY},
                     params={"league": league_id, "season": season, "date": day}, timeout=30)
    data = r.json()
    if r.status_code != 200 or data.get("errors"):
        print("API-Football:", r.status_code, str(data.get("errors"))[:200], file=sys.stderr)
        if "Free plans" in str(data.get("errors")):
            _AF_BLOCK[0] = True  # plano grátis sem acesso à época atual: não insistir
        return []
    out = []
    for it in data.get("response", []):
        out.append((it.get("team", {}).get("name", ""), it.get("player", {}).get("name", ""),
                    it.get("player", {}).get("reason") or it.get("player", {}).get("type") or ""))
    return out


# ---------- lesões da Premier League: API pública do Fantasy Premier League (grátis, sem chave) ----------
FPL_URL = "https://fantasy.premierleague.com/api/bootstrap-static/"
FPL_MIN_MINUTES = 450      # só conta jogadores com peso (>= 450 minutos na época)
FPL_ALIAS = {"Man City": "Manchester City", "Man Utd": "Manchester United", "Spurs": "Tottenham Hotspur",
             "Wolves": "Wolverhampton Wanderers", "Nott'm Forest": "Nottingham Forest", "Newcastle": "Newcastle United",
             "Brighton": "Brighton and Hove Albion", "West Ham": "West Ham United", "Leeds": "Leeds United",
             "Leicester": "Leicester City", "Ipswich": "Ipswich Town", "Norwich": "Norwich City",
             "Sheffield Utd": "Sheffield United", "Luton": "Luton Town"}
_FPL_CACHE = {}


def fpl_injuries():
    """{equipa: {"out": [(jogador, motivo)], "doubt": [(jogador, motivo)]}} só com jogadores importantes."""
    if "d" in _FPL_CACHE:
        return _FPL_CACHE["d"]
    r = requests.get(FPL_URL, headers={"User-Agent": "Mozilla/5.0"}, timeout=30)
    r.raise_for_status()
    data = r.json()
    teams = {t["id"]: FPL_ALIAS.get(t["name"], t["name"]) for t in data["teams"]}
    out = {}
    for p in data["elements"]:
        if (p.get("minutes") or 0) < FPL_MIN_MINUTES:
            continue
        status, chance = p.get("status"), p.get("chance_of_playing_next_round")
        news = (p.get("news") or "").split(" - ")[0].strip()
        t = out.setdefault(teams.get(p["team"], ""), {"out": [], "doubt": []})
        if status in ("i", "s", "n") and (chance is None or chance <= 25):
            t["out"].append((p["web_name"], news))
        elif status == "d" or (chance is not None and chance < 100 and status != "a"):
            t["doubt"].append((p["web_name"], news))
    _FPL_CACHE["d"] = out
    return out


def attach_injuries(shown, league_codes, today):
    """Junta a cada jogo as baixas: Premier League via API do Fantasy (grátis); outras ligas via API-Football se o plano o permitir."""
    season = season_start(today)
    cache = {}
    for name, games in shown.items():
        code = league_codes.get(name)
        for g in games:
            try:
                if code == "PL":
                    fpl = fpl_injuries()
                    th = match_team(g["home"], list(fpl), 0.72)
                    ta = match_team(g["away"], list(fpl), 0.72)
                    if not th and not ta:
                        continue
                    g["inj"] = {"home": fpl.get(th, {}).get("out", []), "away": fpl.get(ta, {}).get("out", []),
                                "doubt_home": fpl.get(th, {}).get("doubt", []), "doubt_away": fpl.get(ta, {}).get("doubt", [])}
                elif AF_KEY and code in AF_LEAGUES and not _AF_BLOCK[0]:
                    day = parse_iso(g["time"]).date().isoformat()
                    key = (code, day)
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
                else:
                    continue
                if max(len(g["inj"]["home"]), len(g["inj"]["away"])) >= INJ_WARN and not g.get("market_only"):
                    g["conf"] = {"alta": "média", "média": "baixa"}.get(g["conf"], g["conf"])
                    g["inj_warn"] = True
            except Exception as e:  # noqa: BLE001
                print("Lesões falharam:", e, file=sys.stderr)


def inj_line(g):
    inj = g.get("inj")
    if not inj:
        return ""
    doubt = inj.get("doubt_home", []) + inj.get("doubt_away", [])
    if not (inj["home"] or inj["away"] or doubt):
        return ""
    def fmt(lst):
        shown = ", ".join(f"{esc(p)} ({esc(m)})" if m else esc(p) for p, m in lst[:4])
        return shown + (f" +{len(lst) - 4}" if len(lst) > 4 else "")
    parts = []
    if inj["home"]: parts.append(f"{esc(g['home'])}: {fmt(inj['home'])}")
    if inj["away"]: parts.append(f"{esc(g['away'])}: {fmt(inj['away'])}")
    lines = []
    if parts:
        lines.append("🚑 Baixas — " + " · ".join(parts))
    dparts = []
    if inj.get("doubt_home"): dparts.append(f"{esc(g['home'])}: {fmt(inj['doubt_home'])}")
    if inj.get("doubt_away"): dparts.append(f"{esc(g['away'])}: {fmt(inj['doubt_away'])}")
    if dparts:
        lines.append("❓ Dúvidas — " + " · ".join(dparts))
    warn = "⚠️ Muitas baixas: confiança reduzida. " if g.get("inj_warn") else ""
    return "\n".join(lines) + "\n<i>" + warn + "(o modelo não conta lesões)</i>"


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


SPARK = "▁▂▃▄▅▆▇█"


def bankroll_line(picks, now, weeks=8):
    """Banca virtual: 1 unidade em cada sugestão resolvida, acumulado desde o início + evolução semanal."""
    rows = [r for r in picks if r.get("estado") in ("ganha", "perdida") and r.get("lucro") not in ("", None)]
    if len(rows) < 5:
        return None
    tot = sum(float(r["lucro"]) for r in rows)
    wk = {}
    for r in rows:
        d = parse_iso(r["inicio_utc"]).date()
        key = d - dt.timedelta(days=d.weekday())
        wk[key] = wk.get(key, 0.0) + float(r["lucro"])
    cum, run = [], 0.0
    for key in sorted(wk):
        run += wk[key]
        cum.append(run)
    cum = cum[-weeks:]
    lo, hi = min(cum), max(cum)
    spark = "".join(SPARK[int((c - lo) / (hi - lo) * 7)] if hi > lo else SPARK[3] for c in cum)
    wins = sum(1 for r in rows if r["estado"] == "ganha")
    return (f"💰 <b>Banca virtual</b> (1 unidade por sugestão): {tot:+.2f} unidades em {len(rows)} sugestões "
            f"(ROI {tot / len(rows):+.0%}, {wins} ganhas)\n📈 {spark}")


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


def adapt_weight(preds, now):
    """Ajuste semanal (2.as feiras): procura o peso do modelo que teria dado o menor erro nos últimos jogos
    e aproxima-se dele no máximo 5 pontos por semana, sempre entre 10% e 35%. Só com 100+ jogos."""
    rows = []
    for r in preds:
        if r.get("estado") != "resolvida":
            continue
        a, b = _trio(r, "pH", "pD", "pA"), _trio(r, "mH", "mD", "mA")
        if a and b:
            rows.append((a, b, _result_idx(r)))
    rows = rows[-300:]
    if len(rows) < ADAPT_MIN_GAMES:
        return f"⚖️ Peso do modelo: {base_weight():.0%} (o ajuste automático começa com {ADAPT_MIN_GAMES} jogos avaliados; há {len(rows)})."

    def err(w):
        tot = 0.0
        for a, b, k in rows:
            for i in range(3):
                x = w * a[i] + (1 - w) * b[i]
                tot += (x - (1.0 if i == k else 0.0)) ** 2
        return tot / len(rows)
    grid = [i / 100 for i in range(round(ADAPT_LO * 100), round(ADAPT_HI * 100) + 1, 5)]
    best = min(grid, key=err)
    cur = base_weight()
    new = cur + max(-ADAPT_STEP, min(ADAPT_STEP, best - cur))
    new = round(min(ADAPT_HI, max(ADAPT_LO, new)) * 100) / 100
    try:
        os.makedirs(HIST_DIR, exist_ok=True)
        with open(ADAPT_FILE, "w", encoding="utf-8") as f:
            json.dump({"base": new, "melhor": best, "jogos": len(rows), "data": now.date().isoformat()}, f)
        _BASE_CACHE[0] = None
    except Exception as e:  # noqa: BLE001
        print("Peso adaptativo não gravado:", e, file=sys.stderr)
        return ""
    if new == cur:
        return f"⚖️ Peso do modelo mantém-se em {cur:.0%} (melhor peso nos últimos {len(rows)} jogos: {best:.0%})."
    return f"⚖️ Peso do modelo ajustado: {cur:.0%} → {new:.0%} (melhor peso nos últimos {len(rows)} jogos: {best:.0%})."


def yesterday_line(preds, now):
    """'Ontem o bot acertou 5/8' (jogos de ontem, hora de Lisboa, já resolvidos)."""
    y = (now.astimezone(LISBON) - dt.timedelta(days=1)).date()
    rows = [r for r in preds if r.get("estado") == "resolvida" and _final_probs(r)
            and parse_iso(r["inicio_utc"]).astimezone(LISBON).date() == y]
    if len(rows) < 2:
        return ""
    hit = sum(1 for r in rows if _final_probs(r).index(max(_final_probs(r))) == _result_idx(r))
    return f"📈 Ontem o bot acertou {hit}/{len(rows)} ({hit / len(rows):.0%})"


def streak_line(preds):
    """Sequência atual de acertos do bot (resultado mais provável) e recorde. Só mostra a partir de 3 seguidos."""
    rows = sorted((r for r in preds if r.get("estado") == "resolvida" and _final_probs(r)), key=lambda r: r["inicio_utc"])
    cur = best = 0
    for r in rows:
        if _final_probs(r).index(max(_final_probs(r))) == _result_idx(r):
            cur += 1
            best = max(best, cur)
        else:
            cur = 0
    if cur < 3:
        return ""
    return f"🔥 Sequência: {cur} acertos seguidos" + (" (recorde!)" if cur == best else f" (recorde {best})")


def week_highlights(rp, lo):
    """Destaques da semana: melhor acerto, maior surpresa, jogo mais louco e placar Bot vs Grupo."""
    out = [""]
    sc = [(r, _final_probs(r)) for r in rp]
    sc = [(r, p) for r, p in sc if p]
    names = ("casa", "empate", "fora")

    def jg(r):
        return f"{esc(short_name(r['casa']))} {r['golos_casa']}–{r['golos_fora']} {esc(short_name(r['fora']))}"
    if sc:
        ok = [(max(p), r, p) for r, p in sc if p.index(max(p)) == _result_idx(r)]
        if ok:
            m, r, _ = max(ok, key=lambda x: x[0])
            out.append(f"🏅 <b>Melhor acerto:</b> {jg(r)} (o bot dava {names[_result_idx(r)]} {m:.0%})")
        r, p = min(sc, key=lambda x: x[1][_result_idx(x[0])])
        if p[_result_idx(r)] < 0.25:
            out.append(f"😱 <b>Maior surpresa:</b> {jg(r)} (o bot dava só {p[_result_idx(r)]:.0%} a este resultado)")
    wild = max(rp, key=lambda r: int(r["golos_casa"]) + int(r["golos_fora"]))
    tot = int(wild["golos_casa"]) + int(wild["golos_fora"])
    if tot >= 5:
        out.append(f"🎢 <b>Jogo mais louco:</b> {jg(wild)} ({tot} golos)")
    g = [r for r in read_csv(DUEL_GROUP_FILE) if r.get("grupo_ok") != "" and r.get("data", "") >= lo.date().isoformat()]
    if g:
        b = sum(int(r["bot_ok"]) for r in g)
        gp = sum(int(r["grupo_ok"]) for r in g)
        out.append(f"🆚 <b>Bot vs Grupo (semana):</b> Bot {b} · Grupo {gp} em {len(g)} jogo{'s' if len(g) != 1 else ''}")
    return out if len(out) > 1 else []


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
    bl = bankroll_line(picks, now)
    if bl:
        lines.append(bl)
    try:
        al = adapt_weight(preds, now)
        if al:
            lines.append(al)
    except Exception as e:  # noqa: BLE001
        print("Ajuste de peso falhou:", e, file=sys.stderr)
    try:
        lines.extend(week_highlights(rp, lo))
    except Exception as e:  # noqa: BLE001
        print("Destaques da semana falharam:", e, file=sys.stderr)
    lines.append("<i>Uma semana é pouco: só dá para tirar conclusões com várias semanas.</i>")
    return "\n".join(lines)


CAL_BINS = [(0, .2), (.2, .4), (.4, .6), (.6, .8), (.8, 1.01)]


def calibration_block(preds, min_games=60):
    """Quando o bot diz X%, acontece X% das vezes? (todas as previsões 1X2 resolvidas)"""
    pts = []
    for r in preds:
        if r.get("estado") != "resolvida":
            continue
        p = _final_probs(r)
        if p is None:
            continue
        k = _result_idx(r)
        pts += [(p[i], 1 if i == k else 0) for i in range(3)]
    n_games = len(pts) // 3
    if n_games < min_games:
        return None
    lines = ["📏 <b>O BOT ESTÁ AFINADO?</b>", "", f"Quando o bot diz X%, quantas vezes acontece? ({n_games} jogos)"]
    for lo, hi in CAL_BINS:
        sel = [(p, y) for p, y in pts if lo <= p < hi]
        if len(sel) < 10:
            continue
        said = sum(p for p, _ in sel) / len(sel)
        real = sum(y for _, y in sel) / len(sel)
        diff = real - said
        flag = "✅" if abs(diff) < 0.05 else ("⬆️ subestima" if diff > 0 else "⬇️ exagera")
        lines.append(f"{lo:.0%}–{min(hi, 1):.0%}: disse {said:.0%} · aconteceu {real:.0%} {flag}")
    return "\n".join(lines) if len(lines) > 3 else None


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

    blocks = [f"⚽ <b>RADAR DO GOLO</b>\n📅 {DIAS[now.weekday()]}, {now:%d/%m/%Y}\n━━━━━━━━━━━━━━━"]
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
    risky = []
    for g in club:
        why = []
        if g.get("market") and max(abs(a - b) for a, b in zip(g["model"], g["market"])) >= DUEL_GAP:
            why.append("modelo e mercado discordam")
        if g.get("spread_warn"):
            why.append("casas divergem")
        if g.get("inj_warn"):
            why.append("muitas baixas")
        if why:
            risky.append(f"• {esc(g['home'])} vs {esc(g['away'])} — {', '.join(why)}")
    if risky:
        lines.append("")
        lines.append("⚠️ <b>Jogos de risco (o bot está menos seguro):</b>")
        lines.extend(risky[:4])
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
    foot.append(f'📊 <a href="{SITE_URL}">Abrir o site</a>')
    foot.append("— <b>Radar do Golo</b> 🎯")
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


def gemini_news(shown):
    """EXPERIMENTAL: notícias/lesões dos jogos fora da Premier League, com pesquisa Google. Nunca altera probabilidades."""
    if not GEMINI_KEY or os.getenv("NEWS_OFF"):
        return ""
    cands = []
    for league, games in shown.items():
        if league == "Premier League":
            continue
        for g in games:
            cands.append((fame_score(league, g), g))
    cands.sort(key=lambda x: -x[0])
    top = cands[:3]
    if not top:
        return ""
    jogos = "\n".join(f"- {g['home']} vs {g['away']}" for _, g in top)
    prompt = ("Pesquisa notícias das últimas 48 horas sobre estes jogos de futebol de hoje: lesões, suspensões, "
              "jogadores importantes em dúvida ou ausentes. Responde em português de Portugal, máx. 1 linha por jogo, "
              "só com informação fiável que encontrares. Se não houver notícias fiáveis, escreve 'sem notícias fiáveis' "
              "nessa linha. Não inventes.\n" + jogos)
    r = None
    try:
        r = requests.post(
            f"https://generativelanguage.googleapis.com/v1beta/models/{GEMINI_MODEL}:generateContent",
            params={"key": GEMINI_KEY},
            json={"contents": [{"parts": [{"text": prompt}]}], "tools": [{"google_search": {}}]}, timeout=90)
        r.raise_for_status()
        txt = "".join(p.get("text", "") for p in r.json()["candidates"][0]["content"]["parts"]).strip()
        if not txt:
            return ""
        return "📰 <b>NOTÍCIAS (experimental, IA)</b>\n" + esc(txt[:900]) + "\n<i>Não influencia as probabilidades; confirma sempre.</i>"
    except Exception as e:  # noqa: BLE001
        print("Notícias Gemini falharam (ignorado):", e, file=sys.stderr)
        if r is not None:
            print("Resposta:", r.text[:300], file=sys.stderr)
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


# ---------- cartões em imagem (estilo "Revista" do site) ----------
CARD_HEAD = """<!doctype html><html><head><meta charset="utf-8">
<link href="https://fonts.googleapis.com/css2?family=Playfair+Display:ital,wght@0,800;1,800&family=Archivo:wght@500;700;900&display=swap" rel="stylesheet">
<style>*{box-sizing:border-box}body{margin:0;width:1080px;height:1080px;background:#f1ede4;color:#141210;font-family:Archivo,Arial,sans-serif;
position:relative;overflow:hidden}.serif{font-family:'Playfair Display',Georgia,serif;font-weight:800;font-variant-numeric:lining-nums;font-feature-settings:'liga' 0,'lnum' 1}
.top{display:flex;justify-content:space-between;padding:34px 56px 0;font-size:22px;font-weight:900;letter-spacing:.2em;text-transform:uppercase}
.mast{margin:8px 0 0;border-top:6px solid #141210;border-bottom:6px solid #141210;text-align:center;font-size:118px;line-height:1.1;padding:0 0 8px;letter-spacing:-.04em}
.foot{position:absolute;left:0;right:0;bottom:0;height:70px;background:#141210;color:#f1ede4;display:flex;align-items:center;justify-content:center;gap:40px;font-weight:900;font-size:22px;letter-spacing:.16em;text-transform:uppercase}
.foot b{color:#e4372c}</style></head><body>"""


def _card_date(now):
    d = now.astimezone(LISBON)
    return f"{DIAS[d.weekday()]}, {d:%d/%m/%Y}"


def cover_html(g, now, extra=""):
    f = g["final"]
    i = f.index(max(f))
    win = f"{short_name(g['home'])} ganha" if i == 0 else f"{short_name(g['away'])} ganha" if i == 2 else "Empate"
    t = parse_iso(g["time"]).astimezone(LISBON)
    likely = ""
    try:
        (ci, cj), _ = top_scores(g["p"]["lh"], g["p"]["la"], 1)[0]
        likely = (f'<div style="text-align:center;margin-top:34px"><div style="font-size:20px;font-weight:900;letter-spacing:.2em;color:#6a6558">RESULTADO MAIS PROVÁVEL</div>'
                  f'<div class="serif" style="font-size:96px;line-height:1.1">{ci}–{cj}</div></div>')
    except Exception:  # noqa: BLE001
        pass
    return (CARD_HEAD + f"""<div class="top"><span>{esc(_card_date(now))}</span><span>Edição de hoje</span></div>
<div class="mast serif">Radar do Golo</div>
<div style="text-align:center;margin-top:30px"><span style="background:#e4372c;color:#fff;font-weight:900;font-size:22px;letter-spacing:.22em;padding:10px 20px;text-transform:uppercase">O jogo do dia · {t:%H:%M}</span></div>
<div class="serif" style="display:flex;justify-content:center;align-items:flex-start;line-height:1;margin-top:14px">
<span style="font-size:300px;line-height:1;letter-spacing:-.05em;padding-bottom:10px">{round(max(f) * 100)}</span><span style="font-size:110px;color:#e4372c;margin-top:.35em;margin-left:8px">%</span></div>
<div style="text-align:center;font-size:24px;font-weight:900;letter-spacing:.2em;text-transform:uppercase;margin-top:6px">{esc(win)}</div>
<div class="serif" style="text-align:center;font-size:66px;line-height:1.15;margin-top:22px">{esc(short_name(g['home']))} <i style="color:#e4372c">contra</i> {esc(short_name(g['away']))}</div>
<div style="width:760px;height:24px;margin:26px auto 0;display:flex;background:#d8d3c7"><div style="width:{f[0] * 100:.1f}%;background:#141210"></div><div style="width:{f[1] * 100:.1f}%;background:#e4372c"></div><div style="width:{f[2] * 100:.1f}%;background:#8d877a"></div></div>
<div style="width:760px;margin:12px auto 0;display:flex;justify-content:space-between;font-size:22px;font-weight:900;letter-spacing:.1em;text-transform:uppercase"><span>Casa {round(f[0] * 100)}</span><span style="color:#e4372c">Empate {round(f[1] * 100)}</span><span style="color:#6a6558">Fora {round(f[2] * 100)}</span></div>
{likely}
<div class="foot"><span>Vota na sondagem do dia</span>{extra}</div></body></html>""")


def night_html(done, now, extra=""):
    names = ("casa", "empate", "fora")
    rows, hit, n = [], 0, 0
    for r in done[:8]:
        fp = _final_probs(r)
        ok = None
        if fp:
            ok = fp.index(max(fp)) == _result_idx(r)
            hit += int(ok)
            n += 1
        mark = "" if ok is None else ('<b style="color:#1f7a45">ACERTOU</b>' if ok else '<b style="color:#e4372c">FALHOU</b>')
        rows.append(f'<div style="display:flex;justify-content:space-between;align-items:baseline;border-bottom:2px solid rgba(20,18,16,.2);padding:14px 0">'
                    f'<span class="serif" style="font-size:38px;max-width:700px">{esc(short_name(r["casa"]))} {esc(r["golos_casa"])}–{esc(r["golos_fora"])} {esc(short_name(r["fora"]))}</span>'
                    f'<span style="font-size:20px;letter-spacing:.14em">{mark}</span></div>')
    head = f'<span class="serif" style="font-size:210px;line-height:1">{hit}</span><span class="serif" style="font-size:90px;color:#e4372c;margin-top:.3em">/{n}</span>' if n else ""
    return (CARD_HEAD + f"""<div class="top"><span>{esc(_card_date(now))}</span><span>Resultados de hoje</span></div>
<div class="mast serif">Radar do Golo</div>
<div style="text-align:center;margin-top:24px"><span style="background:#e4372c;color:#fff;font-weight:900;font-size:22px;letter-spacing:.22em;padding:10px 20px;text-transform:uppercase">O bot acertou</span></div>
<div style="display:flex;justify-content:center;align-items:flex-start;margin-top:8px">{head}</div>
<div style="padding:10px 56px 0">{''.join(rows)}</div>
<div class="foot"><span>Radar do Golo</span>{extra}</div></body></html>""")


def render_card(html):
    """HTML -> PNG (1080x1080) com o Chrome do GitHub Actions. Devolve bytes ou None se não for possível."""
    try:
        from playwright.sync_api import sync_playwright
    except Exception as e:  # noqa: BLE001
        print("Cartão: playwright não instalado, envio só texto:", e, file=sys.stderr)
        return None
    try:
        with sync_playwright() as p:
            try:
                br = p.chromium.launch(channel="chrome", args=["--no-sandbox"])
            except Exception:  # noqa: BLE001
                br = p.chromium.launch(args=["--no-sandbox"])
            pg = br.new_page(viewport={"width": 1080, "height": 1080})
            pg.set_content(html)
            try:
                pg.wait_for_load_state("networkidle", timeout=15000)
                pg.evaluate("document.fonts.ready")
            except Exception:  # noqa: BLE001
                pass
            png = pg.screenshot(type="png")
            br.close()
            return png
    except Exception as e:  # noqa: BLE001
        print("Cartão: falhou a gerar a imagem, envio só texto:", e, file=sys.stderr)
        return None


def send_card(html, caption=""):
    png = render_card(html)
    if not png:
        return False
    try:
        r = requests.post(f"https://api.telegram.org/bot{TG_TOKEN}/sendPhoto",
                          data={"chat_id": TG_CHAT, "caption": caption[:1000], "parse_mode": "HTML"},
                          files={"photo": ("radar.png", png, "image/png")}, timeout=60)
        r.raise_for_status()
        return True
    except Exception as e:  # noqa: BLE001
        print("Cartão: envio falhou:", e, file=sys.stderr)
        return False


def game_card_html(league, g, now):
    f = g["final"]
    i = f.index(max(f))
    t = parse_iso(g["time"]).astimezone(LISBON)
    cells = []
    for k, (lab, name) in enumerate((("Casa", short_name(g["home"])), ("Empate", ""), ("Fora", short_name(g["away"])))):
        on = k == i
        col = "#141210" if k == 0 else "#e4372c" if k == 1 else "#6a6558"
        cells.append(f'<div style="flex:1;text-align:center;{"" if on else "opacity:.55"}"><div class="serif" style="font-size:{170 if on else 120}px;line-height:1;color:{col}">{round(f[k] * 100)}</div>'
                     f'<div style="font-size:20px;font-weight:900;letter-spacing:.14em;text-transform:uppercase;margin-top:4px">{lab}</div></div>')
    chips = []
    if not g.get("market_only") and g.get("p"):
        try:
            (ci, cj), _ = top_scores(g["p"]["lh"], g["p"]["la"], 1)[0]
            chips.append(f"Resultado provável {ci}–{cj}")
        except Exception:  # noqa: BLE001
            pass
        if g.get("final_o") is not None:
            chips.append(f"+2,5 golos {g['final_o']:.0%}")
        chips.append("Confiança " + re.sub(r"^[^\w]+", "", re.sub(r"<[^>]+>", "", conf_txt(g["conf"]))).strip())
    else:
        chips.append("Só mercado")
    chips.append("Betclic ✓" if g.get("has_pref") else "sem Betclic")
    warn = ""
    if g.get("spread_warn") or g.get("inj_warn"):
        warn = '<div style="text-align:center;margin-top:18px;font-size:22px;font-weight:900;letter-spacing:.14em;color:#e4372c;text-transform:uppercase">Jogo de risco: o bot está menos seguro</div>'
    chip_html = "".join(f'<span style="border:3px solid #141210;padding:8px 14px;font-size:20px;font-weight:900;letter-spacing:.08em;text-transform:uppercase">{esc(c)}</span>' for c in chips if c)
    return (CARD_HEAD + f"""<div class="top"><span>{esc(_card_date(now))}</span><span>{esc(league)}</span></div>
<div class="mast serif" style="font-size:84px">Radar do Golo</div>
<div style="text-align:center;margin-top:26px"><span style="background:#e4372c;color:#fff;font-weight:900;font-size:22px;letter-spacing:.22em;padding:10px 20px;text-transform:uppercase">{t:%H:%M}</span></div>
<div class="serif" style="text-align:center;font-size:72px;line-height:1.12;margin:26px 40px 0">{esc(short_name(g['home']))}<br><i style="color:#e4372c;font-size:54px">contra</i><br>{esc(short_name(g['away']))}</div>
<div style="display:flex;margin:34px 56px 0;align-items:flex-end">{''.join(cells)}</div>
<div style="width:900px;height:22px;margin:22px auto 0;display:flex;background:#d8d3c7"><div style="width:{f[0] * 100:.1f}%;background:#141210"></div><div style="width:{f[1] * 100:.1f}%;background:#e4372c"></div><div style="width:{f[2] * 100:.1f}%;background:#8d877a"></div></div>
<div style="display:flex;gap:12px;justify-content:center;flex-wrap:wrap;margin:26px 40px 0">{chip_html}</div>{warn}
<div class="foot"><span>Radar do Golo</span><b>●</b><span>Estimativa, não garantia</span></div></body></html>""")


def render_cards(htmls):
    """Vários HTML -> vários PNG com um único browser (mais rápido). Lista vazia se não der."""
    try:
        from playwright.sync_api import sync_playwright
    except Exception as e:  # noqa: BLE001
        print("Cartões: playwright não instalado:", e, file=sys.stderr)
        return []
    out = []
    try:
        with sync_playwright() as p:
            try:
                br = p.chromium.launch(channel="chrome", args=["--no-sandbox"])
            except Exception:  # noqa: BLE001
                br = p.chromium.launch(args=["--no-sandbox"])
            pg = br.new_page(viewport={"width": 1080, "height": 1080})
            for h in htmls:
                pg.set_content(h)
                try:
                    pg.wait_for_load_state("networkidle", timeout=15000)
                    pg.evaluate("document.fonts.ready")
                except Exception:  # noqa: BLE001
                    pass
                out.append(pg.screenshot(type="png"))
            br.close()
    except Exception as e:  # noqa: BLE001
        print("Cartões: falhou a gerar imagens:", e, file=sys.stderr)
    return out


def send_album(pngs, caption=""):
    for a in range(0, len(pngs), 10):
        chunk = pngs[a:a + 10]
        if len(chunk) == 1:
            requests.post(f"https://api.telegram.org/bot{TG_TOKEN}/sendPhoto", data={"chat_id": TG_CHAT, "caption": caption[:900] if a == 0 else "", "parse_mode": "HTML"},
                          files={"photo": ("j0.png", chunk[0], "image/png")}, timeout=60).raise_for_status()
            continue
        media = [{"type": "photo", "media": f"attach://p{k}"} for k in range(len(chunk))]
        if a == 0 and caption:
            media[0]["caption"] = caption[:900]
            media[0]["parse_mode"] = "HTML"
        requests.post(f"https://api.telegram.org/bot{TG_TOKEN}/sendMediaGroup",
                      data={"chat_id": TG_CHAT, "media": json.dumps(media)},
                      files={f"p{k}": (f"j{k}.png", b, "image/png") for k, b in enumerate(chunk)}, timeout=120).raise_for_status()


ROWS_PER_CARD = 7


def league_card_html(league, games, now, part=1, parts=1):
    rows = []
    for g in games:
        f = g["final"]
        i = f.index(max(f))
        t = parse_iso(g["time"]).astimezone(LISBON)
        cols = ("#141210", "#e4372c", "#6a6558")
        nums = "".join(f'<span style="display:inline-block;width:78px;text-align:right;font-weight:{900 if k == i else 500};font-size:{40 if k == i else 32}px;color:{cols[k]};opacity:{1 if k == i else .6}">{round(f[k] * 100)}</span>' for k in range(3))
        risk = ' <b style="color:#e4372c">!</b>' if (g.get("spread_warn") or g.get("inj_warn")) else ""
        rows.append(f"""<div style="padding:12px 0 10px;border-bottom:2px solid rgba(20,18,16,.2)">
<div style="display:flex;align-items:baseline;gap:18px"><span style="font-size:24px;font-weight:900;letter-spacing:.08em;width:84px">{t:%H:%M}</span>
<span class="serif" style="font-size:36px;flex:1;white-space:nowrap;overflow:hidden;text-overflow:ellipsis">{esc(short_name(g['home']))} <i style="color:#e4372c;font-size:28px">vs</i> {esc(short_name(g['away']))}{risk}</span>
<span class="serif">{nums}</span></div>
<div style="display:flex;height:12px;margin:8px 0 0 102px;background:#d8d3c7"><div style="width:{f[0] * 100:.1f}%;background:#141210"></div><div style="width:{f[1] * 100:.1f}%;background:#e4372c"></div><div style="width:{f[2] * 100:.1f}%;background:#8d877a"></div></div></div>""")
    sub = f"{league}" + (f" · {part}/{parts}" if parts > 1 else "")
    return (CARD_HEAD + f"""<div class="top"><span>{esc(_card_date(now))}</span><span>Os jogos de hoje</span></div>
<div class="mast serif" style="font-size:84px">Radar do Golo</div>
<div style="text-align:center;margin-top:20px"><span style="background:#e4372c;color:#fff;font-weight:900;font-size:24px;letter-spacing:.22em;padding:10px 22px;text-transform:uppercase">{esc(sub)}</span></div>
<div style="display:flex;justify-content:flex-end;gap:0;padding:14px 56px 0;font-size:16px;font-weight:900;letter-spacing:.12em;text-transform:uppercase"><span style="width:78px;text-align:right">Casa</span><span style="width:78px;text-align:right">Emp.</span><span style="width:78px;text-align:right">Fora</span></div>
<div style="padding:0 56px">{''.join(rows)}</div>
<div class="foot"><span>Radar do Golo</span><b>●</b><span>! = jogo de risco</span></div></body></html>""")


def league_cards(shown, now):
    """Um (ou mais) cartão(ões) por liga, com todos os jogos dessa liga, enviados como álbum."""
    htmls = []
    for league, games in shown.items():
        gs = sorted((g for g in games if g.get("final")), key=lambda g: g["time"])
        if not gs:
            continue
        parts = [gs[i:i + ROWS_PER_CARD] for i in range(0, len(gs), ROWS_PER_CARD)]
        for n, part in enumerate(parts, 1):
            htmls.append(league_card_html(league, part, now, n, len(parts)))
    htmls = htmls[:10]
    if not htmls:
        return
    pngs = render_cards(htmls)
    if pngs:
        send_album(pngs, f"🃏 <b>Os jogos de hoje</b> ({len(pngs)} cartões, um por liga)")


def morning_card(shown, now):
    cands = []
    for league, games in shown.items():
        for g in games:
            if g.get("final") and parse_iso(g["time"]) > now:
                cands.append((fame_score(league, g), g))
    if not cands:
        return
    g = max(cands, key=lambda x: x[0])[1]
    yl = ""
    try:
        yl = yesterday_line(read_csv(PREDS_FILE), now)
    except Exception:  # noqa: BLE001
        pass
    extra = f"<b>●</b><span>{esc(re.sub(r'^\S+\s+', '', yl))}</span>" if yl else ""
    send_card(cover_html(g, now, extra), f"🎯 <b>O jogo do dia</b> — mais detalhes na mensagem seguinte")
    return g


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


SHORT_ALIAS = {"sporting lisbon": "Sporting", "sporting cp": "Sporting", "sporting clube de portugal": "Sporting",
               "sl benfica": "Benfica", "sporting braga": "Braga", "sc braga": "Braga", "vitoria guimaraes": "Vitória SC",
               "bayern munich": "Bayern de Munique", "inter milan": "Inter", "ac milan": "Milan",
               "atletico madrid": "Atlético de Madrid", "paris saint germain": "PSG", "paris saint-germain": "PSG",
               "manchester united": "Man. United", "manchester city": "Man. City"}


def short_name(t):
    raw = t.lower().strip()
    t = re.sub(r"^1\.\s*", "", t)
    t = re.sub(r"\b(FC|CF|AFC|SAD|AC|SC|CD|AS|RC|OGC|SS|SSC|US|TSG|VfB|VfL|SV|RB)\b\.?", " ", t)
    t = re.sub(r"\s+", " ", t).strip() or t
    return SHORT_ALIAS.get(raw) or SHORT_ALIAS.get(t.lower()) or t


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
    return [head] + body + [note, "— <b>Radar do Golo</b> 🎯"]


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
        sl = streak_line(preds_h)
        if sl:
            sm.append(sl)
        blocks.append("\n".join(sm))
    if newly:
        blocks.append(history_blocks(picks_h, preds_h, newly)[0])
    try:
        blocks.extend(group_duel(done, now))
        blocks.extend(exact_duel(done, now))
    except Exception as e:  # noqa: BLE001
        print("Bot contra o grupo falhou:", e, file=sys.stderr)
    blocks.append("— <b>Radar do Golo</b> 🎯")
    try:
        sl2 = streak_line(preds_h)
        if done:
            send_card(night_html(done, now, f"<b>●</b><span>{esc(re.sub(r'^\S+\s+', '', sl2))}</span>" if sl2 else ""), "🌙 <b>Resultados de hoje</b>")
    except Exception as e:  # noqa: BLE001
        print("Cartão da noite falhou:", e, file=sys.stderr)
    telegram(blocks)


# ---------- onzes iniciais (modo "onze") ----------
ONZE_FILE = f"{HIST_DIR}/onzes.txt"
ONZE_WINDOW_MIN = 75      # só jogos que começam nos próximos 75 minutos
ONZE_MAX_REQ = 25         # pedidos à API-Football por execução (limite grátis: 100/dia)
ONZE_ROTATION = 4         # tantas mudanças face ao jogo anterior = "muita rotação"


def af_get(path, params):
    r = requests.get("https://v3.football.api-sports.io/" + path,
                     headers={"x-apisports-key": AF_KEY}, params=params, timeout=30)
    data = r.json()
    if r.status_code != 200 or data.get("errors"):
        print("API-Football:", path, r.status_code, str(data.get("errors"))[:200], file=sys.stderr)
        return []
    return data.get("response", [])


def af_lineup(fixture_id):
    """{id_equipa: {"nome","formacao","xi":[(id,nome)]}} — vazio se ainda não há onzes."""
    out = {}
    for it in af_get("fixtures/lineups", {"fixture": fixture_id}):
        xi = [(p["player"]["id"], p["player"]["name"]) for p in it.get("startXI", [])]
        if xi:
            out[it["team"]["id"]] = {"nome": it["team"]["name"], "formacao": it.get("formation") or "", "xi": xi}
    return out


def onze_line(side_icon, team, lu, prev_ids):
    names = ", ".join(esc(n.split()[-1]) for _, n in lu["xi"])
    form = f" ({lu['formacao']})" if lu["formacao"] else ""
    line = f"{side_icon} <b>{esc(team)}</b>{form}\n{names}"
    if prev_ids:
        ch = sum(1 for i, _ in lu["xi"] if i not in prev_ids)
        warn = " ⚠️ muita rotação" if ch >= ONZE_ROTATION else ""
        line += f"\n🔄 {ch} mudança(s) face ao jogo anterior{warn}"
    return line


def lineups_mode(now):
    """Envia o onze inicial dos jogos analisados que começam daqui a pouco (se já estiver publicado)."""
    if not AF_KEY:
        print("Sem APIFOOTBALL_KEY; nada a fazer.", file=sys.stderr)
        return
    preds = read_csv(PREDS_FILE)
    sent = set(open(ONZE_FILE, encoding="utf-8").read().split("\n")) if os.path.exists(ONZE_FILE) else set()
    lim = now + dt.timedelta(minutes=ONZE_WINDOW_MIN)
    todo = [r for r in preds if r.get("estado") == "pendente" and r["id"] not in sent
            and now - dt.timedelta(minutes=5) <= parse_iso(r["inicio_utc"]) <= lim]
    if not todo:
        print("Sem jogos a começar nos próximos minutos.", file=sys.stderr)
        return
    code_of = {v[0]: k for k, v in LEAGUES.items()}
    season = season_start(now.date())
    reqs = [0]

    def get(path, params):
        reqs[0] += 1
        return af_get(path, params)

    fx_cache, blocks, newly = {}, [], []
    for r in sorted(todo, key=lambda r: r["inicio_utc"]):
        if reqs[0] >= ONZE_MAX_REQ:
            break
        code = code_of.get(r["liga"])
        if code not in AF_LEAGUES:
            continue
        try:
            day = parse_iso(r["inicio_utc"]).date().isoformat()
            if (code, day) not in fx_cache:
                fx_cache[(code, day)] = get("fixtures", {"league": AF_LEAGUES[code], "season": season, "date": day})
            fixtures = fx_cache[(code, day)]
            names = [f["teams"]["home"]["name"] for f in fixtures]
            hn = match_team(r["casa"], names, 0.72)
            fx = next((f for f in fixtures if f["teams"]["home"]["name"] == hn), None) if hn else None
            if not fx:
                continue
            reqs[0] += 1
            lu = af_lineup(fx["fixture"]["id"])
            hid, aid = fx["teams"]["home"]["id"], fx["teams"]["away"]["id"]
            if hid not in lu or aid not in lu:
                continue  # onzes ainda não publicados: tenta na próxima execução
            prev = {}
            for tid in (hid, aid):
                if reqs[0] >= ONZE_MAX_REQ:
                    break
                last = get("fixtures", {"team": tid, "last": 1})
                if last:
                    reqs[0] += 1
                    pl = af_lineup(last[0]["fixture"]["id"])
                    prev[tid] = {i for i, _ in pl.get(tid, {}).get("xi", [])}
            blocks.append(f"📋 <b>ONZES INICIAIS</b> · 🕗 <i>{fmt_time(r['inicio_utc'])}</i>\n"
                          f"<b>{esc(r['casa'])}</b> vs <b>{esc(r['fora'])}</b>\n\n"
                          + onze_line("🏠", r["casa"], lu[hid], prev.get(hid)) + "\n\n"
                          + onze_line("✈️", r["fora"], lu[aid], prev.get(aid))
                          + "\n<i>(informativo: as probabilidades não mudam)</i>")
            newly.append(r["id"])
        except Exception as e:  # noqa: BLE001
            print("Onzes falharam:", r.get("casa"), e, file=sys.stderr)
    print(f"Onzes: {len(blocks)} jogo(s), {reqs[0]} pedidos.", file=sys.stderr)
    if blocks:
        telegram(blocks)
        os.makedirs(HIST_DIR, exist_ok=True)
        with open(ONZE_FILE, "a", encoding="utf-8") as f:
            f.write("\n".join(newly) + "\n")


# ---------- AO VIVO (MODO=aovivo): mensagem que se atualiza sozinha + probabilidade em tempo real ----------
LIVE_POLL_S = 150          # segundos entre leituras (a API grátis tem 100 pedidos/dia)
LIVE_MAX_REQ = 70          # tecto de pedidos por jogo
LIVE_DONE = {"FT", "AET", "PEN", "PST", "CANC", "ABD", "AWD", "WO"}
LIVE_SLEEP = time.sleep    # trocado nos testes


def _grid(lh, la, top=9):
    return [[pois(i, lh) * pois(j, la) for j in range(top + 1)] for i in range(top + 1)]


def _hda(lh, la, gh=0, ga=0):
    g = _grid(lh, la)
    h = d = a = 0.0
    for i, row in enumerate(g):
        for j, pr in enumerate(row):
            diff = gh + i - (ga + j)
            if diff > 0: h += pr
            elif diff == 0: d += pr
            else: a += pr
    t = h + d + a
    return h / t, d / t, a / t


def calibrate_lambdas(lh, la, target):
    """Ajusta os golos esperados para que o 1X2 pré-jogo coincida com a probabilidade final do bot (modelo+mercado)."""
    best, bl = None, (lh, la)
    for ka in range(30, 171, 4):
        for kb in range(30, 171, 4):
            a, b = lh * ka / 100, la * kb / 100
            p = _hda(a, b)
            e = sum((x - y) ** 2 for x, y in zip(p, target))
            if best is None or e < best:
                best, bl = e, (a, b)
    return bl


def live_probs(lh, la, gh, ga, minute, red_h=0, red_a=0):
    """1X2 a partir do resultado atual e do tempo que falta (golos restantes ~ Poisson; cartão vermelho: heurística)."""
    r = max(90 - minute, 0) / 90
    r = r if minute < 90 else 0.03  # compensações
    fh = (0.75 ** red_h) * (1.25 ** red_a)
    fa = (0.75 ** red_a) * (1.25 ** red_h)
    return _hda(lh * r * fh, la * r * fa, gh, ga)


def parse_live(item, home_id):
    fx, goals, events = item.get("fixture", {}), item.get("goals", {}), item.get("events") or []
    st = fx.get("status", {})
    out = {"status": st.get("short", ""), "minute": st.get("elapsed") or 0,
           "gh": goals.get("home") or 0, "ga": goals.get("away") or 0, "goals": [], "red_h": 0, "red_a": 0}
    for e in events:
        is_home = e.get("team", {}).get("id") == home_id
        t, d = e.get("type"), e.get("detail") or ""
        tm = (e.get("time", {}).get("elapsed") or 0) + (e.get("time", {}).get("extra") or 0)
        if t == "Goal" and "Missed" not in d:
            own = "Own" in d
            out["goals"].append((tm, is_home != own, e.get("player", {}).get("name") or "", d))
        elif t == "Card" and "Red" in d:
            out["red_h" if is_home else "red_a"] += 1
    return out


def spark(vals, n=14):
    if not vals:
        return ""
    if len(vals) > n:
        step = len(vals) / n
        vals = [vals[int(i * step)] for i in range(n)]
    return "".join(SPARK[min(7, int(v * 8))] for v in vals)  # 0-100% -> 8 níveis


def live_text(home, away, kick, st, probs, pre, hist, events_txt):
    status = st["status"]
    if status in LIVE_DONE:
        head = "🏁 <b>TERMINADO</b>"
    elif status == "HT":
        head = "⏸ <b>INTERVALO</b>"
    elif status in ("NS", "TBD", ""):
        head = f"⏳ <b>VAI COMEÇAR</b> · 🕗 {fmt_time(kick)}"
    else:
        head = f"🔴 <b>AO VIVO · {st['minute']}'</b>"
    lines = [head, f"<b>{esc(home)} {st['gh']}–{st['ga']} {esc(away)}</b>", probs_line(probs),
             f"<i>Antes do jogo: {pre[0]:.0%} / {pre[1]:.0%} / {pre[2]:.0%}</i>"]
    if len(hist) >= 2:
        lines.append(f"📈 {esc(short_name(home))} {spark([h[1] for h in hist])}\n"
                     f"📉 {esc(short_name(away))} {spark([h[3] for h in hist])}")
    if events_txt:
        lines.append("\n".join(events_txt[-8:]))
    if st["red_h"] or st["red_a"]:
        lines.append(f"🟥 Expulsões: {esc(short_name(home))} {st['red_h']} · {esc(short_name(away))} {st['red_a']}")
    return "\n".join(lines)


def tg_send(text, parse="HTML"):
    r = requests.post(f"https://api.telegram.org/bot{TG_TOKEN}/sendMessage",
                      json={"chat_id": TG_CHAT, "text": text, "parse_mode": parse, "disable_web_page_preview": True}, timeout=30)
    r.raise_for_status()
    return r.json()["result"]["message_id"]


def tg_edit(mid, text):
    r = requests.post(f"https://api.telegram.org/bot{TG_TOKEN}/editMessageText",
                      json={"chat_id": TG_CHAT, "message_id": mid, "text": text, "parse_mode": "HTML",
                            "disable_web_page_preview": True}, timeout=30)
    if r.status_code == 400 and "not modified" in r.text:
        return
    r.raise_for_status()


def live_chart_url(home, away, hist, goals):
    """Gráfico da probabilidade ao longo do jogo (QuickChart, grátis). Devolve o URL da imagem ou None."""
    if len(hist) < 3:
        return None
    pts = hist if len(hist) <= 60 else hist[:: len(hist) // 60 + 1] + [hist[-1]]
    def line(label, idx, color):
        return {"label": label, "data": [{"x": p[0], "y": round(p[idx] * 100)} for p in pts],
                "borderColor": color, "backgroundColor": color, "showLine": True, "fill": False,
                "pointRadius": 0, "borderWidth": 3, "lineTension": 0.25}
    gl = []
    for tm, is_home, player, _ in goals:
        near = min(hist, key=lambda p: abs(p[0] - tm))
        gl.append({"x": tm, "y": round(near[1 if is_home else 3] * 100)})
    ds = [line(short_name(home), 1, "#2e9e4f"), line("Empate", 2, "#e0a800"), line(short_name(away), 3, "#2f6fd6")]
    if gl:
        ds.append({"label": "⚽ Golo", "data": gl, "showLine": False, "pointRadius": 9, "pointStyle": "star",
                   "borderColor": "#000", "backgroundColor": "#fff"})
    cfg = {"type": "scatter", "data": {"datasets": ds},
           "options": {"title": {"display": True, "text": f"{short_name(home)} vs {short_name(away)} — probabilidade ao vivo", "fontSize": 18},
                       "scales": {"xAxes": [{"type": "linear", "ticks": {"min": 0, "max": max(90, int(hist[-1][0])), "stepSize": 15},
                                             "scaleLabel": {"display": True, "labelString": "minuto"}}],
                                  "yAxes": [{"ticks": {"min": 0, "max": 100}, "scaleLabel": {"display": True, "labelString": "%"}}]}}}
    r = requests.post("https://quickchart.io/chart/create",
                      json={"chart": cfg, "width": 900, "height": 480, "backgroundColor": "white", "version": "2"}, timeout=30)
    d = r.json()
    return d.get("url") if r.status_code == 200 and d.get("success") else None


# ---------- sondagem diária: o jogo ao vivo é escolhido por votação ----------
POLL_FILE = f"{HIST_DIR}/sondagem.json"
FAMOUS = ["benfica", "porto", "sporting", "braga", "real madrid", "barcelona", "atletico", "athletic", "sevilla",
          "manchester city", "manchester united", "liverpool", "arsenal", "chelsea", "tottenham", "newcastle", "aston villa",
          "bayern", "dortmund", "leverkusen", "paris", "marseille", "monaco", "juventus", "inter", "milan", "napoli", "roma",
          "lazio", "atalanta", "ajax", "psv", "feyenoord", "portugal", "espanha", "spain", "franca", "france", "inglaterra",
          "england", "alemanha", "germany", "italia", "italy", "brasil", "argentina", "croatia", "croacia"]
LEAGUE_FAME = {"Champions League": 6, "Liga das Nações": 4, "Premier League": 3, "La Liga": 3, "Liga Portugal": 3,
               "Serie A": 2, "Bundesliga": 2, "Ligue 1": 2}
POLL_MIN_AHEAD_MIN = 90      # só jogos que começam daqui a mais de 90 min
POLL_CLOSE_BEFORE_MIN = 30   # a votação fecha 30 min antes do primeiro jogo da sondagem


def fame_score(league, g):
    names = norm(g["home"]) + " | " + norm(g["away"])
    n = sum(1 for f in FAMOUS if f in norm(g["home"])) > 0, sum(1 for f in FAMOUS if f in norm(g["away"])) > 0
    f = g.get("final") or (0.4, 0.3, 0.3)
    return 10 * sum(n) + LEAGUE_FAME.get(league, 0) + 2 * (1 - max(f))


def send_poll(shown, now):
    """Depois da mensagem das 9h: sondagem com os 5 jogos mais 'famosos' do dia."""
    cands = []
    for league, games in shown.items():
        for g in games:
            if parse_iso(g["time"]) > now + dt.timedelta(minutes=POLL_MIN_AHEAD_MIN):
                cands.append((fame_score(league, g), league, g))
    cands.sort(key=lambda x: -x[0])
    top = cands[:5]
    if len(top) < 2:
        return
    top.sort(key=lambda x: x[2]["time"])  # por hora do jogo
    opts, saved = [], []
    for _, league, g in top:
        opts.append(f"{fmt_time(g['time']).split(' · ')[-1]} · {short_name(g['home'])} vs {short_name(g['away'])}"[:100])
        f = g.get("final") or (0.4, 0.3, 0.3)
        p = g.get("p") or {}
        saved.append({"casa": g["home"], "fora": g["away"], "fd_casa": g.get("fd_home", ""), "fd_fora": g.get("fd_away", ""),
                      "inicio_utc": g["time"], "fH": f"{f[0]:.4f}", "fD": f"{f[1]:.4f}", "fA": f"{f[2]:.4f}",
                      "xg_casa": f"{p['lh']:.2f}" if p.get("lh") else "", "xg_fora": f"{p['la']:.2f}" if p.get("la") else ""})
    close = min(parse_iso(o["inicio_utc"]) for o in saved) - dt.timedelta(minutes=POLL_CLOSE_BEFORE_MIN)
    close_txt = close.astimezone(LISBON).strftime("%H:%M")
    r = requests.post(f"https://api.telegram.org/bot{TG_TOKEN}/sendPoll",
                      json={"chat_id": TG_CHAT, "question": f"🗳️ Que jogo queres ver AO VIVO hoje? Votação até às {close_txt}; o mais votado é seguido minuto a minuto.",
                            "options": opts, "is_anonymous": True, "allows_multiple_answers": False}, timeout=30)
    r.raise_for_status()
    res = r.json()["result"]
    os.makedirs(HIST_DIR, exist_ok=True)
    with open(POLL_FILE, "w", encoding="utf-8") as f:
        json.dump({"date": now.date().isoformat(), "poll_id": res["poll"]["id"], "message_id": res["message_id"],
                   "fecha_utc": close.strftime("%Y-%m-%dT%H:%M:%SZ"), "options": saved}, f)


# ---------- Bot contra o grupo ----------
GROUP_FILE = f"{HIST_DIR}/palpite_grupo.json"
DUEL_GROUP_FILE = f"{HIST_DIR}/duelo_grupo.csv"
DUEL_GROUP_FIELDS = ["data", "casa", "fora", "resultado", "bot", "grupo", "votos", "bot_ok", "grupo_ok"]
GROUP_NAMES = ("casa", "empate", "fora")
TACA_FILE = f"{HIST_DIR}/taca.csv"
TACA_FIELDS = ["data", "uid", "nome", "voto", "certo"]


def read_voters(poll_id):
    """Quem votou em quê (sondagem não anónima): último voto de cada pessoa, a partir dos updates poll_answer."""
    r = requests.post(f"https://api.telegram.org/bot{TG_TOKEN}/getUpdates",
                      json={"offset": -100, "limit": 100, "allowed_updates": ["poll", "poll_answer"]}, timeout=30)
    r.raise_for_status()
    out = {}
    for u in r.json().get("result", []):
        a = u.get("poll_answer")
        if a and a.get("poll_id") == poll_id and a.get("user"):
            usr = a["user"]
            if a.get("option_ids"):
                out[usr["id"]] = (usr.get("first_name") or "?", a["option_ids"][0])
            else:
                out.pop(usr["id"], None)  # retirou o voto
    return out


def taca_lines(rows):
    """Classificação acumulada: acertos/jogos por pessoa (nomes próprios; o bot entra como jogador)."""
    tab = {}
    for r in rows:
        t = tab.setdefault(r["uid"], {"nome": r["nome"], "ok": 0, "n": 0})
        t["nome"] = r["nome"]
        t["n"] += 1
        t["ok"] += int(r["certo"])
    duel = [r for r in read_csv(DUEL_GROUP_FILE)]
    if duel:
        tab["bot"] = {"nome": "🤖 Bot", "ok": sum(int(r["bot_ok"]) for r in duel), "n": len(duel)}
    rank = sorted(tab.values(), key=lambda t: (-t["ok"], -(t["ok"] / t["n"]), t["nome"]))
    medals = ["🥇", "🥈", "🥉"]
    return [f"{medals[i] if i < 3 else str(i + 1) + '.'} {esc(t['nome'])} — {t['ok']}/{t['n']} ({t['ok'] / t['n']:.0%})"
            for i, t in enumerate(rank[:8])]


def send_group_poll(shown, now):
    """Segunda sondagem das 9h: o grupo palpita no jogo mais famoso; o bot guarda o seu palpite em segredo."""
    cands = []
    for league, games in shown.items():
        for g in games:
            if g.get("final") and parse_iso(g["time"]) > now + dt.timedelta(minutes=POLL_MIN_AHEAD_MIN):
                cands.append((fame_score(league, g), g))
    if not cands:
        return
    cands.sort(key=lambda x: -x[0])
    g = cands[0][1]
    f = g["final"]
    bot = f.index(max(f))
    q = f"🆚 BOT CONTRA O GRUPO: {short_name(g['home'])} vs {short_name(g['away'])} — quem ganha? Vota antes do jogo (o bot já escolheu, em segredo)."
    r = requests.post(f"https://api.telegram.org/bot{TG_TOKEN}/sendPoll",
                      json={"chat_id": TG_CHAT, "question": q[:300],
                            "options": [f"🏠 {short_name(g['home'])}"[:100], "🤝 Empate", f"✈️ {short_name(g['away'])}"[:100]],
                            "is_anonymous": False, "allows_multiple_answers": False}, timeout=30)
    r.raise_for_status()
    res = r.json()["result"]
    with open(GROUP_FILE, "w", encoding="utf-8") as fh:
        json.dump({"date": now.date().isoformat(), "poll_id": res["poll"]["id"], "message_id": res["message_id"],
                   "casa": g["home"], "fora": g["away"], "inicio_utc": g["time"], "bot": bot,
                   "probs": [round(x, 4) for x in f]}, fh)


def group_duel(done, now):
    """À noite: compara o palpite do grupo (opção mais votada) com o do bot. Devolve blocos de texto."""
    if not os.path.exists(GROUP_FILE):
        return []
    with open(GROUP_FILE, encoding="utf-8") as fh:
        d = json.load(fh)
    if d.get("done") or d.get("date") != now.astimezone(LISBON).date().isoformat():
        return []
    row = next((r for r in done if r["casa"] == d["casa"] and r["fora"] == d["fora"]), None)
    if not row:
        return []
    res = _result_idx(row)
    d["done"] = True
    with open(GROUP_FILE, "w", encoding="utf-8") as fh:
        json.dump(d, fh)
    votes = None
    try:  # stopPoll devolve a contagem final, sem depender do getUpdates
        r = requests.post(f"https://api.telegram.org/bot{TG_TOKEN}/stopPoll",
                          json={"chat_id": TG_CHAT, "message_id": d["message_id"]}, timeout=30)
        r.raise_for_status()
        votes = [o["voter_count"] for o in r.json()["result"]["options"]]
    except Exception as e:  # noqa: BLE001
        print("stopPoll (grupo) falhou:", e, file=sys.stderr)
        try:
            votes = read_votes(d["poll_id"])
        except Exception as e2:  # noqa: BLE001
            print("read_votes (grupo) falhou:", e2, file=sys.stderr)
    if not votes or sum(votes) < 2:
        return ["🆚 <b>BOT CONTRA O GRUPO</b>\nPoucos votos hoje (menos de 2), não conta para o placar."]
    top = max(votes)
    grp = [i for i, v in enumerate(votes) if v == top]
    bot = d["bot"]
    lines = [f"🆚 <b>BOT CONTRA O GRUPO</b>",
             f"{esc(d['casa'])} {row['golos_casa']}–{row['golos_fora']} {esc(d['fora'])}",
             f"🤖 Bot: {GROUP_NAMES[bot]} {d['probs'][bot]:.0%} {'✅' if bot == res else '❌'}"]
    if len(grp) == 1:
        gi = grp[0]
        lines.append(f"👥 Grupo: {GROUP_NAMES[gi]} ({votes[gi]}/{sum(votes)} votos) {'✅' if gi == res else '❌'}")
        gtxt, gok = GROUP_NAMES[gi], int(gi == res)
    else:
        lines.append(f"👥 Grupo: empate nos votos ({votes}) — não conta")
        gtxt, gok = "empate_votos", ""
    rows = read_csv(DUEL_GROUP_FILE)
    rows.append({"data": d["date"], "casa": d["casa"], "fora": d["fora"], "resultado": GROUP_NAMES[res], "bot": GROUP_NAMES[bot],
                 "grupo": gtxt, "votos": "/".join(map(str, votes)), "bot_ok": int(bot == res), "grupo_ok": gok})
    write_csv(DUEL_GROUP_FILE, DUEL_GROUP_FIELDS, rows)
    try:  # Taça de previsores: pontos individuais (1 por palpite certo)
        voters = read_voters(d["poll_id"])
        trows = read_csv(TACA_FILE)
        for uid, (nome, opt) in voters.items():
            trows.append({"data": d["date"], "uid": hashlib.sha256(str(uid).encode()).hexdigest()[:10], "nome": nome,
                          "voto": GROUP_NAMES[opt] if 0 <= opt < 3 else "?", "certo": int(opt == res)})
        if voters:
            write_csv(TACA_FILE, TACA_FIELDS, trows)
            got = [f"{'✅' if o == res else '❌'} {esc(n)}" for n, o in voters.values()]
            lines.append("🗳️ Palpites: " + " · ".join(got[:12]))
            lines.append("🏆 <b>TAÇA DE PREVISORES</b>\n" + "\n".join(taca_lines(trows)))
    except Exception as e:  # noqa: BLE001
        print("Taça falhou:", e, file=sys.stderr)
    sc = [r for r in rows if r["grupo_ok"] != ""]
    if sc:
        b = sum(int(r["bot_ok"]) for r in sc)
        gp = sum(int(r["grupo_ok"]) for r in sc)
        lead = "🤖 Bot na frente" if b > gp else "👥 Grupo na frente" if gp > b else "🤝 Empatados"
        lines.append(f"📊 Placar ({len(sc)} {"jogo" if len(sc) == 1 else "jogos"}): Bot {b} · Grupo {gp} — {lead}")
    return ["\n".join(lines)]


# ---------- resultado exato (sextas-feiras) ----------
EXATO_FILE = f"{HIST_DIR}/exato.json"
EXATO_CSV = f"{HIST_DIR}/exato.csv"
EXATO_FIELDS = ["data", "casa", "fora", "resultado", "bot", "grupo", "votos", "bot_ok", "grupo_ok"]


def send_exact_poll(shown, now):
    """Sextas-feiras: o grupo tenta adivinhar o resultado exato do jogo mais famoso das próximas 48 h."""
    cands = []
    for league, games in shown.items():
        for g in games:
            if g.get("p") and parse_iso(g["time"]) > now + dt.timedelta(minutes=POLL_MIN_AHEAD_MIN):
                cands.append((fame_score(league, g), g))
    if not cands:
        return
    g = max(cands, key=lambda x: x[0])[1]
    sc = [f"{i}–{j}" for (i, j), _ in top_scores(g["p"]["lh"], g["p"]["la"], 4)]
    opts = sc + ["Outro resultado"]
    q = f"🎯 RESULTADO EXATO: {short_name(g['home'])} vs {short_name(g['away'])} ({fmt_time(g['time'])}). Qual será? O bot já escolheu."
    r = requests.post(f"https://api.telegram.org/bot{TG_TOKEN}/sendPoll",
                      json={"chat_id": TG_CHAT, "question": q[:300], "options": opts,
                            "is_anonymous": True, "allows_multiple_answers": False}, timeout=30)
    r.raise_for_status()
    res = r.json()["result"]
    with open(EXATO_FILE, "w", encoding="utf-8") as f:
        json.dump({"date": now.date().isoformat(), "poll_id": res["poll"]["id"], "message_id": res["message_id"],
                   "casa": g["home"], "fora": g["away"], "inicio_utc": g["time"], "opcoes": opts, "bot": sc[0]}, f)


def exact_duel(done, now):
    """À noite: se o jogo da sondagem de resultado exato terminou, compara bot, grupo e realidade."""
    if not os.path.exists(EXATO_FILE):
        return []
    with open(EXATO_FILE, encoding="utf-8") as f:
        d = json.load(f)
    if d.get("done"):
        return []
    row = next((r for r in done if r["casa"] == d["casa"] and r["fora"] == d["fora"]), None)
    if not row:
        return []
    real = f"{row['golos_casa']}–{row['golos_fora']}"
    d["done"] = True
    with open(EXATO_FILE, "w", encoding="utf-8") as f:
        json.dump(d, f)
    votes = None
    try:
        r = requests.post(f"https://api.telegram.org/bot{TG_TOKEN}/stopPoll",
                          json={"chat_id": TG_CHAT, "message_id": d["message_id"]}, timeout=30)
        r.raise_for_status()
        votes = [o["voter_count"] for o in r.json()["result"]["options"]]
    except Exception as e:  # noqa: BLE001
        print("stopPoll (exato) falhou:", e, file=sys.stderr)
    lines = ["🎯 <b>RESULTADO EXATO</b>", f"{esc(d['casa'])} {real} {esc(d['fora'])}",
             f"🤖 Bot: {d['bot']} {'✅' if d['bot'] == real else '❌'}"]
    gtxt, gok = "", ""
    if votes and sum(votes) >= 2:
        top = max(votes)
        win = [i for i, v in enumerate(votes) if v == top]
        if len(win) == 1:
            gtxt = d["opcoes"][win[0]]
            gok = int(gtxt == real)
            lines.append(f"👥 Grupo: {gtxt} ({top}/{sum(votes)} votos) {'✅' if gok else '❌'}")
        else:
            lines.append("👥 Grupo: empate nos votos — não conta")
    else:
        lines.append("👥 Poucos votos — não conta")
    rows = read_csv(EXATO_CSV)
    rows.append({"data": d["date"], "casa": d["casa"], "fora": d["fora"], "resultado": real, "bot": d["bot"],
                 "grupo": gtxt, "votos": "/".join(map(str, votes or [])), "bot_ok": int(d["bot"] == real), "grupo_ok": gok})
    write_csv(EXATO_CSV, EXATO_FIELDS, rows)
    return ["\n".join(lines)]


def read_votes(poll_id):
    r = requests.post(f"https://api.telegram.org/bot{TG_TOKEN}/getUpdates",
                      json={"allowed_updates": ["poll"], "limit": 100}, timeout=30)
    r.raise_for_status()
    votes = None
    for u in r.json().get("result", []):
        p = u.get("poll")
        if p and p.get("id") == poll_id:
            votes = [o["voter_count"] for o in p["options"]]  # fica com o estado mais recente
    return votes


def auto_choice(now):
    """Jogo mais votado de hoje, mas só se começar dentro de ~20 minutos (para não ficar à espera horas)."""
    if not os.path.exists(POLL_FILE):
        return None
    with open(POLL_FILE, encoding="utf-8") as f:
        d = json.load(f)
    if d.get("date") != now.date().isoformat():
        return None
    if d.get("fecha_utc") and now >= parse_iso(d["fecha_utc"]):
        try:  # fecha a sondagem: a partir daqui o resultado fica fixo (um só jogo ao vivo por dia)
            requests.post(f"https://api.telegram.org/bot{TG_TOKEN}/stopPoll",
                          json={"chat_id": TG_CHAT, "message_id": d["message_id"]}, timeout=30)
        except Exception as e:  # noqa: BLE001
            print("stopPoll falhou (ignorado):", e, file=sys.stderr)
    votes = read_votes(d["poll_id"]) or [0] * len(d["options"])
    best = max(range(len(votes)), key=lambda i: (votes[i], -i))
    r = d["options"][best]
    k = parse_iso(r["inicio_utc"])
    print(f"Votos: {votes} → {r['casa']} vs {r['fora']}", file=sys.stderr)
    if not (now - dt.timedelta(minutes=3) <= k <= now + dt.timedelta(minutes=21)):
        return None
    return r


def find_live(items, casas, foras):
    """Procura o jogo na lista de jogos ao vivo da API (por nome das duas equipas; aceita vários nomes de cada)."""
    for it in items or []:
        h, a = it["teams"]["home"]["name"], it["teams"]["away"]["name"]
        if any(match_team(n, [h], 0.72) for n in casas if n) and any(match_team(n, [a], 0.72) for n in foras if n):
            return it
    return None


def pick_live_game(preds, text, now):
    t = norm(text)
    best = None
    for r in preds:
        if t and t not in norm(r["casa"]) and t not in norm(r["fora"]):
            continue
        k = parse_iso(r["inicio_utc"])
        if not (now - dt.timedelta(hours=3) <= k <= now + dt.timedelta(hours=14)):
            continue
        if best is None or abs((k - now).total_seconds()) < abs((parse_iso(best["inicio_utc"]) - now).total_seconds()):
            best = r
    return best


AOVIVO_FILE = f"{HIST_DIR}/aovivo.json"


def live_snapshot(r, st, probs, pre, hist, ev_lines, push=False):
    """Guarda o estado do jogo ao vivo para o site; só faz commit nos momentos importantes (golo, intervalo, fim)."""
    try:
        data = {"atualizado": now_utc().strftime("%Y-%m-%dT%H:%M:%SZ"), "casa": r["casa"], "fora": r["fora"],
                "inicio_utc": r["inicio_utc"], "estado": st["status"], "minuto": st["minute"],
                "golos_casa": st["gh"], "golos_fora": st["ga"], "vermelhos": [st["red_h"], st["red_a"]],
                "pre": [round(x, 4) for x in pre], "agora": [round(x, 4) for x in probs],
                "hist": [[h[0], round(h[1], 3), round(h[2], 3), round(h[3], 3)] for h in hist][-200:],
                "eventos": [re.sub(r"<[^>]+>", "", html.unescape(e)) for e in ev_lines][-20:],
                "terminado": st["status"] in LIVE_DONE}
        os.makedirs(HIST_DIR, exist_ok=True)
        with open(AOVIVO_FILE, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False)
        if push and os.getenv("GITHUB_ACTIONS") == "true":
            git = lambda *a: subprocess.run(["git", *a], check=True, capture_output=True, text=True, timeout=120)
            git("config", "user.name", "github-actions")
            git("config", "user.email", "github-actions@users.noreply.github.com")
            git("add", AOVIVO_FILE)
            if subprocess.run(["git", "diff", "--cached", "--quiet"]).returncode == 0:
                return
            git("commit", "-m", "Ao vivo")
            for _ in range(3):
                try:
                    git("pull", "--rebase", "--autostash")
                    git("push")
                    break
                except subprocess.CalledProcessError as e:
                    print("push ao vivo falhou:", (e.stderr or "")[:200], file=sys.stderr)
                    time.sleep(5)
    except Exception as e:  # noqa: BLE001
        print("Snapshot ao vivo falhou (ignorado):", e, file=sys.stderr)


def live_mode(now):
    if not AF_KEY:
        print("Sem APIFOOTBALL_KEY.", file=sys.stderr)
        return
    preds = read_csv(PREDS_FILE)
    jogo = os.getenv("JOGO", "").strip()
    r = pick_live_game(preds, jogo, now) if jogo else auto_choice(now)
    if not r:
        print("Nenhum jogo para seguir agora." if not jogo else "Jogo não encontrado no histórico (tem de ter sido analisado na mensagem das 9h).", file=sys.stderr)
        return
    kick = parse_iso(r["inicio_utc"])
    reqs = [0]

    def get(path, params):
        reqs[0] += 1
        return af_get(path, params)

    pre = _trio(r, "fH", "fD", "fA") or _trio(r, "pH", "pD", "pA")
    lh0, la0 = fnum(r.get("xg_casa")) or 1.4, fnum(r.get("xg_fora")) or 1.1
    lh, la = calibrate_lambdas(lh0, la0, pre)
    # espera pelo apito inicial
    while now_utc() < kick - dt.timedelta(minutes=2):
        LIVE_SLEEP(min(60, max(1, (kick - now_utc()).total_seconds())))
    st0 = {"status": "NS", "minute": 0, "gh": 0, "ga": 0, "red_h": 0, "red_a": 0}
    mid = tg_send(live_text(r["casa"], r["fora"], r["inicio_utc"], st0, pre, pre, [], []))
    hist, seen, ev_lines, last_txt, st = [(0, *pre)], 0, [], "", st0
    live_snapshot(r, st0, pre, pre, hist, [], push=True)
    last_key = ("NS", 0)
    prev, fid, home_id, missing, seen_live = pre, None, None, 0, False
    swings = []  # (variação da prob. da casa, minuto, jogador, equipa, antes, depois)
    while reqs[0] < LIVE_MAX_REQ:
        LIVE_SLEEP(LIVE_POLL_S)
        try:
            # o plano grátis só deixa ver jogos AO VIVO (fixtures?live=all): um pedido traz todos os jogos
            items = get("fixtures", {"live": "all"})
            it = find_live(items, [r["casa"], r.get("fd_casa")], [r["fora"], r.get("fd_fora")])
            if it is None:
                if seen_live:
                    missing += 1
                    if missing >= 2:  # o jogo saiu da lista ao vivo = terminou
                        st = dict(st, status="FT")
                elif now_utc() > kick + dt.timedelta(minutes=25):
                    print("Jogo não apareceu ao vivo na API.", file=sys.stderr)
                    break
            else:
                seen_live, missing = True, 0
                fid, home_id = it["fixture"]["id"], it["teams"]["home"]["id"]
                st = parse_live(it, home_id)
            if not seen_live:
                continue
            probs = live_probs(lh, la, st["gh"], st["ga"], 45 if st["status"] == "HT" else st["minute"], st["red_h"], st["red_a"])
            swing = probs  # para os avisos de golo (não o 100% do apito final)
            if st["status"] in LIVE_DONE:
                probs = (1.0, 0.0, 0.0) if st["gh"] > st["ga"] else ((0.0, 1.0, 0.0) if st["gh"] == st["ga"] else (0.0, 0.0, 1.0))
            hist.append((st["minute"], *probs))
            for tm, is_home, player, d in st["goals"][seen:]:
                who = r["casa"] if is_home else r["fora"]
                pen = " (p.b.)" if "Own" in d else (" (g.p.)" if "Penalty" in d else "")
                ev_lines.append(f"⚽ {tm}' {esc(player)} ({esc(short_name(who))}){pen}")
                swings.append((abs(swing[0] - prev[0]) + abs(swing[2] - prev[2]), tm, player, who, prev, swing))
                try:
                    tg_send(f"⚽ <b>GOLO! {esc(r['casa'])} {st['gh']}–{st['ga']} {esc(r['fora'])}</b> · {tm}'\n"
                            f"{esc(player)} ({esc(short_name(who))}){pen}\n"
                            f"{esc(short_name(r['casa']))}: {prev[0]:.0%} → {swing[0]:.0%} · {esc(short_name(r['fora']))}: {prev[2]:.0%} → {swing[2]:.0%}")
                except Exception as e:  # noqa: BLE001
                    print("Aviso de golo falhou:", e, file=sys.stderr)
            seen = len(st["goals"])
            prev = swing
            key = (st["status"] if st["status"] in ("HT", "2H", *LIVE_DONE) else "1H", st["gh"] + st["ga"])
            live_snapshot(r, st, probs, pre, hist, ev_lines, push=key != last_key)
            last_key = key
            txt = live_text(r["casa"], r["fora"], r["inicio_utc"], st, probs, pre, hist, ev_lines)
            if txt != last_txt:
                tg_edit(mid, txt)
                last_txt = txt
        except Exception as e:  # noqa: BLE001
            print("Leitura ao vivo falhou:", e, file=sys.stderr)
        if st["status"] in LIVE_DONE:
            break
    try:
        url = live_chart_url(r["casa"], r["fora"], hist, st["goals"])
        if url:
            res = _result_idx({"golos_casa": st["gh"], "golos_fora": st["ga"]})
            cap = (f"📊 {esc(r['casa'])} {st['gh']}–{st['ga']} {esc(r['fora'])}\nAntes do jogo o bot dava "
                   f"{('casa', 'empate', 'fora')[res]} {pre[res]:.0%}.")
            if swings:
                big = max(swings, key=lambda x: x[0])
                if big[0] >= 0.15:
                    _, tm, pl, who, p0, p1 = big
                    cap += (f"\n🔄 <b>Momento da viragem:</b> {tm}' golo de {esc(pl)} ({esc(short_name(who))}) — "
                            f"{esc(short_name(r['casa']))} {p0[0]:.0%} → {p1[0]:.0%} · {esc(short_name(r['fora']))} {p0[2]:.0%} → {p1[2]:.0%}")
            requests.post(f"https://api.telegram.org/bot{TG_TOKEN}/sendPhoto",
                          json={"chat_id": TG_CHAT, "photo": url, "caption": cap, "parse_mode": "HTML"}, timeout=60).raise_for_status()
    except Exception as e:  # noqa: BLE001
        print("Gráfico falhou:", e, file=sys.stderr)
    print(f"Ao vivo terminado: {reqs[0]} pedidos.", file=sys.stderr)


def now_utc():
    return dt.datetime.now(dt.timezone.utc)


def api_test():
    """MODO=testeapi: diz no Telegram o que a chave grátis da API-Football consegue fazer."""
    out = ["🔧 <b>TESTE DA API-FOOTBALL</b>"]
    if not AF_KEY:
        tg_send("🔧 Sem APIFOOTBALL_KEY no GitHub.")
        return
    try:
        r = requests.get("https://v3.football.api-sports.io/status", headers={"x-apisports-key": AF_KEY}, timeout=30)
        d = r.json().get("response") or {}
        req = d.get("requests", {})
        out.append(f"Conta: {d.get('subscription', {}).get('plan', '?')} · pedidos hoje {req.get('current', '?')}/{req.get('limit_day', '?')}")
    except Exception as e:  # noqa: BLE001
        out.append(f"Estado falhou: {e}")
    today = now_utc().date()
    tests = [("Jogos de hoje (PL)", "fixtures", {"league": 39, "season": season_start(today), "date": today.isoformat()}),
             ("Jogos ao vivo agora", "fixtures", {"live": "all"}),
             ("Lesões (La Liga)", "injuries", {"league": 140, "season": season_start(today), "date": today.isoformat()})]
    for label, path, params in tests:
        try:
            rr = requests.get("https://v3.football.api-sports.io/" + path, headers={"x-apisports-key": AF_KEY}, params=params, timeout=30)
            d = rr.json()
            err = d.get("errors")
            n = len(d.get("response") or [])
            out.append(f"{'✅' if n and not err else '⚠️'} {label}: {n} resultado(s)" + (f" · erro: {str(err)[:150]}" if err else ""))
        except Exception as e:  # noqa: BLE001
            out.append(f"❌ {label}: {e}")
    tg_send("\n".join(out))


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
    if os.getenv("MODO", "").strip().lower() == "aovivo":
        try:
            live_mode(now)
        except Exception as e:  # noqa: BLE001
            print("Modo ao vivo falhou:", e, file=sys.stderr)
        return
    if os.getenv("MODO", "").strip().lower() == "testeapi":
        try:
            api_test()
        except Exception as e:  # noqa: BLE001
            print("Teste da API falhou:", e, file=sys.stderr)
        return
    if os.getenv("MODO", "").strip().lower() == "onze":
        try:
            lineups_mode(now)
        except Exception as e:  # noqa: BLE001
            print("Modo onze falhou:", e, file=sys.stderr)
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
    teams_seen = {}
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
            teams_seen[name] = sorted(st["att"].keys())
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
            if now.astimezone(LISBON).day <= 7:  # 1.ª segunda-feira do mês
                cb = calibration_block(preds_h)
                if cb:
                    extra.insert(1 if wb else 0, cb)
    except Exception as e:  # noqa: BLE001
        print("Histórico falhou:", e, file=sys.stderr)

    blocks = build_blocks(shown, fallback, extra)
    try:  # uma linha com o desempenho de ontem, no resumo do topo
        yl = yesterday_line(read_csv(PREDS_FILE), now)
        if yl and len(blocks) > 1 and blocks[1].startswith("📌"):
            blocks[1] += "\n" + yl
    except Exception as e:  # noqa: BLE001
        print("Linha de ontem falhou:", e, file=sys.stderr)
    summary = gemini_summary(plain_text(blocks))
    if summary:
        blocks.insert(2, summary)  # logo a seguir ao resumo do topo
    try:
        news = gemini_news(shown)
        if news:
            blocks.insert(3 if summary else 2, news)
    except Exception as e:  # noqa: BLE001
        print("Notícias falharam:", e, file=sys.stderr)
    try:
        extra_leagues(teams_seen)
    except Exception as e:  # noqa: BLE001
        print("Ligas extra falharam:", e, file=sys.stderr)
    try:  # lista de equipas por liga, para o site (escolha da equipa favorita)
        if teams_seen:
            write_csv(f"{HIST_DIR}/equipas.csv", ["liga", "equipa"], [{"liga": l, "equipa": t} for l, ts in teams_seen.items() for t in ts])
    except Exception as e:  # noqa: BLE001
        print("equipas.csv falhou:", e, file=sys.stderr)
    try:
        league_cards(shown, now)   # primeiro todas as ligas...
        morning_card(shown, now)   # ...e no fim o jogo do dia
    except Exception as e:  # noqa: BLE001
        print("Cartões da manhã falharam:", e, file=sys.stderr)
    telegram(blocks)
    mark_sent(now)
    try:
        send_poll(shown, now)
    except Exception as e:  # noqa: BLE001
        print("Sondagem falhou:", e, file=sys.stderr)
    try:
        send_group_poll(shown, now)
    except Exception as e:  # noqa: BLE001
        print("Sondagem do grupo falhou:", e, file=sys.stderr)
    if now.astimezone(LISBON).weekday() == 4:  # sexta-feira
        try:
            send_exact_poll(shown, now)
        except Exception as e:  # noqa: BLE001
            print("Sondagem de resultado exato falhou:", e, file=sys.stderr)
    if sim_models:  # segunda mensagem, só às segundas-feiras
        try:
            sb = season_sim_blocks(sim_models, now.date())
            if sb:
                telegram(sb)
        except Exception as e:  # noqa: BLE001
            print("Corrida da época falhou:", e, file=sys.stderr)


if __name__ == "__main__":
    main()
