"""Analista diário de futebol -> Telegram (versão 3: com histórico).

Fluxo: resultados da época (football-data.org) -> modelo de Poisson ->
probabilidades 1X2 / Over-Under 2.5 / BTTS -> compara com odds (The Odds API,
Betclic se disponível) -> envia as melhores "value bets" por Telegram.

Histórico (novo): cada sugestão e cada previsão ficam guardadas em CSV na pasta
"historico/". Nas execuções seguintes o bot descobre o resultado real, marca a
sugestão como ganha/perdida e mostra o desempenho acumulado na mensagem.
"""
import os
import re
import sys
import csv
import math
import time
import html
import difflib
import datetime as dt
from zoneinfo import ZoneInfo
import requests

FD_KEY = os.environ["FOOTBALL_DATA_KEY"]
ODDS_KEY = os.environ["ODDS_API_KEY"]
TG_TOKEN = os.environ["TELEGRAM_TOKEN"]
TG_CHAT = os.environ["TELEGRAM_CHAT_ID"]
GEMINI_KEY = os.getenv("GEMINI_API_KEY", "")
GEMINI_MODEL = os.getenv("GEMINI_MODEL", "gemini-2.0-flash")
BOOKMAKER = os.getenv("BOOKMAKER", "betclic_fr")
ODDS_REGIONS = os.getenv("ODDS_REGIONS", "fr")

# código football-data.org: (nome, chave The Odds API)
LEAGUES = {
    "PPL": ("Liga Portugal", "soccer_portugal_primeira_liga"),
    "PL": ("Premier League", "soccer_epl"),
    "PD": ("La Liga", "soccer_spain_la_liga"),
    "CL": ("Champions League", "soccer_uefa_champs_league"),
}

HOURS_AHEAD = 48       # jogos nas próximas X horas
FALLBACK_HOURS = 240   # se não houver jogos perto, mostra os próximos (10 dias)
FALLBACK_PER_LEAGUE = 3
MIN_EDGE = 0.05        # vantagem mínima (5%) para sugerir
MAX_EDGE = 0.30        # acima disto desconfia-se do modelo
WARN_EDGE = 0.15       # acima disto avisa que a vantagem parece exagerada
MIN_ODD, MAX_ODD = 1.40, 6.00
MIN_GAMES = 4          # jogos mínimos por equipa para confiar
SHRINK = 3             # "jogos fictícios" na média, evita extremos
MAX_GOALS = 10

# histórico
HIST_DIR = "historico"
PICKS_FILE = f"{HIST_DIR}/sugestoes.csv"
PREDS_FILE = f"{HIST_DIR}/previsoes.csv"
STALE_DAYS = 7         # sem resultado ao fim de X dias -> "sem_resultado"
MATCH_WINDOW_H = 36    # tolerância (horas) ao emparelhar jogo e resultado
MIN_SAMPLE = 100       # abaixo disto o placar ainda não é fiável
PICK_FIELDS = [
    "id", "enviado_em", "liga", "casa", "fora", "fd_casa", "fd_fora", "inicio_utc",
    "sugestao", "selecao", "odd", "prob_modelo", "vantagem", "confianca",
    "casa_apostas", "estado", "golos_casa", "golos_fora", "lucro",
]
PRED_FIELDS = [
    "id", "enviado_em", "liga", "casa", "fora", "fd_casa", "fd_fora", "inicio_utc",
    "pH", "pD", "pA", "pO25", "pBTTS", "xg_casa", "xg_fora", "confianca",
    "estado", "golos_casa", "golos_fora",
]

LISBON = ZoneInfo("Europe/Lisbon")
DIAS = ["Segunda", "Terça", "Quarta", "Quinta", "Sexta", "Sábado", "Domingo"]
DIAS_C = ["Seg", "Ter", "Qua", "Qui", "Sex", "Sáb", "Dom"]
NUMS = ["1️⃣", "2️⃣", "3️⃣", "4️⃣", "5️⃣", "6️⃣"]


def parse_iso(s):
    return dt.datetime.fromisoformat(s.replace("Z", "+00:00"))


# ---------- dados ----------
def fd_matches(code):
    r = requests.get(
        f"https://api.football-data.org/v4/competitions/{code}/matches",
        headers={"X-Auth-Token": FD_KEY},
        params={"status": "FINISHED"},
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


def build_strengths(matches):
    gf, ga, n = {}, {}, {}
    tot_h = tot_a = 0
    for m in matches:
        sc = score90(m)
        if sc is None:
            continue
        sh, sa = sc
        h, a = m["homeTeam"]["name"], m["awayTeam"]["name"]
        for t in (h, a):
            gf.setdefault(t, 0); ga.setdefault(t, 0); n.setdefault(t, 0)
        gf[h] += sh; ga[h] += sa; n[h] += 1
        gf[a] += sa; ga[a] += sh; n[a] += 1
        tot_h += sh; tot_a += sa
    games = sum(n.values()) / 2
    if games < 10:
        return None
    avg_h, avg_a = tot_h / games, tot_a / games
    avg_team = (avg_h + avg_a) / 2
    att, dfn = {}, {}
    for t in n:
        att[t] = ((gf[t] + SHRINK * avg_team) / (n[t] + SHRINK)) / avg_team
        dfn[t] = ((ga[t] + SHRINK * avg_team) / (n[t] + SHRINK)) / avg_team
    return {"att": att, "def": dfn, "n": n, "avg_h": avg_h, "avg_a": avg_a}


def norm(s):
    s = s.lower()
    s = re.sub(r"\b(fc|cf|sc|cd|afc|sad|club|clube|de|futebol|sporting clube)\b", " ", s)
    return re.sub(r"[^a-z0-9 ]", "", s).strip()


def match_team(name, candidates):
    nn = norm(name)
    best, score = None, 0
    for c in candidates:
        cn = norm(c)
        r = difflib.SequenceMatcher(None, nn, cn).ratio()
        if nn in cn or cn in nn:
            r = max(r, 0.85)
        if r > score:
            best, score = c, r
    return best if score >= 0.6 else None


def odds_events(sport):
    r = requests.get(
        f"https://api.the-odds-api.com/v4/sports/{sport}/odds",
        params={
            "apiKey": ODDS_KEY, "regions": ODDS_REGIONS,
            "markets": "h2h,totals", "oddsFormat": "decimal",
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


def pick_book(event):
    books = event.get("bookmakers", [])
    for b in books:
        if b["key"] == BOOKMAKER:
            return b
    return books[0] if books else None


def analyse_event(ev, st):
    home = match_team(ev["home_team"], st["att"].keys())
    away = match_team(ev["away_team"], st["att"].keys())
    book = pick_book(ev)
    if not home or not away or not book:
        return None
    p = predict(st, home, away)
    conf = "alta" if min(st["n"][home], st["n"][away]) >= 10 else (
        "média" if min(st["n"][home], st["n"][away]) >= MIN_GAMES else "baixa")
    picks = []
    for mk in book["markets"]:
        if mk["key"] == "h2h":
            for o in mk["outcomes"]:
                if o["name"] == ev["home_team"]: key, lab = "H", f"Vitória {ev['home_team']}"
                elif o["name"] == ev["away_team"]: key, lab = "A", f"Vitória {ev['away_team']}"
                else: key, lab = "D", "Empate"
                picks.append((lab, p[key], o["price"], key))
        elif mk["key"] == "totals":
            for o in mk["outcomes"]:
                if o.get("point") != 2.5:
                    continue
                over = o["name"] == "Over"
                po = p["O25"] if over else 1 - p["O25"]
                lab = "Mais de 2.5 golos" if over else "Menos de 2.5 golos"
                picks.append((lab, po, o["price"], "O" if over else "U"))
    good = []
    for lab, prob, odd, sel in picks:
        edge = prob * odd - 1
        if MIN_EDGE <= edge <= MAX_EDGE and MIN_ODD <= odd <= MAX_ODD:
            good.append({"label": lab, "prob": prob, "odd": odd, "edge": edge, "sel": sel})
    return {
        "id": ev.get("id") or f"{ev['home_team']}|{ev['away_team']}|{ev['commence_time']}",
        "home": ev["home_team"], "away": ev["away_team"], "time": ev["commence_time"],
        "fd_home": home, "fd_away": away,
        "p": p, "conf": conf, "book": book["title"], "picks": good,
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
    """Índice (casa, fora) -> [(início, golos casa, golos fora)] dos jogos terminados."""
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
    """Marca sugestões/previsões pendentes cujo jogo já terminou. Devolve as sugestões resolvidas agora."""
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
    """Regista previsões (todos os jogos analisados) e sugestões (só as mostradas)."""
    stamp = now.strftime("%Y-%m-%dT%H:%M:%SZ")
    by_id = {r["id"]: r for r in preds}
    for league, games in all_results.items():
        for g in games:
            p = g["p"]
            vals = {
                "pH": f"{p['H']:.4f}", "pD": f"{p['D']:.4f}", "pA": f"{p['A']:.4f}",
                "pO25": f"{p['O25']:.4f}", "pBTTS": f"{p['BTTS']:.4f}",
                "xg_casa": f"{p['lh']:.2f}", "xg_fora": f"{p['la']:.2f}",
                "confianca": g["conf"], "inicio_utc": g["time"],
            }
            old = by_id.get(g["id"])
            if old is None:
                row = {
                    "id": g["id"], "enviado_em": stamp, "liga": league,
                    "casa": g["home"], "fora": g["away"],
                    "fd_casa": g["fd_home"], "fd_fora": g["fd_away"],
                    "estado": "pendente", **vals,
                }
                preds.append(row)
                by_id[g["id"]] = row
            elif old["estado"] == "pendente":
                old.update(vals)  # mantém a previsão mais recente antes do jogo
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
                    "odd": f"{pk['odd']:.2f}", "prob_modelo": f"{pk['prob']:.4f}",
                    "vantagem": f"{pk['edge']:.4f}", "confianca": g["conf"],
                    "casa_apostas": g["book"], "estado": "pendente",
                })
                have.add((g["id"], pk["sel"]))


# ---------- saída (Telegram em HTML) ----------
def esc(s):
    return html.escape(str(s))


def to_lisbon(iso):
    return parse_iso(iso).astimezone(LISBON)


def fmt_time(iso):
    t = to_lisbon(iso)
    return f"{DIAS_C[t.weekday()]} {t:%d/%m} · {t:%H:%M}"


def bar(p, n=10):
    f = round(p * n)
    return "▰" * f + "▱" * (n - f)


def conf_txt(c):
    return {"alta": "🟢 alta", "média": "🟡 média", "baixa": "🔴 baixa"}[c]


def game_block(g):
    p = g["p"]
    return "\n".join([
        f"🕗 <i>{fmt_time(g['time'])}</i>",
        f"<b>{esc(g['home'])}</b> vs <b>{esc(g['away'])}</b>",
        f"{bar(p['H'])} {p['H']:.0%} 🏠 {esc(g['home'])}",
        f"{bar(p['D'])} {p['D']:.0%} 🤝 Empate",
        f"{bar(p['A'])} {p['A']:.0%} ✈️ {esc(g['away'])}",
        f"⚽ Golos esperados: {p['lh']:.1f} – {p['la']:.1f}",
        f"📈 +2.5 golos: {p['O25']:.0%} · Ambas marcam: {p['BTTS']:.0%}",
        f"🔎 Confiança: {conf_txt(g['conf'])}",
    ])


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
    if res:
        n = len(res)
        wins = sum(1 for r in res if r["estado"] == "ganha")
        profit = sum(float(r["lucro"]) for r in res)
        avg_p = sum(float(r["prob_modelo"]) for r in res) / n
        lines += [
            f"🎯 Sugestões resolvidas: {n} · acertou {wins} ({wins / n:.0%})",
            f"💶 Com 1 unidade por sugestão: <b>{profit:+.2f}</b> (ROI {profit / n:+.0%})",
            f"🧮 Probabilidade média do modelo {avg_p:.0%} vs acertos reais {wins / n:.0%}",
        ]
    else:
        lines.append("Ainda sem sugestões resolvidas.")
    if pend:
        lines.append(f"⏳ Por resolver: {len(pend)}")
    if lost:
        lines.append(f"❓ Sem resultado encontrado: {len(lost)} (pode ser nome de equipa por emparelhar)")
    if rp:
        hit = brier = 0.0
        for r in rp:
            ph, pd_, pa = float(r["pH"]), float(r["pD"]), float(r["pA"])
            gh, ga = int(r["golos_casa"]), int(r["golos_fora"])
            yh, yd, ya = float(gh > ga), float(gh == ga), float(gh < ga)
            brier += (ph - yh) ** 2 + (pd_ - yd) ** 2 + (pa - ya) ** 2
            top = max((ph, "H"), (pd_, "D"), (pa, "A"))[1]
            hit += 1.0 if (top == "H" and yh) or (top == "D" and yd) or (top == "A" and ya) else 0.0
        m = len(rp)
        lines.append(
            f"🔮 Previsões 1X2 avaliadas: {m} · resultado mais provável acertou "
            f"{hit / m:.0%} · erro de Brier {brier / m:.3f}"
        )
        lines.append("<i>Brier: quanto mais baixo, melhor (0.667 equivale a chutar).</i>")
    if len(res) < MIN_SAMPLE:
        lines.append(f"⚠️ <i>Amostra pequena ({len(res)}): só é fiável a partir de {MIN_SAMPLE}+ sugestões resolvidas.</i>")
    blocks.append("\n".join(lines))
    return blocks


def build_blocks(results, fallback, extra=None):
    now = dt.datetime.now(LISBON)
    blocks = [
        "⚽ <b>ANÁLISE DO DIA</b>\n"
        f"📅 {DIAS[now.weekday()]}, {now:%d/%m/%Y}\n"
        "━━━━━━━━━━━━━━━"
    ]
    if fallback:
        blocks.append(f"ℹ️ <i>Sem jogos nas próximas {HOURS_AHEAD}h nas ligas seguidas "
                      "(pausa de seleções?). A mostrar os próximos jogos.</i>")
    all_picks, books = [], set()
    for league, games in results.items():
        if not games:
            continue
        blocks.append(f"🏆 <b>{esc(league.upper())}</b>")
        for g in games:
            blocks.append(game_block(g))
            books.add(g["book"])
            for pk in g["picks"]:
                all_picks.append((pk["edge"], g, pk))
    if not any(results.values()):
        blocks.append("Sem jogos analisados nos próximos dias.")
    all_picks.sort(key=lambda x: -x[0])
    head = "🎯 <b>MELHORES OPORTUNIDADES</b>"
    if not all_picks:
        blocks.append(head + "\nNenhuma vantagem clara. Não apostar também é uma decisão. 🧘")
    else:
        lines = [head, ""]
        for i, (edge, g, pk) in enumerate(all_picks[:6]):
            warn = "\n   ⚠️ <i>Vantagem muito alta: desconfia, o modelo pode estar errado.</i>" \
                if edge > WARN_EDGE else ""
            lines.append(
                f"{NUMS[i]} <b>{esc(pk['label'])}</b> @ <b>{pk['odd']:.2f}</b>\n"
                f"   {esc(g['home'])} vs {esc(g['away'])} · {fmt_time(g['time'])}\n"
                f"   📊 Modelo {pk['prob']:.0%} · vantagem <b>{edge:+.0%}</b> · "
                f"{conf_txt(g['conf'])}{warn}"
            )
        blocks.append("\n".join(lines))
    if extra:
        blocks.extend(extra)
    if books:
        blocks.append("📚 Odds: " + esc(", ".join(sorted(books))))
    blocks.append(
        "ℹ️ <i>Vantagem = quanto a odd paga a mais do que o modelo acha justo.</i>\n"
        "⚠️ <i>Estimativa estatística, não garantia. Aposta com responsabilidade.</i>"
    )
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
    r = None
    try:
        r = requests.post(
            f"https://generativelanguage.googleapis.com/v1beta/models/{GEMINI_MODEL}:generateContent",
            params={"key": GEMINI_KEY},
            json={"contents": [{"parts": [{"text": prompt}]}]},
            timeout=60,
        )
        txt = r.json()["candidates"][0]["content"]["parts"][0]["text"].strip()
        return "🧠 <b>RESUMO</b>\n" + esc(txt)
    except Exception as e:  # noqa: BLE001
        print("Gemini falhou:", e, file=sys.stderr)
        if r is not None:
            print("Resposta do Gemini:", r.text[:300], file=sys.stderr)
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
    for c in chunks:
        r = requests.post(
            f"https://api.telegram.org/bot{TG_TOKEN}/sendMessage",
            json={"chat_id": TG_CHAT, "text": c, "parse_mode": "HTML",
                  "disable_web_page_preview": True},
            timeout=30,
        )
        r.raise_for_status()


def main(now=None):
    now = now or dt.datetime.now(dt.timezone.utc)
    near = now + dt.timedelta(hours=HOURS_AHEAD)
    far = now + dt.timedelta(hours=FALLBACK_HOURS)
    results, idx = {}, {}
    for code, (name, sport) in LEAGUES.items():
        try:
            matches = fd_matches(code)
            add_index(idx, matches)
            st = build_strengths(matches)
            if not st:
                print("Poucos dados:", name, file=sys.stderr)
                continue
            games = []
            for ev in odds_events(sport):
                t = parse_iso(ev["commence_time"])
                if not (now <= t <= far):
                    continue
                g = analyse_event(ev, st)
                if g:
                    g["league"] = name
                    games.append(g)
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

    extra = []
    try:  # o histórico nunca pode impedir o envio da mensagem
        picks_h = read_csv(PICKS_FILE)
        preds_h = read_csv(PREDS_FILE)
        newly = settle(picks_h, preds_h, idx, now)
        log_new(picks_h, preds_h, results, shown, now)
        write_csv(PICKS_FILE, PICK_FIELDS, picks_h)
        write_csv(PREDS_FILE, PRED_FIELDS, preds_h)
        extra = history_blocks(picks_h, preds_h, newly)
    except Exception as e:  # noqa: BLE001
        print("Histórico falhou:", e, file=sys.stderr)

    blocks = build_blocks(shown, fallback, extra)
    summary = gemini_summary(plain_text(blocks))
    if summary:
        blocks.insert(len(blocks) - 1, summary)
    telegram(blocks)


if __name__ == "__main__":
    main()
 
