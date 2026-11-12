"""Analista diário de futebol -> Telegram.
 
Fluxo: resultados da época (football-data.org) -> modelo de Poisson ->
probabilidades 1X2 / Over-Under 2.5 / BTTS -> compara com odds (The Odds API,
Betclic se disponível) -> envia as melhores "value bets" por Telegram.
"""
import os
import re
import sys
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
 
LISBON = ZoneInfo("Europe/Lisbon")
DIAS = ["Segunda", "Terça", "Quarta", "Quinta", "Sexta", "Sábado", "Domingo"]
DIAS_C = ["Seg", "Ter", "Qua", "Qui", "Sex", "Sáb", "Dom"]
NUMS = ["1️⃣", "2️⃣", "3️⃣", "4️⃣", "5️⃣", "6️⃣"]
 
 
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
 
 
def build_strengths(matches):
    gf, ga, n = {}, {}, {}
    tot_h = tot_a = 0
    for m in matches:
        s = m["score"]["fullTime"]
        if s["home"] is None or s["away"] is None:
            continue
        h, a = m["homeTeam"]["name"], m["awayTeam"]["name"]
        for t in (h, a):
            gf.setdefault(t, 0); ga.setdefault(t, 0); n.setdefault(t, 0)
        gf[h] += s["home"]; ga[h] += s["away"]; n[h] += 1
        gf[a] += s["away"]; ga[a] += s["home"]; n[a] += 1
        tot_h += s["home"]; tot_a += s["away"]
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
                picks.append((lab, p[key], o["price"]))
        elif mk["key"] == "totals":
            for o in mk["outcomes"]:
                if o.get("point") != 2.5:
                    continue
                po = p["O25"] if o["name"] == "Over" else 1 - p["O25"]
                lab = "Mais de 2.5 golos" if o["name"] == "Over" else "Menos de 2.5 golos"
                picks.append((lab, po, o["price"]))
    good = []
    for lab, prob, odd in picks:
        edge = prob * odd - 1
        if MIN_EDGE <= edge <= MAX_EDGE and MIN_ODD <= odd <= MAX_ODD:
            good.append({"label": lab, "prob": prob, "odd": odd, "edge": edge})
    return {
        "home": ev["home_team"], "away": ev["away_team"], "time": ev["commence_time"],
        "p": p, "conf": conf, "book": book["title"], "picks": good,
    }
 
 
# ---------- saída (Telegram em HTML) ----------
def esc(s):
    return html.escape(str(s))
 
 
def to_lisbon(iso):
    return dt.datetime.fromisoformat(iso.replace("Z", "+00:00")).astimezone(LISBON)
 
 
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
 
 
def build_blocks(results, fallback):
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
        try:
            print("Resposta do Gemini:", r.text[:300], file=sys.stderr)
        except Exception:  # noqa: BLE001
            pass
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
 
 
def main():
    now = dt.datetime.now(dt.timezone.utc)
    near = now + dt.timedelta(hours=HOURS_AHEAD)
    far = now + dt.timedelta(hours=FALLBACK_HOURS)
    results = {}
    for code, (name, sport) in LEAGUES.items():
        try:
            st = build_strengths(fd_matches(code))
            if not st:
                print("Poucos dados:", name, file=sys.stderr)
                continue
            games = []
            for ev in odds_events(sport):
                t = dt.datetime.fromisoformat(ev["commence_time"].replace("Z", "+00:00"))
                if not (now <= t <= far):
                    continue
                g = analyse_event(ev, st)
                if g:
                    games.append(g)
            games.sort(key=lambda g: g["time"])
            results[name] = games
        except Exception as e:  # noqa: BLE001
            print("Erro em", name, e, file=sys.stderr)
 
    def is_near(g):
        return dt.datetime.fromisoformat(g["time"].replace("Z", "+00:00")) <= near
 
    near_res = {n: [g for g in gs if is_near(g)] for n, gs in results.items()}
    fallback = not any(near_res.values())
    if fallback:
        shown = {n: gs[:FALLBACK_PER_LEAGUE] for n, gs in results.items()}
    else:
        shown = near_res
    blocks = build_blocks(shown, fallback)
    summary = gemini_summary(plain_text(blocks))
    if summary:
        blocks.insert(len(blocks) - 1, summary)
    telegram(blocks)
 
 
if __name__ == "__main__":
    main()
 
