# Analista de futebol no Telegram (grátis)

## 1. Criar as contas e chaves (todas grátis)
1. **Telegram**: fala com @BotFather, `/newbot`, guarda o TOKEN. Envia uma mensagem ao teu bot e abre
   `https://api.telegram.org/bot<TOKEN>/getUpdates` para ver o teu `chat.id`.
2. **football-data.org**: regista-te e copia a API key.
3. **the-odds-api.com**: regista-te e copia a API key (plano grátis ~500 créditos/mês).
4. **(Opcional) Gemini**: chave em aistudio.google.com para o resumo em texto.

## 2. GitHub
1. Cria um repositório **privado**.
2. Põe lá `bot.py` e `requirements.txt`, e o `daily.yml` em `.github/workflows/daily.yml`.
3. Settings > Secrets and variables > Actions > New secret, com os nomes:
   `FOOTBALL_DATA_KEY`, `ODDS_API_KEY`, `TELEGRAM_TOKEN`, `TELEGRAM_CHAT_ID`, `GEMINI_API_KEY` (opcional).
4. Separador Actions > "analista-futebol" > Run workflow para testar.

## 3. Notas
- Cada liga gasta 2 créditos de odds por execução (h2h + totais). 4 ligas x 30 dias = 240/mês.
  Se juntares ligas, vigia o limite.
- Se a Betclic não aparecer nas odds, o bot usa o primeiro bookmaker disponível e diz qual.
  Podes mudar a variável `BOOKMAKER` ou `ODDS_REGIONS` em `bot.py`.
- Para mais ligas: acrescenta em `LEAGUES` (código football-data + chave da Odds API).
  O plano grátis do football-data só cobre algumas competições.
- Cantos: não incluídos (as APIs grátis não dão odds nem dados fiáveis de cantos).
