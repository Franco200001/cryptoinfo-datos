"""
Cryptoinfo - noticias que afectan a cripto + avisos al móvil.

Lee titulares recientes de Google News (en español), puntúa cada uno según
lo mucho que puede mover el mercado, estima su impacto en cripto
(alcista / bajista / volatilidad) y:
  - guarda las relevantes en noticias.json, que muestra la web Cryptoinfo
  - envía las más importantes por Telegram (o WhatsApp con CallMeBot)

Variables de entorno (secretos de GitHub):
  TELEGRAM_TOKEN      token del bot que da @BotFather
  TELEGRAM_CHAT_ID    id de tu chat (si falta, se detecta si le has escrito al bot)
  CALLMEBOT_PHONE     opcional, para WhatsApp: tu número con prefijo (+34...)
  CALLMEBOT_APIKEY    opcional, para WhatsApp: la clave que da CallMeBot
  DRY_RUN=1           no envía nada, solo muestra qué enviaría
"""

import email.utils
import hashlib
import html
import json
import os
import re
import sys
import unicodedata
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from datetime import datetime, timedelta, timezone
from zoneinfo import ZoneInfo

WEB = "https://cryptoinfo-es.netlify.app"
HERE = os.path.dirname(os.path.abspath(__file__))
STATE_FILE = os.path.join(HERE, "estado.json")
NEWS_FILE = os.path.join(HERE, "noticias.json")
MADRID = ZoneInfo("Europe/Madrid")

# Ventana de noticias que se consideran "nuevas" para avisar al móvil
MAX_AGE = timedelta(hours=3)
# Ventana y límites de la lista que se muestra en la web
PAGE_AGE = timedelta(hours=24)
PAGE_THRESHOLD = 5
PAGE_MAX = 20
# Límites para no saturar el móvil
MAX_PER_RUN = 2
MAX_PER_DAY = 8
# Puntuación mínima para avisar
THRESHOLD = 6

GN = "https://news.google.com/rss/search?hl=es&gl=ES&ceid=ES:es&q="
FEEDS = [
    GN + urllib.parse.quote('"Reserva Federal" OR Powell OR BCE OR Lagarde OR "tipos de interés" when:1d'),
    GN + urllib.parse.quote('IPC OR inflación OR "datos de empleo" OR nóminas OR recesión mercados when:1d'),
    GN + urllib.parse.quote('bitcoin OR ethereum OR criptomonedas OR cripto when:1d'),
    GN + urllib.parse.quote('SEC OR ETF OR hackeo OR regulación cripto bitcoin when:1d'),
]

# --- Puntuación -------------------------------------------------------------
# Temas que de verdad mueven el mercado (peso alto)
HIGH = {
    "reserva federal": 4, "la fed": 4, "fed ": 3, "powell": 4, "fomc": 4,
    "bce": 3, "lagarde": 3, "banco central": 2,
    "tipos de interes": 4, "sube los tipos": 5, "baja los tipos": 5, "recorte de tipos": 4,
    "subida de tipos": 4, "bajada de tipos": 4,
    " ipc": 4, "inflacion": 3, "nominas": 3, "datos de empleo": 3, "desempleo": 2,
    "recesion": 3, " pib ": 2, "aranceles": 3,
    " sec ": 3, " etf": 3, "regulacion": 2, " mica ": 2, "prohibe": 3, "prohibicion": 3,
    "hackeo": 5, "hackeado": 5, "hack ": 4, "exploit": 4, "robo de": 3,
    "quiebra": 5, "bancarrota": 5, "insolvencia": 4, "colapso": 4,
    "liquidaciones": 3, "desplome": 4, "se desploma": 5, "se hunde": 4, "crash": 4,
    "se dispara": 4, "maximo historico": 5, "record historico": 4, "nuevo maximo": 3,
    "reserva estrategica": 4, "blackrock": 2, "binance": 2, "tether": 2, "stablecoin": 2,
    "halving": 3,
}
# Contexto de mercado (peso bajo)
LOW = {
    "bitcoin": 1, " btc": 1, "ethereum": 1, " eth ": 1, "cripto": 1,
    "wall street": 1, "mercados": 1, " bolsa": 1, "nasdaq": 1, "s&p": 1,
    "dolar": 1, " oro ": 1, "petroleo": 1, " bonos": 1,
}
# Contenido poco útil para un aviso (guías, predicciones, opiniones...)
NOISE = {
    "mejores": -5, "como comprar": -6, "guia": -5, "que es ": -5, "prediccion": -4,
    "podria": -3, "segun un analista": -4, "oportunidad de compra": -4, "wallets": -5,
    "precio, noticias": -8, "en vivo": -4, "tutorial": -6, "curso": -6, "opinion": -3,
    "patrocinado": -10, "cotizacion hoy": -4, "horoscopo": -10,
}
# Medios de referencia (pequeño extra de fiabilidad)
TRUSTED = (
    "el pais", "expansion", "el economista", "cinco dias", "europa press", "efe",
    "reuters", "bloomberg", "coindesk", "cointelegraph", "investing", "fxstreet",
    "la vanguardia", "el confidencial", "rtve", "abc", "el mundo", "bolsamania",
    "beincrypto", "criptonoticias", "infobae", "xtb",
)

TAGS = [
    ("🏦 Bancos centrales", ("reserva federal", "la fed", "fed ", "powell", "fomc", "bce", "lagarde", "tipos de interes", "banco central")),
    ("📊 Datos macro", (" ipc", "inflacion", "nominas", "empleo", " pib ", "recesion")),
    ("⚖️ Regulación", (" sec ", " etf", "regulacion", " mica ", "prohib")),
    ("🔓 Seguridad", ("hack", "exploit", "robo de")),
    ("💥 Movimiento fuerte", ("desplom", "se hunde", "crash", "se dispara", "maximo historico", "record", "liquidaciones", "colapso")),
    ("🌍 Geopolítica", ("aranceles", "guerra", "sanciones")),
]


# --- Impacto en cripto -------------------------------------------------------
# (dirección, motivo, condición). Gana la primera regla que encaja.
def _has(t, *keys):
    return any(k in t for k in keys)


IMPACT_RULES = [
    ("bajista", "Un hackeo resta confianza y suele provocar ventas en el token afectado y en el sector.",
     lambda t: _has(t, "hack", "exploit", "robo de", "robados")),
    ("bajista", "Una quiebra genera contagio y miedo en todo el mercado cripto.",
     lambda t: _has(t, "quiebra", "bancarrota", "insolvencia", "colapso")),
    ("bajista", "Tipos más altos encarecen el dinero y restan atractivo a activos de riesgo como BTC.",
     lambda t: _has(t, "sube los tipos", "subida de tipos", "subir tipos", "subir los tipos", "alza de tipos",
                    "aumento de tasas", "subida de tasas", "subir tasas", "endurec", "halcon")),
    ("alcista", "Tipos más bajos abaratan el dinero y suelen favorecer a cripto.",
     lambda t: _has(t, "recorte de tipos", "baja los tipos", "bajada de tipos", "recorta los tipos", "rebaja de tipos",
                    "bajar tipos", "bajada de tasas", "recorte de tasas", "recorta tasas", "paloma")),
    ("alcista", "Una inflación más baja acerca las bajadas de tipos: buena señal para cripto.",
     lambda t: _has(t, "inflacion", " ipc", " cpi") and
               _has(t, "se modera", "modera", "cede", "baja ", "desacelera", "menor de lo esperado", "por debajo", "se enfria")),
    ("bajista", "Una inflación alta aleja las bajadas de tipos y presiona a cripto.",
     lambda t: (_has(t, "inflacion", " ipc", " cpi")) and
               _has(t, "al alza", "sube", "supera", "alta", "repunta", "sorprende", "acelera", "por encima")),
    ("alcista", "Los ETF canalizan dinero institucional hacia cripto.",
     lambda t: " etf" in t and _has(t, "aprueba", "aprobacion", "entradas", "lanza", "record", "luz verde")),
    ("bajista", "Salidas de dinero de los ETF indican que los grandes inversores están vendiendo.",
     lambda t: " etf" in t and _has(t, "salidas", "retiran", "rechaza")),
    ("alcista", "Compras de grandes inversores o gobiernos aumentan la demanda.",
     lambda t: _has(t, "reserva estrategica", "compra bitcoin", "compra de bitcoin", "compra mas bitcoin", "acumula",
                    "adopcion", "adopta", "invierte en bitcoin", "blackrock compra")),
    ("bajista", "Más presión regulatoria suele asustar al mercado cripto.",
     lambda t: _has(t, "prohib", "demanda a", "demanda contra", "multa", "investiga", "restriccion", "veta")),
    ("alcista", "Reglas claras dan seguridad a los inversores y atraen capital.",
     lambda t: _has(t, "regulacion", " mica ", " ley ") and _has(t, "aprueba", "claridad", "luz verde", "favorable")),
    ("bajista", "Las tensiones comerciales y geopolíticas aumentan la aversión al riesgo.",
     lambda t: _has(t, "aranceles", "guerra comercial", "sanciones", "conflicto", "guerra ")),
    ("bajista", "Las caídas fuertes provocan liquidaciones en cadena y más volatilidad.",
     lambda t: _has(t, "se desploma", "desplome", "se hunde", "crash", "liquidaciones", "cae ", "caida", "pierde", "retrocede")),
    ("alcista", "El impulso alcista atrae nuevos compradores al mercado.",
     lambda t: _has(t, "maximo historico", "record", "se dispara", "sube ", "repunta", "rally", "escala", "avanza")),
    ("volatilidad", "Dato o decisión clave: suele traer movimientos bruscos en BTC y ETH.",
     lambda t: _has(t, "fed ", "la fed", "reserva federal", "powell", "bce", "lagarde", " ipc", "inflacion",
                    "nominas", "empleo", "fomc", " pib ")),
]


def impact(title, s):
    t = norm(title)
    for direction, reason, cond in IMPACT_RULES:
        try:
            if cond(t):
                break
        except Exception:
            continue
    else:
        direction, reason = "volatilidad", "Noticia relevante para el mercado: atención a posibles movimientos."
    return {"impacto": direction, "motivo": reason, "nivel": "alto" if s >= 9 else "medio"}


def norm(text):
    text = unicodedata.normalize("NFKD", text.lower())
    text = "".join(c for c in text if not unicodedata.combining(c))
    return " " + re.sub(r"\s+", " ", text) + " "


def score(title, source):
    t = norm(title)
    high = sum(w for k, w in HIGH.items() if k in t)
    s = high + sum(w for k, w in LOW.items() if k in t) + sum(w for k, w in NOISE.items() if k in t)
    if any(m in norm(source) for m in TRUSTED):
        s += 1
    return s, high


def tags_for(title):
    t = norm(title)
    return [name for name, keys in TAGS if any(k in t for k in keys)]


def words(title):
    stop = {"de", "la", "el", "en", "y", "a", "los", "las", "del", "por", "que", "se", "un", "una",
            "con", "para", "al", "su", "lo", "es", "eeuu", "ee", "uu", "tras", "como", "mas"}
    return {w for w in re.findall(r"[a-z0-9]+", norm(title)) if len(w) > 2 and w not in stop}


def similar(a, b):
    wa, wb = words(a), words(b)
    if not wa or not wb:
        return False
    return len(wa & wb) / min(len(wa), len(wb)) >= 0.5


# --- Lectura de noticias ----------------------------------------------------
def fetch(url):
    req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0 (cryptoinfo-avisos)"})
    with urllib.request.urlopen(req, timeout=25) as r:
        return r.read()


def read_news():
    now = datetime.now(timezone.utc)
    items, seen_titles = [], set()
    for url in FEEDS:
        try:
            root = ET.fromstring(fetch(url))
        except Exception as e:
            print(f"Aviso: no se pudo leer una fuente ({e})", file=sys.stderr)
            continue
        for it in root.iter("item"):
            raw = (it.findtext("title") or "").strip()
            link = (it.findtext("link") or "").strip()
            source = (it.findtext("source") or "").strip()
            try:
                pub = email.utils.parsedate_to_datetime(it.findtext("pubDate"))
            except Exception:
                continue
            if now - pub > PAGE_AGE:
                continue
            # Google News añade " - Medio" al final del título
            title = raw
            if source and raw.endswith(" - " + source):
                title = raw[: -len(source) - 3].strip()
            key = norm(title)
            if not title or key in seen_titles:
                continue
            seen_titles.add(key)
            s, high = score(title, source)
            items.append({"title": title, "link": link, "source": source, "pub": pub,
                          "score": s, "high": high, **impact(title, s),
                          "id": hashlib.sha1(key.encode()).hexdigest()[:16]})
    items.sort(key=lambda x: (x["score"], x["pub"]), reverse=True)
    return items


# --- Estado (qué se ha enviado ya) -------------------------------------------
def load_state():
    try:
        with open(STATE_FILE, encoding="utf-8") as f:
            return json.load(f)
    except FileNotFoundError:
        return {"sent": [], "chat_id": None}


def save_state(state):
    cutoff = (datetime.now(timezone.utc) - timedelta(days=3)).isoformat()
    state["sent"] = [s for s in state["sent"] if s["ts"] >= cutoff]
    state.pop("chat_id", None)  # el repositorio es público: nunca se guarda el chat
    with open(STATE_FILE, "w", encoding="utf-8") as f:
        json.dump(state, f, ensure_ascii=False, indent=1)


# --- Envío ------------------------------------------------------------------
def telegram(method, **params):
    token = os.environ["TELEGRAM_TOKEN"].strip()
    data = urllib.parse.urlencode(params).encode()
    req = urllib.request.Request(f"https://api.telegram.org/bot{token}/{method}", data=data)
    with urllib.request.urlopen(req, timeout=25) as r:
        return json.load(r)


def telegram_chat_id(state):
    cid = os.environ.get("TELEGRAM_CHAT_ID", "").strip() or state.get("chat_id")
    if cid:
        return cid
    res = telegram("getUpdates")
    for upd in reversed(res.get("result", [])):
        msg = upd.get("message") or upd.get("my_chat_member") or {}
        chat = msg.get("chat")
        if chat:
            return str(chat["id"])
    return None


def format_message(item):
    hora = item["pub"].astimezone(MADRID).strftime("%H:%M")
    tags = " · ".join(tags_for(item["title"]))
    lines = ["🚨 <b>Noticia importante</b>", "", f"<b>{html.escape(item['title'])}</b>"]
    meta = f"📰 {html.escape(item['source'] or 'Google News')} · {hora}"
    lines.append(meta)
    if tags:
        lines.append(tags)
    arrow = {"alcista": "🟢 Posible impacto alcista", "bajista": "🔴 Posible impacto bajista",
             "volatilidad": "🟡 Posible volatilidad"}[item["impacto"]]
    lines += ["", f"<b>{arrow} en cripto</b>", html.escape(item["motivo"])]
    lines += ["", f'<a href="{html.escape(item["link"])}">Leer la noticia</a> · <a href="{WEB}#noticias">Ver en Cryptoinfo</a>']
    return "\n".join(lines)


def send(text_html, state):
    if os.environ.get("DRY_RUN"):
        print("---- (prueba, no se envía) ----\n" + text_html + "\n")
        return True
    ok = False
    if os.environ.get("TELEGRAM_TOKEN", "").strip():
        cid = telegram_chat_id(state)
        if not cid:
            print("ERROR: no encuentro tu chat. Abre tu bot en Telegram y pulsa Iniciar (/start).", file=sys.stderr)
        else:
            res = telegram("sendMessage", chat_id=cid, text=text_html, parse_mode="HTML",
                           disable_web_page_preview="true")
            ok = res.get("ok", False)
    if os.environ.get("CALLMEBOT_APIKEY", "").strip():
        plain = re.sub(r"<a href=\"([^\"]+)\">([^<]+)</a>", r"\2: \1", text_html)
        plain = re.sub(r"</?b>", "*", plain)
        plain = html.unescape(re.sub(r"<[^>]+>", "", plain))
        q = urllib.parse.urlencode({"phone": os.environ["CALLMEBOT_PHONE"].strip(),
                                    "text": plain, "apikey": os.environ["CALLMEBOT_APIKEY"].strip()})
        fetch("https://api.callmebot.com/whatsapp.php?" + q)
        ok = True
    return ok


def write_page_news(items, now):
    """Guarda en noticias.json las noticias relevantes de las últimas 24 h para la web."""
    chosen = []
    for it in items:  # ya vienen ordenadas por puntuación
        if it["score"] < PAGE_THRESHOLD or it["high"] < 3:
            continue
        if any(similar(it["title"], c["title"]) for c in chosen):
            continue
        chosen.append(it)
        if len(chosen) >= PAGE_MAX:
            break
    chosen.sort(key=lambda x: x["pub"], reverse=True)
    news = [{
        "titulo": it["title"], "enlace": it["link"], "medio": it["source"] or "Google News",
        "fecha": it["pub"].astimezone(timezone.utc).isoformat(timespec="seconds"),
        "impacto": it["impacto"], "motivo": it["motivo"], "nivel": it["nivel"],
        "temas": tags_for(it["title"]),
    } for it in chosen]

    try:
        with open(NEWS_FILE, encoding="utf-8") as f:
            old = json.load(f).get("noticias")
    except (FileNotFoundError, ValueError):
        old = None
    if news == old:
        print("noticias.json sin cambios.")
        return
    with open(NEWS_FILE, "w", encoding="utf-8") as f:
        json.dump({"actualizado": now.isoformat(timespec="seconds"), "noticias": news},
                  f, ensure_ascii=False, indent=1)
    print(f"noticias.json actualizado con {len(news)} noticias.")


def main():
    state = load_state()
    first_run = not state.get("started")
    items = read_news()
    now = datetime.now(timezone.utc)

    print(f"{len(items)} titulares de las últimas 24 h. Los mejor puntuados:")
    for it in items[:10]:
        print(f"  [{it['score']:>3}] {it['impacto']:<11} {it['title'][:90]} ({it['source']})")

    # 1) Lista para la web (se guarda antes de enviar nada, para que no dependa de Telegram)
    write_page_news(items, now)

    if first_run:
        welcome = ("✅ <b>Avisos de Cryptoinfo activados</b>\n\n"
                   "Te escribiré aquí cuando salga una noticia que pueda mover el mercado: "
                   "Fed y BCE, inflación, regulación, hackeos, caídas o subidas fuertes...\n\n"
                   f'<a href="{WEB}">Abrir Cryptoinfo</a>')
        if not send(welcome, state):
            sys.exit(1)
        state["started"] = now.isoformat()

    sent_today = [s for s in state["sent"] if s["ts"] >= (now - timedelta(hours=24)).isoformat()]
    budget = min(MAX_PER_RUN, MAX_PER_DAY - len(sent_today))
    sent_ids = {s["id"] for s in state["sent"]}
    recent_titles = [s["title"] for s in state["sent"]]

    chosen = []
    for it in items:
        if budget <= 0:
            break
        if it["score"] < THRESHOLD or it["high"] < 3 or it["id"] in sent_ids:
            continue
        if now - it["pub"] > MAX_AGE:  # al móvil solo lo reciente
            continue
        # Evita repetir la misma noticia contada por otro medio
        if any(similar(it["title"], t) for t in recent_titles + [c["title"] for c in chosen]):
            continue
        chosen.append(it)
        budget -= 1

    for it in chosen:
        if send(format_message(it), state):
            state["sent"].append({"id": it["id"], "title": it["title"], "ts": now.isoformat()})
            print(f"Enviado: {it['title']}")

    if not chosen:
        print("Nada nuevo lo bastante importante.")
    if not os.environ.get("DRY_RUN"):
        save_state(state)


if __name__ == "__main__":
    main()
