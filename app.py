import json
import os
import re
import threading
import time
from datetime import datetime

import requests
from flask import Flask, jsonify, request, send_from_directory

app = Flask(__name__, static_folder=".", static_url_path="")

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
DATA_DIR = os.path.join(BASE_DIR, "data")
SAVED_PATH = os.path.join(DATA_DIR, "saved_etfs.json")

HEADERS = {"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36"}

# Yahoo Finance's quoteSummary endpoint requires a session cookie + crumb
# token. We fetch it lazily and cache it; on 401/429 we drop the cache and
# re-negotiate on the next request.
_session = None
_crumb = None
_session_lock = threading.Lock()


def get_session_and_crumb():
    global _session, _crumb
    with _session_lock:
        if _session is not None and _crumb is not None:
            return _session, _crumb
        s = requests.Session()
        s.headers.update(HEADERS)
        try:
            s.get("https://fc.yahoo.com", timeout=8)
        except requests.RequestException:
            pass
        r = s.get("https://query1.finance.yahoo.com/v1/test/getcrumb", timeout=8)
        r.raise_for_status()
        crumb = r.text.strip()
        _session, _crumb = s, crumb
        return s, crumb


def reset_session():
    global _session, _crumb
    with _session_lock:
        _session, _crumb = None, None


def raw(container, key):
    value = (container or {}).get(key)
    if isinstance(value, dict):
        return value.get("raw")
    return value


def load_saved():
    if not os.path.exists(SAVED_PATH):
        return []
    with open(SAVED_PATH, "r", encoding="utf-8") as f:
        return json.load(f)


def write_saved(items):
    os.makedirs(DATA_DIR, exist_ok=True)
    with open(SAVED_PATH, "w", encoding="utf-8") as f:
        json.dump(items, f, ensure_ascii=False, indent=2)


def market_of(symbol):
    return "국내" if re.fullmatch(r"\d{6}", symbol) or symbol.endswith((".KS", ".KQ")) else "해외"


def num(value):
    """Parse a comma-formatted numeric string ("13,660,080") into a float."""
    if value is None:
        return None
    try:
        return float(str(value).replace(",", "").replace("원", "").strip())
    except ValueError:
        return None


def parse_krw(value):
    """Parse Korean-unit money strings like "24조 4,433억" into a won amount."""
    if not value:
        return None
    s = str(value).replace(",", "")
    total = 0.0
    matched = False
    for unit, mult in (("조", 1e12), ("억", 1e8), ("만", 1e4)):
        m = re.search(rf"(-?\d+(?:\.\d+)?){unit}", s)
        if m:
            total += float(m.group(1)) * mult
            s = s[: m.start()] + s[m.end() :]
            matched = True
    remainder = re.search(r"-?\d+(?:\.\d+)?", s)
    if remainder:
        total += float(remainder.group(0))
        matched = True
    return total if matched else None


# Full KRX-listed ETF universe, sourced from Naver Finance (which mirrors
# official KRX data). Cached in memory since it's ~1000+ rows and rarely
# changes within a session; used to power accurate Korean-name/code search
# and as a quick lookup for the domestic quote endpoint.
_krx_list_cache = {"items": None, "fetched_at": 0}
_KRX_LIST_TTL_SECONDS = 600


def fetch_krx_etf_list():
    now = time.time()
    cache = _krx_list_cache
    if cache["items"] is not None and now - cache["fetched_at"] < _KRX_LIST_TTL_SECONDS:
        return cache["items"]
    url = "https://finance.naver.com/api/sise/etfItemList.nhn"
    r = requests.get(url, headers=HEADERS, timeout=10)
    r.raise_for_status()
    data = json.loads(r.content.decode("cp949", errors="replace"))
    items = data.get("result", {}).get("etfItemList", [])
    cache["items"] = items
    cache["fetched_at"] = now
    return items


def search_krx_etfs(query):
    query = query.strip().lower()
    if not query:
        return []
    try:
        items = fetch_krx_etf_list()
    except requests.RequestException:
        return []
    exact, prefix, contains = [], [], []
    for it in items:
        code = it.get("itemcode", "")
        name = (it.get("itemname") or "")
        name_lower = name.lower()
        candidate = {
            "symbol": code,
            "name": name,
            "exchange": "KRX",
            "type": "ETF",
            "market": "국내",
        }
        if query == code or query == name_lower:
            exact.append(candidate)
        elif code.startswith(query) or name_lower.startswith(query):
            prefix.append(candidate)
        elif query in name_lower:
            contains.append(candidate)
    return (exact + prefix + contains)[:8]


def fetch_domestic_quote(code):
    listing = None
    try:
        listing = next((it for it in fetch_krx_etf_list() if it.get("itemcode") == code), None)
    except requests.RequestException:
        listing = None

    detail = {}
    try:
        r = requests.get(
            f"https://m.stock.naver.com/api/stock/{code}/integration", headers=HEADERS, timeout=8
        )
        if r.status_code == 200:
            detail = r.json()
    except requests.RequestException:
        detail = {}

    name = (listing or {}).get("itemname") or detail.get("stockName")
    if not name:
        return {"symbol": code, "hasData": False}

    total_map = {i["code"]: i.get("value") for i in detail.get("totalInfos", []) if "code" in i}
    key_ind = detail.get("etfKeyIndicator") or {}

    price = num((listing or {}).get("nowVal")) or num(total_map.get("lastClosePrice"))
    prev_close = num(total_map.get("lastClosePrice"))
    change = price - prev_close if price is not None and prev_close is not None else None
    change_pct = (change / prev_close * 100) if change and prev_close else None

    expense_ratio = key_ind.get("totalFee")
    dividend_yield = key_ind.get("dividendYieldTtm")

    return {
        "symbol": code,
        "name": name,
        "market": "국내",
        "currency": "KRW",
        "price": price,
        "change": change,
        "changePercent": change_pct,
        "previousClose": prev_close,
        "dayHigh": num(total_map.get("highPrice")),
        "dayLow": num(total_map.get("lowPrice")),
        "fiftyTwoWeekHigh": num(total_map.get("highPriceOf52WeeksAdjusted") or total_map.get("highPriceOf52Weeks")),
        "fiftyTwoWeekLow": num(total_map.get("lowPriceOf52WeeksAdjusted") or total_map.get("lowPriceOf52Weeks")),
        "volume": num(total_map.get("accumulatedTradingVolume")),
        "totalAssets": parse_krw(key_ind.get("totalNav")),
        "expenseRatio": (expense_ratio / 100) if expense_ratio is not None else None,
        "category": None,
        "fundFamily": key_ind.get("issuerName"),
        "exchange": "KRX",
        "yield": (dividend_yield / 100) if dividend_yield is not None else None,
        "inceptionDate": None,
        "hasData": price is not None,
        "updatedAt": datetime.now().isoformat(),
    }


def yahoo_search(query):
    url = "https://query2.finance.yahoo.com/v1/finance/search"
    params = {"q": query, "quotesCount": 8, "newsCount": 0, "lang": "ko-KR"}
    r = requests.get(url, params=params, headers=HEADERS, timeout=8)
    r.raise_for_status()
    quotes = r.json().get("quotes", [])
    results = []
    for q in quotes:
        symbol = q.get("symbol")
        if not symbol:
            continue
        results.append(
            {
                "symbol": symbol,
                "name": q.get("shortname") or q.get("longname") or symbol,
                "exchange": q.get("exchDisp", ""),
                "type": q.get("quoteType", ""),
                "market": market_of(symbol),
            }
        )
    return results


def resolve_candidates(query):
    query = query.strip()
    candidates = list(search_krx_etfs(query))
    existing_symbols = {c["symbol"] for c in candidates}

    try:
        search_results = yahoo_search(query)
    except requests.RequestException:
        search_results = []

    etf_first = [c for c in search_results if c["type"] == "ETF"]
    others = [c for c in search_results if c["type"] != "ETF"]
    for c in etf_first + others:
        if c["symbol"] not in existing_symbols:
            candidates.append(c)
            existing_symbols.add(c["symbol"])

    return candidates


def fetch_chart_meta(symbol):
    url = f"https://query1.finance.yahoo.com/v8/finance/chart/{symbol}"
    r = requests.get(url, headers=HEADERS, timeout=8)
    if r.status_code == 404:
        return None
    r.raise_for_status()
    result = r.json().get("chart", {}).get("result")
    if not result:
        return None
    return result[0].get("meta", {})


def fetch_fund_detail(symbol):
    """Best-effort fetch of fund-profile fields. Yahoo doesn't have this
    data for every ticker (notably many KRX-listed ETFs), so callers must
    tolerate an empty dict."""
    modules = "summaryDetail,defaultKeyStatistics,fundProfile"
    for attempt in range(2):
        try:
            session, crumb = get_session_and_crumb()
            url = f"https://query1.finance.yahoo.com/v10/finance/quoteSummary/{symbol}"
            r = session.get(url, params={"modules": modules, "crumb": crumb}, timeout=8)
            if r.status_code in (401, 429):
                reset_session()
                continue
            r.raise_for_status()
            result = r.json().get("quoteSummary", {}).get("result")
            return result[0] if result else {}
        except requests.RequestException:
            reset_session()
    return {}


def fetch_quote(symbol):
    if re.fullmatch(r"\d{6}", symbol):
        return fetch_domestic_quote(symbol)
    if symbol.endswith((".KS", ".KQ")):
        return fetch_domestic_quote(symbol[:-3])

    meta = fetch_chart_meta(symbol)
    if not meta or meta.get("regularMarketPrice") is None:
        return {"symbol": symbol, "hasData": False}

    detail = fetch_fund_detail(symbol)
    summary_detail = detail.get("summaryDetail") or {}
    fund_profile = detail.get("fundProfile") or {}
    key_stats = detail.get("defaultKeyStatistics") or {}
    fees = fund_profile.get("feesExpensesInvestment") or {}

    price = meta.get("regularMarketPrice")
    prev_close = meta.get("previousClose") or meta.get("chartPreviousClose")
    change = price - prev_close if prev_close is not None else None
    change_pct = (change / prev_close * 100) if change is not None and prev_close else None

    return {
        "symbol": symbol,
        "name": meta.get("longName") or meta.get("shortName") or symbol,
        "market": market_of(symbol),
        "currency": meta.get("currency", ""),
        "price": price,
        "change": change,
        "changePercent": change_pct,
        "previousClose": prev_close,
        "dayHigh": meta.get("regularMarketDayHigh"),
        "dayLow": meta.get("regularMarketDayLow"),
        "fiftyTwoWeekHigh": meta.get("fiftyTwoWeekHigh"),
        "fiftyTwoWeekLow": meta.get("fiftyTwoWeekLow"),
        "volume": meta.get("regularMarketVolume"),
        "totalAssets": raw(summary_detail, "totalAssets"),
        "expenseRatio": raw(fees, "annualReportExpenseRatio"),
        "category": fund_profile.get("categoryName"),
        "fundFamily": fund_profile.get("family"),
        "exchange": meta.get("fullExchangeName") or meta.get("exchangeName"),
        "yield": raw(summary_detail, "yield"),
        "inceptionDate": raw(key_stats, "fundInceptionDate"),
        "hasData": True,
        "updatedAt": datetime.now().isoformat(),
    }


@app.route("/")
def index():
    return send_from_directory(BASE_DIR, "index.html")


@app.route("/api/search")
def api_search():
    q = request.args.get("q", "")
    if not q.strip():
        return jsonify({"error": "검색어를 입력해주세요."}), 400
    candidates = resolve_candidates(q)
    return jsonify({"results": candidates})


@app.route("/api/quote/<path:symbol>")
def api_quote(symbol):
    try:
        data = fetch_quote(symbol)
    except Exception as e:
        return jsonify({"error": f"조회 중 오류가 발생했습니다: {e}"}), 502
    return jsonify(data)


@app.route("/api/saved", methods=["GET"])
def api_saved_list():
    return jsonify(load_saved())


@app.route("/api/saved", methods=["POST"])
def api_saved_add():
    body = request.get_json(force=True, silent=True) or {}
    symbol = body.get("symbol")
    if not symbol:
        return jsonify({"error": "symbol이 필요합니다."}), 400
    items = load_saved()
    if not any(i["symbol"] == symbol for i in items):
        items.append(
            {
                "symbol": symbol,
                "name": body.get("name", symbol),
                "market": body.get("market", market_of(symbol)),
                "addedAt": datetime.now().isoformat(),
            }
        )
        write_saved(items)
    return jsonify(items)


@app.route("/api/saved/<path:symbol>", methods=["DELETE"])
def api_saved_remove(symbol):
    items = [i for i in load_saved() if i["symbol"] != symbol]
    write_saved(items)
    return jsonify(items)


if __name__ == "__main__":
    port = int(os.environ.get("PORT", 5057))
    debug = os.environ.get("FLASK_DEBUG") == "1"
    app.run(debug=debug, host="0.0.0.0", port=port)
