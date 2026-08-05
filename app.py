import json
import os
import re
import threading
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
    return "국내" if symbol.endswith((".KS", ".KQ")) else "해외"


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
    candidates = []

    if re.fullmatch(r"\d{6}", query):
        for suffix in (".KS", ".KQ"):
            symbol = query + suffix
            try:
                meta = fetch_chart_meta(symbol)
            except requests.RequestException:
                meta = None
            if meta and meta.get("regularMarketPrice") is not None:
                candidates.append(
                    {
                        "symbol": symbol,
                        "name": meta.get("longName") or meta.get("shortName") or symbol,
                        "exchange": meta.get("fullExchangeName") or "KRX",
                        "type": "ETF",
                        "market": "국내",
                    }
                )

    try:
        search_results = yahoo_search(query)
    except requests.RequestException:
        search_results = []

    etf_first = [c for c in search_results if c["type"] == "ETF"]
    others = [c for c in search_results if c["type"] != "ETF"]
    existing_symbols = {c["symbol"] for c in candidates}
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
