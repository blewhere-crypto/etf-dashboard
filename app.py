import json
import os
import re
import statistics
import threading
import time
from datetime import datetime, timedelta

import truststore

truststore.inject_into_ssl()  # trust the OS certificate store (like curl), not just certifi's bundle

import requests
import urllib3
from flask import Flask, jsonify, request, send_from_directory

urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)

app = Flask(__name__, static_folder=".", static_url_path="")

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
DATA_DIR = os.path.join(BASE_DIR, "data")
SAVED_PATH = os.path.join(DATA_DIR, "saved_etfs.json")
HISTORY_PATH = os.path.join(DATA_DIR, "search_history.json")
HISTORY_LIMIT = 30

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


def load_history():
    if not os.path.exists(HISTORY_PATH):
        return []
    with open(HISTORY_PATH, "r", encoding="utf-8") as f:
        return json.load(f)


def write_history(items):
    os.makedirs(DATA_DIR, exist_ok=True)
    with open(HISTORY_PATH, "w", encoding="utf-8") as f:
        json.dump(items, f, ensure_ascii=False, indent=2)


def market_of(symbol):
    return "국내" if resolve_krx_code(symbol) else "해외"


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
    query_norm = _compact(query.strip().lower())
    if not query_norm:
        return []
    try:
        items = fetch_krx_etf_list()
    except requests.RequestException:
        return []
    exact, prefix, contains = [], [], []
    for it in items:
        code = it.get("itemcode", "")
        code_norm = _compact(code.lower())
        name = it.get("itemname") or ""
        name_norm = _compact(name.lower())
        candidate = {
            "symbol": code,
            "name": name,
            "exchange": "KRX",
            "type": "ETF",
            "market": "국내",
        }
        if query_norm == code_norm or query_norm == name_norm:
            exact.append(candidate)
        elif code_norm.startswith(query_norm) or name_norm.startswith(query_norm):
            prefix.append(candidate)
        elif query_norm in name_norm or query_norm in code_norm:
            contains.append(candidate)
    return (exact + prefix + contains)[:8]


def resolve_krx_code(symbol):
    """Return the canonical (correctly-cased) KRX item code for `symbol` if
    it refers to a KRX-listed ETF, else None. Handles plain 6-digit codes
    (the common case) as well as the ~25% of KRX ETF codes that mix in a
    letter (e.g. "0223R0"), matched case-insensitively."""
    bare = symbol[:-3] if symbol.endswith((".KS", ".KQ")) else symbol
    if re.fullmatch(r"\d{6}", bare):
        return bare
    if not (len(bare) == 6 and bare.isalnum()):
        return None
    try:
        items = fetch_krx_etf_list()
    except requests.RequestException:
        return None
    upper = bare.upper()
    for it in items:
        if it.get("itemcode", "").upper() == upper:
            return it["itemcode"]
    return None


def parse_korean_date(value):
    """Parse a Naver-style "2002년 10월 14일" string into "2002-10-14"."""
    if not value:
        return None
    m = re.search(r"(\d{4})년\s*(\d{1,2})월\s*(\d{1,2})일", value)
    if not m:
        return None
    year, month, day = m.groups()
    return f"{year}-{int(month):02d}-{int(day):02d}"


def fetch_naver_coinfo(code):
    """Scrape the desktop ETF info page for fields the mobile API lacks
    (listing date, fund type/category). No auth required."""
    url = f"https://finance.naver.com/item/coinfo.naver?code={code}"
    try:
        r = requests.get(url, headers=HEADERS, timeout=8)
        r.raise_for_status()
        text = r.content.decode("euc-kr", errors="replace")
    except requests.RequestException:
        return {}
    result = {}
    m = re.search(r"상장일</th>\s*<td>([^<]+)</td>", text)
    if m:
        result["inceptionDate"] = parse_korean_date(m.group(1).strip())
    m = re.search(r"유형</th>\s*<td><span[^>]*>([^<]+)</span></td>", text)
    if m:
        result["category"] = m.group(1).strip()
    m = re.search(r"기초지수</th>\s*<td><span[^>]*>([^<]+)</span></td>", text)
    if m:
        result["benchmarkIndex"] = m.group(1).strip()
    return result


def format_period_label(days):
    """Turn a day count into a short Korean label like "3년", "1년 2개월",
    "8개월", or "12일" — used so a volatility figure never claims to cover
    "3년" when the underlying series is actually shorter (e.g. a fund
    listed 8 months ago)."""
    if not days or days < 1:
        return None
    days = int(days)
    if days < 30:
        return f"{days}일"
    years, remaining_days = divmod(days, 365)
    months = remaining_days // 30
    if months >= 12:
        years += 1
        months = 0
    if years >= 1:
        return f"{years}년 {months}개월" if months else f"{years}년"
    return f"{months}개월"


def historical_var(returns, confidence=0.975):
    """Empirical (historical) VaR at the given confidence level, as a
    positive loss percentage — e.g. 2.15 means "on the worst 2.5% of days
    in the sample, the loss exceeded 2.15%". Uses linear interpolation
    between ranks, same convention as numpy's default percentile method."""
    if not returns:
        return None
    ordered = sorted(returns)
    n = len(ordered)
    idx = (1 - confidence) * (n - 1)
    lower = int(idx)
    upper = min(lower + 1, n - 1)
    frac = idx - lower
    percentile_return = ordered[lower] + frac * (ordered[upper] - ordered[lower])
    return -percentile_return * 100


def compute_risk_stats(dates, closes):
    """Annualized volatility (%) and 1-day historical VaR at 97.5%
    confidence (%), from parallel lists of dates and closes. Returns
    (volatility, var975, days_covered) — days_covered reflects whatever
    history is actually available, which may be less than the 3y window
    requested (e.g. a recently-listed fund)."""
    points = sorted(
        ((d, c) for d, c in zip(dates, closes) if d is not None and c is not None),
        key=lambda p: p[0],
    )
    if len(points) < 2:
        return None, None, None
    values = [c for _, c in points]
    returns = [(curr - prev) / prev for prev, curr in zip(values, values[1:]) if prev]
    if len(returns) < 2:
        return None, None, None
    volatility = statistics.stdev(returns) * (252 ** 0.5) * 100
    var975 = historical_var(returns, 0.975) * (250 ** 0.5)
    days_covered = (points[-1][0] - points[0][0]).days
    return volatility, var975, days_covered


def fetch_naver_daily_series_risk_stats(base_url):
    end = datetime.now().strftime("%Y%m%d")
    start = (datetime.now() - timedelta(days=3 * 365 + 14)).strftime("%Y%m%d")
    try:
        r = requests.get(base_url, params={"startDateTime": start, "endDateTime": end}, headers=HEADERS, timeout=10)
        r.raise_for_status()
        rows = r.json()
    except (requests.RequestException, ValueError):
        return None, None, None
    if not isinstance(rows, list):
        return None, None, None
    dates = []
    for row in rows:
        d = row.get("localDate")
        try:
            dates.append(datetime.strptime(d, "%Y%m%d").date() if d else None)
        except (ValueError, TypeError):
            dates.append(None)
    closes = [row.get("closePrice") for row in rows]
    return compute_risk_stats(dates, closes)


def fetch_domestic_risk_stats(code):
    return fetch_naver_daily_series_risk_stats(f"https://api.stock.naver.com/chart/domestic/item/{code}/day")


# Common ETF benchmark index names -> Naver's domestic index chart code.
# Naver doesn't expose a name->code search for indices, so this only covers
# the broad-market indices Naver actually has a chart feed for. The many
# custom/thematic indices Korean ETFs track (KRX 반도체, FnGuide/WISE/iSelect
# sector indices, etc.) are calculated by private index providers with no
# free public historical series we could find — those stay unmapped and the
# UI shows "-" rather than guessing.
DOMESTIC_INDEX_CODES = {
    "코스피 200": "KPI200",
    "코스피200": "KPI200",
    "코스피 100": "KPI100",
    "코스피100": "KPI100",
    "코스피": "KOSPI",
    "코스닥": "KOSDAQ",
}

# Benchmark name -> Yahoo Finance index ticker, for the well-known global
# indices some domestic ETFs track (e.g. "KODEX 미국S&P500" -> S&P 500).
OVERSEAS_INDEX_TICKERS = {
    "S&P 500": "^GSPC",
    "S&P500": "^GSPC",
    "나스닥 100": "^NDX",
    "나스닥100": "^NDX",
    "NASDAQ 100": "^NDX",
    "나스닥종합": "^IXIC",
    "나스닥 종합": "^IXIC",
    "다우존스": "^DJI",
    "다우존스산업평균": "^DJI",
    "다우존스 산업평균": "^DJI",
    "러셀 2000": "^RUT",
    "러셀2000": "^RUT",
    "필라델피아 반도체": "^SOX",
    "필라델피아반도체": "^SOX",
    "니케이 225": "^N225",
    "니케이225": "^N225",
    "항셍": "^HSI",
    "항셍테크": "^HSTECH",
    "유로스톡스 50": "^STOXX50E",
    "유로스톡스50": "^STOXX50E",
    "독일DAX": "^GDAXI",
    "DAX": "^GDAXI",
    "영국FTSE100": "^FTSE",
    "FTSE100": "^FTSE",
}


def normalize_benchmark_name(name):
    """Strip parenthetical qualifiers ("(Price Return)", "(TR)") and common
    Korean/English suffix words so lookup keys match regardless of how the
    fund's disclosure page phrases the benchmark name (e.g. "S&P 500 Total
    Return Index" vs plain "S&P 500")."""
    if not name:
        return ""
    name = re.sub(r"\([^)]*\)", "", name)
    for suffix in ("지수", "Total Return", "Price Return", "Net Total Return", "Index", "TR", "PR", "NTR"):
        name = re.sub(re.escape(suffix), "", name, flags=re.IGNORECASE)
    return name.strip()


def _compact(text):
    return re.sub(r"[\s\-]", "", text)


def resolve_domestic_index_code(benchmark_name):
    normalized = _compact(normalize_benchmark_name(benchmark_name))
    if not normalized:
        return None
    for key in sorted(DOMESTIC_INDEX_CODES, key=len, reverse=True):
        if _compact(key) in normalized:
            return DOMESTIC_INDEX_CODES[key]
    return None


def resolve_overseas_index_ticker(benchmark_name):
    normalized = _compact(normalize_benchmark_name(benchmark_name)).upper()
    if not normalized:
        return None
    for key in sorted(OVERSEAS_INDEX_TICKERS, key=len, reverse=True):
        if _compact(key).upper() in normalized:
            return OVERSEAS_INDEX_TICKERS[key]
    return None


def fetch_domestic_index_risk_stats(index_code):
    if not index_code:
        return None, None, None
    return fetch_naver_daily_series_risk_stats(f"https://api.stock.naver.com/chart/domestic/index/{index_code}/day")


def fetch_overseas_risk_stats(symbol):
    url = f"https://query1.finance.yahoo.com/v8/finance/chart/{symbol}"
    try:
        r = requests.get(url, params={"range": "3y", "interval": "1d"}, headers=HEADERS, timeout=10)
        r.raise_for_status()
        result = r.json().get("chart", {}).get("result")
    except requests.RequestException:
        return None, None, None
    if not result:
        return None, None, None
    timestamps = result[0].get("timestamp") or []
    quotes = result[0].get("indicators", {}).get("quote") or [{}]
    closes = quotes[0].get("close", [])
    dates = [datetime.utcfromtimestamp(ts).date() if ts is not None else None for ts in timestamps]
    return compute_risk_stats(dates, closes)


def fetch_60d_averages(code):
    """60-trading-day average volume/value, computed from daily OHLCV
    history (KRX doesn't expose a simple public endpoint with this
    pre-computed, so we derive it ourselves)."""
    end = datetime.now().strftime("%Y%m%d")
    start = (datetime.now() - timedelta(days=130)).strftime("%Y%m%d")
    url = f"https://api.stock.naver.com/chart/domestic/item/{code}/day"
    try:
        r = requests.get(url, params={"startDateTime": start, "endDateTime": end}, headers=HEADERS, timeout=8)
        r.raise_for_status()
        rows = r.json()
    except (requests.RequestException, ValueError):
        return {}
    if not isinstance(rows, list) or not rows:
        return {}
    recent = rows[-60:]
    volumes = [row["accumulatedTradingVolume"] for row in recent if row.get("accumulatedTradingVolume") is not None]
    values = [
        row["accumulatedTradingVolume"] * row["closePrice"]
        for row in recent
        if row.get("accumulatedTradingVolume") is not None and row.get("closePrice") is not None
    ]
    if not volumes:
        return {}
    return {
        "avgVolume60d": sum(volumes) / len(volumes),
        "avgTradingValue60d": (sum(values) / len(values)) if values else None,
    }


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

    coinfo = fetch_naver_coinfo(code)
    averages_60d = fetch_60d_averages(code)
    volatility, var975, volatility_days = fetch_domestic_risk_stats(code)

    benchmark_index_code = resolve_domestic_index_code(coinfo.get("benchmarkIndex"))
    if benchmark_index_code:
        benchmark_volatility, benchmark_var975, benchmark_volatility_days = fetch_domestic_index_risk_stats(benchmark_index_code)
    else:
        overseas_index_ticker = resolve_overseas_index_ticker(coinfo.get("benchmarkIndex"))
        if overseas_index_ticker:
            benchmark_volatility, benchmark_var975, benchmark_volatility_days = fetch_overseas_risk_stats(overseas_index_ticker)
        else:
            benchmark_volatility, benchmark_var975, benchmark_volatility_days = None, None, None

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
        "category": coinfo.get("category"),
        "fundFamily": key_ind.get("issuerName"),
        "exchange": "KRX",
        "yield": (dividend_yield / 100) if dividend_yield is not None else None,
        "inceptionDate": coinfo.get("inceptionDate"),
        "avgVolume60d": averages_60d.get("avgVolume60d"),
        "avgTradingValue60d": averages_60d.get("avgTradingValue60d"),
        "benchmarkIndex": coinfo.get("benchmarkIndex"),
        "volatility": volatility,
        "volatilityPeriod": format_period_label(volatility_days),
        "var975": var975,
        "var975Period": format_period_label(volatility_days),
        "benchmarkVolatility": benchmark_volatility,
        "benchmarkVolatilityPeriod": format_period_label(benchmark_volatility_days),
        "benchmarkVar975": benchmark_var975,
        "benchmarkVar975Period": format_period_label(benchmark_volatility_days),
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
    krx_code = resolve_krx_code(symbol)
    if krx_code:
        return fetch_domestic_quote(krx_code)

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
    volatility, var975, volatility_days = fetch_overseas_risk_stats(symbol)

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
        "avgVolume60d": None,
        "avgTradingValue60d": None,
        "benchmarkIndex": None,
        "volatility": volatility,
        "volatilityPeriod": format_period_label(volatility_days),
        "var975": var975,
        "var975Period": format_period_label(volatility_days),
        "benchmarkVolatility": None,
        "benchmarkVolatilityPeriod": None,
        "benchmarkVar975": None,
        "benchmarkVar975Period": None,
        "hasData": True,
        "updatedAt": datetime.now().isoformat(),
    }


KOFIA_URL = "https://dis.kofia.or.kr/proframeWeb/XMLSERVICES/"
KOFIA_REFERER = (
    "https://dis.kofia.or.kr/websquare/index.jsp?w2xPath=/wq/fundann/DISFundStdPrice.xml"
    "&divisionId=MDIS01004001000000&serviceId=SDIS01004001000"
)
KOFIA_HEADERS = {
    "User-Agent": HEADERS["User-Agent"],
    "Content-Type": "text/xml; charset=UTF-8",
    "Referer": KOFIA_REFERER,
}


def kofia_last_business_day():
    d = datetime.now() - timedelta(days=1)
    while d.weekday() >= 5:
        d -= timedelta(days=1)
    return d.strftime("%Y%m%d")


def parse_kofia_date(value):
    if not value or len(value) != 8:
        return None
    return f"{value[:4]}-{value[4:6]}-{value[6:8]}"


def fetch_kofia_funds(name_query):
    """Search public (공모) mutual funds by name via KOFIA's electronic
    disclosure system (dis.kofia.or.kr). No login required, confirmed by
    hand via the site's own search form. Its TLS chain isn't recognized by
    Python's bundled CA list even though OS-level clients (e.g. curl on
    Windows) trust it fine, so verification is disabled for this one
    external call — no credentials or sensitive data cross this request,
    it's a public read-only fund lookup."""
    body = f"""<?xml version="1.0" encoding="utf-8"?>
<message>
  <proframeHeader>
    <pfmAppName>FS-DIS2</pfmAppName>
    <pfmSvcName>DISFundStdPriceSO</pfmSvcName>
    <pfmFnName>select</pfmFnName>
  </proframeHeader>
  <systemHeader></systemHeader>
    <DISCondFuncDTO>
    <tmpV30>{kofia_last_business_day()}</tmpV30>
    <tmpV3></tmpV3>
    <tmpV4></tmpV4>
    <tmpV7>1</tmpV7>
    <tmpV5></tmpV5>
    <tmpV11></tmpV11>
    <tmpV12>{name_query}</tmpV12>
    <tmpV50></tmpV50>
    <tmpV51></tmpV51>
</DISCondFuncDTO>
</message>
"""
    r = requests.post(KOFIA_URL, data=body.encode("utf-8"), headers=KOFIA_HEADERS, timeout=20, verify=False)
    r.raise_for_status()
    blocks = re.findall(r"<selectMeta>(.*?)</selectMeta>", r.text, re.S)

    def field(block, tag):
        m = re.search(rf"<{tag}>([^<]*)</{tag}>", block)
        return m.group(1).strip() if m and m.group(1).strip() else None

    results = []
    for b in blocks:
        name = field(b, "tmpV2")
        code = field(b, "tmpV12")
        if not name or not code:
            continue
        aum_mm = field(b, "tmpV5")
        nav = field(b, "tmpV6")
        results.append(
            {
                "code": code,
                "name": name,
                "company": field(b, "tmpV1"),
                "type": field(b, "tmpV3"),
                "inceptionDate": parse_kofia_date(field(b, "tmpV4")),
                "aum": float(aum_mm) * 1_000_000 if aum_mm else None,
                "nav": float(nav) if nav else None,
                "baseDate": parse_kofia_date(field(b, "tmpV14")),
                "market": "공모펀드",
            }
        )
    return results


@app.route("/api/fund/search")
def api_fund_search():
    q = request.args.get("q", "").strip()
    if not q:
        return jsonify({"error": "검색어를 입력해주세요."}), 400
    try:
        results = fetch_kofia_funds(q)
    except requests.RequestException as e:
        return jsonify({"error": f"검색 중 오류가 발생했습니다: {e}"}), 502
    return jsonify({"results": results[:30]})


def fetch_kofia_nav_history(code, start_date, end_date):
    """Daily 기준가(NAV) history for one fund over [start_date, end_date]
    (YYYYMMDD strings), via KOFIA's "기준가격변동추이" service. Computing
    this for every search result would mean one heavy request per row, so
    callers should only use this for a single fund the user has opened."""
    body = f"""<?xml version="1.0" encoding="utf-8"?>
<message>
  <proframeHeader>
    <pfmAppName>FS-DIS2</pfmAppName>
    <pfmSvcName>DISFundStdPrcStutSO</pfmSvcName>
    <pfmFnName>select</pfmFnName>
  </proframeHeader>
  <systemHeader></systemHeader>
    <DISCondFuncDTO>
    <tmpV30>{start_date}</tmpV30>
    <tmpV31>{end_date}</tmpV31>
    <tmpV10>0</tmpV10>
    <tmpV12>{code}</tmpV12>
</DISCondFuncDTO>
</message>
"""
    r = requests.post(KOFIA_URL, data=body.encode("utf-8"), headers=KOFIA_HEADERS, timeout=30, verify=False)
    r.raise_for_status()
    blocks = re.findall(r"<selectMeta>(.*?)</selectMeta>", r.text, re.S)

    dates, closes = [], []
    for b in blocks:
        m1 = re.search(r"<tmpV1>([^<]*)</tmpV1>", b)
        m2 = re.search(r"<tmpV2>([^<]*)</tmpV2>", b)
        raw_date = m1.group(1).strip() if m1 else None
        raw_nav = m2.group(1).strip() if m2 else None
        try:
            dates.append(datetime.strptime(raw_date, "%Y%m%d").date() if raw_date else None)
        except ValueError:
            dates.append(None)
        try:
            closes.append(float(raw_nav) if raw_nav else None)
        except ValueError:
            closes.append(None)
    return dates, closes


def fetch_kofia_risk_stats(code):
    end_date = kofia_last_business_day()
    start_date = (datetime.now() - timedelta(days=3 * 365 + 14)).strftime("%Y%m%d")
    dates, closes = fetch_kofia_nav_history(code, start_date, end_date)
    volatility, var975, days_covered = compute_risk_stats(dates, closes)
    return {
        "volatility": volatility,
        "volatilityPeriod": format_period_label(days_covered),
        "var975": var975,
        "var975Period": format_period_label(days_covered),
    }


@app.route("/api/fund/risk/<path:code>")
def api_fund_risk(code):
    try:
        return jsonify(fetch_kofia_risk_stats(code))
    except requests.RequestException as e:
        return jsonify({"error": f"변동성 계산 중 오류가 발생했습니다: {e}"}), 502


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
    kind = body.get("kind", "etf")
    items = load_saved()
    if not any(i["symbol"] == symbol and i.get("kind", "etf") == kind for i in items):
        entry = dict(body)
        entry["symbol"] = symbol
        entry["name"] = body.get("name", symbol)
        entry["market"] = body.get("market") or (market_of(symbol) if kind == "etf" else "공모펀드")
        entry["kind"] = kind
        entry["addedAt"] = datetime.now().isoformat()
        items.append(entry)
        write_saved(items)
    return jsonify(items)


@app.route("/api/saved/<path:symbol>", methods=["DELETE"])
def api_saved_remove(symbol):
    items = [i for i in load_saved() if i["symbol"] != symbol]
    write_saved(items)
    return jsonify(items)


@app.route("/api/history", methods=["GET"])
def api_history_list():
    return jsonify(load_history())


@app.route("/api/history", methods=["POST"])
def api_history_add():
    body = request.get_json(force=True, silent=True) or {}
    symbol = body.get("symbol")
    if not symbol:
        return jsonify({"error": "symbol이 필요합니다."}), 400
    kind = body.get("kind", "etf")
    items = [i for i in load_history() if not (i["symbol"] == symbol and i.get("kind", "etf") == kind)]
    entry = dict(body)
    entry["symbol"] = symbol
    entry["name"] = body.get("name", symbol)
    entry["market"] = body.get("market") or (market_of(symbol) if kind == "etf" else "공모펀드")
    entry["kind"] = kind
    entry["searchedAt"] = datetime.now().isoformat()
    items.insert(0, entry)
    write_history(items[:HISTORY_LIMIT])
    return jsonify(items[:HISTORY_LIMIT])


@app.route("/api/history", methods=["DELETE"])
def api_history_clear():
    kind = request.args.get("kind")
    if kind:
        items = [i for i in load_history() if i.get("kind", "etf") != kind]
    else:
        items = []
    write_history(items)
    return jsonify(items)


@app.route("/api/history/<path:symbol>", methods=["DELETE"])
def api_history_remove(symbol):
    items = [i for i in load_history() if i["symbol"] != symbol]
    write_history(items)
    return jsonify(items)


if __name__ == "__main__":
    port = int(os.environ.get("PORT", 5057))
    debug = os.environ.get("FLASK_DEBUG") == "1"
    app.run(debug=debug, host="0.0.0.0", port=port)
