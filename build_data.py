#!/usr/bin/env python3
"""Stock scan for NASDAQ and NYSE common stocks. Writes data.json.

A stock is kept only if BOTH hold, using the settings in params:
  1. the last closed bar's close is above the EMA(ema) of closes
  2. a regular bullish RSI divergence was confirmed within the last maxAge bars

Regular bullish divergence follows the logic of TradingView's built-in Divergence Indicator:
  - find pivot lows of RSI (pivL bars to the left, pivR bars to the right)
  - compare each RSI pivot low with the previous RSI pivot low
  - signal when price made a LOWER low there while RSI made a HIGHER low,
    and the two pivots are between rangeMin and rangeMax bars apart
  - the signal is confirmed pivR bars after the pivot; its age counts bars since then

Settings come from the PARAMS environment variable (JSON), else params.json, else defaults.
"""
import csv, io, json, os, re, sys, time, datetime as dt
from concurrent.futures import ThreadPoolExecutor
import urllib.request

DEFAULTS = {"tf": "1d", "ema": 1200, "rsiLen": 14, "pivL": 5, "pivR": 5,
            "rangeMin": 5, "rangeMax": 60, "maxAge": 3, "priceSrc": "low"}
LIMITS = {"ema": (2, 5000), "rsiLen": (2, 200), "pivL": (1, 50), "pivR": (1, 50),
          "rangeMin": (1, 500), "rangeMax": (2, 1000), "maxAge": (0, 50)}
# timeframe -> (yahoo interval, shallow period for the divergence pass, deep period for the EMA pass)
YF = {"15m": ("15m", "60d", "60d"), "1h": ("1h", "730d", "730d"), "4h": ("1h", "730d", "730d"),
      "1d": ("1d", "3y", "max"), "1w": ("1wk", "10y", "max")}
INCLUDE_EXCHANGES = {"N": "NYSE"}          # add "A": "NYSE American", "P": "NYSE Arca" if wanted
BATCH = 150
ET = "America/New_York"
NASDAQ_URL = "https://www.nasdaqtrader.com/dynamic/SymDir/nasdaqlisted.txt"
OTHER_URL = "https://www.nasdaqtrader.com/dynamic/SymDir/otherlisted.txt"
BAD_NAME = re.compile(r"\b(warrants?|rights?|units?|preferred|depositary|notes?|debentures?|subordinated)\b", re.I)
SYM_OK = re.compile(r"^[A-Z]{1,5}([.-][A-Z])?$")


# ---------------------------------------------------------------- settings
def normalize_params(p):
    q = dict(DEFAULTS)
    q.update({k: v for k, v in (p or {}).items() if k in DEFAULTS})
    if q["tf"] == "1wk":
        q["tf"] = "1w"
    if q["tf"] not in YF:
        raise ValueError(f"timeframe must be one of {sorted(YF)}")
    if q["priceSrc"] not in ("low", "close"):
        raise ValueError("priceSrc must be low or close")
    for k, (lo, hi) in LIMITS.items():
        q[k] = int(q[k])
        if not lo <= q[k] <= hi:
            raise ValueError(f"{k} must be between {lo} and {hi}")
    if q["rangeMin"] > q["rangeMax"]:
        raise ValueError("rangeMin cannot be larger than rangeMax")
    return q


def load_params():
    raw = os.environ.get("PARAMS", "").strip()
    if raw:
        p = normalize_params(json.loads(raw))
        with open("params.json", "w") as f:
            json.dump(p, f)
        return p
    if os.path.exists("params.json"):
        return normalize_params(json.load(open("params.json")))
    return normalize_params({})


# ---------------------------------------------------------------- indicators
def ema_last(vals, n):
    """EMA of the last value, seeded with the SMA of the first n values (as TradingView's ta.ema)."""
    if len(vals) < n:
        return None
    a = 2.0 / (n + 1)
    e = sum(vals[:n]) / n
    for v in vals[n:]:
        e = a * v + (1 - a) * e
    return e


def _rs(g, l):
    return 100.0 if l == 0 else 100.0 - 100.0 / (1.0 + g / l)


def rsi_series(c, n):
    """Wilder RSI for every bar; None until n+1 closes exist."""
    out = [None] * len(c)
    if len(c) < n + 1:
        return out
    g = l = 0.0
    for i in range(1, n + 1):
        d = c[i] - c[i - 1]
        g += max(d, 0.0)
        l += max(-d, 0.0)
    g, l = g / n, l / n
    out[n] = _rs(g, l)
    for i in range(n + 1, len(c)):
        d = c[i] - c[i - 1]
        g = (g * (n - 1) + max(d, 0.0)) / n
        l = (l * (n - 1) + max(-d, 0.0)) / n
        out[i] = _rs(g, l)
    return out


def last_bull_div(rsi, price, L, R, min_r, max_r, max_age, full=False):
    """Most recent regular bullish divergence confirmed within max_age bars, or None.
    full=True scans the whole series (reference version used by the tests)."""
    n = len(rsi)
    start = L if full else max(L, n - 1 - max_age - R - max_r - L - 1)
    prev = None
    found = None
    for p in range(start, n - R):
        r = rsi[p]
        if r is None:
            continue
        ok = True
        for j in range(p - L, p + R + 1):
            if rsi[j] is None or rsi[j] < r:
                ok = False
                break
        if not ok:
            continue
        if prev is not None:
            d = p - prev[0]
            if min_r <= d <= max_r and r > prev[1] and price[p] < prev[2]:
                found = (p, prev[0], r, prev[1], price[p], prev[2])
        prev = (p, r, price[p])
    if not found:
        return None
    age = n - 1 - (found[0] + R)
    if age > max_age:
        return None
    return {"p": found[0], "q": found[1], "rsiNow": found[2], "rsiPrev": found[3],
            "priceNow": found[4], "pricePrev": found[5], "age": age}


# ---------------------------------------------------------------- bars
def fmt_ts(ts, tf):
    ts = ts.tz_convert(ET) if getattr(ts, "tzinfo", None) is not None else ts
    return ts.strftime("%Y-%m-%d") if tf in ("1d", "1w") else ts.strftime("%Y-%m-%d %H:%M")


def unfinished(ts, tf, now):
    import pandas as pd
    if tf == "15m":
        end = ts + pd.Timedelta(minutes=15)
    elif tf == "1h":
        end = ts + pd.Timedelta(hours=1)
    elif tf == "4h":
        end = ts + (pd.Timedelta(hours=4) if ts.tz_convert(ET).hour < 12 else pd.Timedelta(hours=2, minutes=30))
    elif tf == "1d":
        end = ts + pd.Timedelta(hours=16, minutes=15)
    else:
        end = ts + pd.Timedelta(days=4, hours=16, minutes=15)
    return end > now


def to_4h(sub):
    """US stock 4H bars: 09:30-13:30 and 13:30-16:00, built from hourly bars."""
    import pandas as pd
    day = sub.index.tz_convert(ET).normalize()
    pos = pd.Series(0, index=sub.index).groupby(day).cumcount().values
    half = (pos >= 4).astype(int)
    keys = [day, half]
    close = sub["Close"].groupby(keys).last()
    low = sub["Low"].groupby(keys).min()
    ts = pd.Series(sub.index, index=sub.index).groupby(keys).first()
    out = pd.DataFrame({"Close": close.values, "Low": low.values}, index=pd.DatetimeIndex(ts.values))
    return out.sort_index()


def clean_frame(sub, tf, now):
    """Close/Low frame with tz-aware index, 4h aggregation applied, unfinished last bar removed."""
    import pandas as pd
    sub = sub.dropna(subset=["Close", "Low"])
    if len(sub) == 0:
        return None
    if getattr(sub.index, "tz", None) is None:
        sub = sub.copy()
        sub.index = sub.index.tz_localize(ET)
    if tf == "4h":
        sub = to_4h(sub)
    if len(sub) and unfinished(sub.index[-1], tf, now):
        sub = sub.iloc[:-1]
    return sub if len(sub) else None


# ---------------------------------------------------------------- data
def parse_universe(nasdaq_txt, other_txt):
    out = {}
    for row in csv.DictReader(io.StringIO(nasdaq_txt), delimiter="|"):
        s = (row.get("Symbol") or "").strip()
        if not s or s.startswith("File Creation"):
            continue
        if row.get("ETF") == "Y" or row.get("Test Issue") == "Y":
            continue
        out[s] = (row["Security Name"], "NASDAQ")
    for row in csv.DictReader(io.StringIO(other_txt), delimiter="|"):
        s = (row.get("ACT Symbol") or "").strip()
        if not s or s.startswith("File Creation"):
            continue
        ex = INCLUDE_EXCHANGES.get(row.get("Exchange"))
        if not ex or row.get("ETF") == "Y" or row.get("Test Issue") == "Y":
            continue
        out[s] = (row["Security Name"], ex)
    clean = {}
    for s, (name, ex) in out.items():
        if not SYM_OK.match(s) or BAD_NAME.search(name):
            continue
        clean[s.replace(".", "-")] = (name.split(" - ")[0].strip(), ex)   # Yahoo uses BRK-B
    return clean


def fetch_text(url):
    req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
    with urllib.request.urlopen(req, timeout=60) as r:
        return r.read().decode("utf-8", "replace")


def fetch_universe_text():
    out = []
    for name, url in (("nasdaqlisted.txt", NASDAQ_URL), ("otherlisted.txt", OTHER_URL)):
        try:
            out.append(fetch_text(url))
        except Exception as e:
            print(f"https failed for {name} ({e}); trying ftp", file=sys.stderr)
            out.append(fetch_text("ftp://ftp.nasdaqtrader.com/symboldirectory/" + name))
    return out


def download_batch(yf, chunk, interval, period, tries=3):
    err = None
    for a in range(tries):
        try:
            df = yf.download(chunk, period=period, interval=interval, group_by="ticker",
                             auto_adjust=True, threads=True, progress=False)
            if df is not None and len(df):
                return df, None
        except Exception as e:
            err = e
        time.sleep(5 * (a + 1))
    return None, err


def extract(df, sym):
    multi = getattr(df.columns, "nlevels", 1) > 1
    if multi:
        if sym not in set(df.columns.get_level_values(0)):
            return None
        return df[sym]
    return df


# ---------------------------------------------------------------- scan
def stage1(yf, symbols, P, diag, now):
    """Download recent bars for everyone and keep tickers with a fresh bullish divergence."""
    interval, shallow, _ = YF[P["tf"]]
    need = P["rsiLen"] + P["pivL"] + P["pivR"] + 5
    keep, scanned = [], 0
    for i in range(0, len(symbols), BATCH):
        chunk = symbols[i:i + BATCH]
        df, err = download_batch(yf, chunk, interval, shallow)
        if df is None:
            diag["batchesFailed"] += 1
            diag["lastError"] = repr(err)[:300] if err else "empty result"
            print("batch failed", i, diag["lastError"], file=sys.stderr, flush=True)
            continue
        for s in chunk:
            try:
                sub = extract(df, s)
                sub = clean_frame(sub, P["tf"], now) if sub is not None else None
            except Exception:
                sub = None
            if sub is None or len(sub) < need:
                continue
            scanned += 1
            closes, lows = sub["Close"].tolist(), sub["Low"].tolist()
            rsi = rsi_series(closes, P["rsiLen"])
            price = lows if P["priceSrc"] == "low" else closes
            d = last_bull_div(rsi, price, P["pivL"], P["pivR"], P["rangeMin"], P["rangeMax"], P["maxAge"])
            if d:
                d["dateNow"] = fmt_ts(sub.index[d["p"]], P["tf"])
                d["datePrev"] = fmt_ts(sub.index[d["q"]], P["tf"])
                keep.append({"sym": s, "div": d, "rsi": rsi[-1], "closes": closes, "asOf": fmt_ts(sub.index[-1], P["tf"])})
        print(f"divergence pass {min(i + BATCH, len(symbols))}/{len(symbols)}  ok: {scanned}  with divergence: {len(keep)}", flush=True)
        time.sleep(1)
    return keep, scanned


def stage2(yf, keep, P, diag, now):
    """For tickers with a divergence, get full history and test price > EMA."""
    interval, shallow, deep = YF[P["tf"]]
    series = {k["sym"]: k["closes"] for k in keep}
    if deep != shallow:
        series = {}
        syms = [k["sym"] for k in keep]
        for i in range(0, len(syms), BATCH):
            chunk = syms[i:i + BATCH]
            df, err = download_batch(yf, chunk, interval, deep)
            if df is None:
                diag["batchesFailed"] += 1
                diag["lastError"] = repr(err)[:300] if err else "empty result"
                continue
            for s in chunk:
                try:
                    sub = clean_frame(extract(df, s), P["tf"], now)
                except Exception:
                    sub = None
                if sub is not None:
                    series[s] = sub["Close"].tolist()
            time.sleep(1)
    out = []
    for k in keep:
        closes = series.get(k["sym"])
        if not closes or len(closes) < P["ema"]:
            diag["insufficientHistory"] += 1
            continue
        e = ema_last(closes, P["ema"])
        if closes[-1] > e:
            out.append({"sym": k["sym"], "price": closes[-1], "ema": e, "pct": (closes[-1] / e - 1) * 100,
                        "rsi": k["rsi"], "bars": len(closes), "age": k["div"]["age"], "div": k["div"], "asOf": k["asOf"]})
    return out


def build(yf, uni_texts, P, out_path="data.json"):
    import pandas as pd
    now = pd.Timestamp.now(tz="UTC")
    uni = parse_universe(*uni_texts)
    counts = {ex: sum(1 for v in uni.values() if v[1] == ex) for ex in sorted({v[1] for v in uni.values()})}
    print("universe", counts, "params", P, flush=True)
    if len(uni) < 1000:
        raise SystemExit(f"Symbol lists look wrong: only {len(uni)} tickers parsed")
    diag = {"batchesFailed": 0, "lastError": None, "insufficientHistory": 0}
    keep, scanned = stage1(yf, sorted(uni), P, diag, now)
    if scanned < 0.5 * len(uni):
        raise SystemExit(f"Price history failed for most tickers ({scanned} of {len(uni)} ok). Yahoo probably "
                         f"rate-limited this run, or this timeframe has too little data. Last error: {diag['lastError']}. "
                         f"data.json left unchanged.")
    hits = stage2(yf, keep, P, diag, now)
    for h in hits:
        h["name"], h["exch"] = uni[h["sym"]]
    hits.sort(key=lambda x: (x["age"], -x["pct"]))
    out = {"generated": dt.datetime.now(dt.timezone.utc).isoformat(timespec="seconds"), "params": P,
           "universe": counts, "scanned": scanned, "withDivergence": len(keep),
           "insufficientHistory": diag["insufficientHistory"], "aboveEma": len(hits),
           "batchesFailed": diag["batchesFailed"], "stocks": hits}
    with open(out_path, "w") as f:
        json.dump(out, f, separators=(",", ":"))
    print(f"done: universe {len(uni)}, scanned {scanned}, with divergence {len(keep)}, "
          f"not enough history for EMA {diag['insufficientHistory']}, final matches {len(hits)}")
    return out


def main():
    import yfinance as yf
    build(yf, fetch_universe_text(), load_params())


if __name__ == "__main__":
    main()
