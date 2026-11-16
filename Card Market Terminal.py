#!/usr/bin/env python3
"""Card Market Terminal v3.22 — single-file, stdlib-only market terminal for MTG, Pokémon, One Piece and Riftbound singles.

Market monitor (indices, breadth, movers, alerts), command line (type a card name or HELP), rankings with
autocorrelation-adjusted Sharpe and false-discovery-rate significance, calibrated forecasts, buy/sell
prices after fees and liquidity, set heatmap and release calendar, and a portfolio with hold/sell signals.
Free data only: TCGCSV (TCGplayer prices), MTGJSON (MTG history), Scryfall (set calendar), FRED (T-bill rate).

Run the GUI:       python3 "Card Market Terminal.py"
Run a headless sync: python3 "Card Market Terminal.py" --sync
Run offline tests: python3 "Card Market Terminal.py" --self-test

The TCGCSV collector checks its daily build marker and uses a custom User-Agent and
request pacing. It does not place trades or perform per-card rapid polling.
"""
import bisect
import csv
import gzip
import http.client
import io
import tempfile
import json
import lzma
import math
import statistics
import os
import queue
import re
import sqlite3
import sys
import threading
import time
import urllib.request
import urllib.parse
import urllib.error
import unittest
from unittest import mock
from urllib.parse import urlsplit, urljoin
from xml.sax.saxutils import escape as xml_escape
import plistlib
import subprocess
import hashlib
import pickle
import shutil
from contextlib import contextmanager
from datetime import date, datetime, timezone, timedelta
from pathlib import Path
try:
    import tkinter as tk
    from tkinter import ttk, filedialog, messagebox
except ImportError:  # Python without Tk: --sync and --self-test still work; only the GUI needs it
    tk=ttk=filedialog=messagebox=None

APP = 'Card Market Terminal'
SUPPORTED_GAMES = ('MTG', 'Pokémon', 'One Piece', 'Riftbound')
# Rarities priced like ordinary cards in the non-MTG games (everything else counts as a special treatment).
REGULAR_RARITIES = ('Common','Uncommon','Rare','C','UC','R')
HISTORY_ARCHIVE_BASE = 'https://tcgcsv.com/archive/tcgplayer'
HISTORY_ARCHIVE_FIRST_DATE = datetime(2024, 2, 8).date()
def _data_root():
    """Where the data lives: --data FOLDER (passed by the Windows scheduled task) or CMT_DATA if set; a 'CardMarketTerminalData'
    folder beside this script (a portable copy you can carry between computers); otherwise the one in your user profile."""
    if '--data' in sys.argv[1:-1]: return Path(sys.argv[sys.argv.index('--data',1)+1])
    if os.environ.get('CMT_DATA'): return Path(os.environ['CMT_DATA'])
    beside=Path(__file__).resolve().parent/'CardMarketTerminalData'
    return beside if beside.is_dir() else Path.home()/'CardMarketTerminalData'

ROOT = _data_root()
DB = ROOT / 'market.sqlite3'
USER_AGENT = 'CardMarketTerminal/3.22 (daily market-data research; local desktop application)'
TCGCSV_BASE = 'https://tcgcsv.com/tcgplayer'
TCGCSV_LAST_UPDATED = 'https://tcgcsv.com/last-updated.txt'
TCGCSV_CATEGORIES = [(1, 'MTG'), (3, 'Pokémon'), (68, 'One Piece'), (89, 'Riftbound')]
TCGCSV_DAILY_REQUEST_BUDGET = 8000  # keep a safety margin below TCGCSV's 10,000/day warning
TCGCSV_MIN_INTERVAL = 0.11  # documented minimum spacing between request starts
TCGCSV_PREFETCH_DEPTH = 4   # groups fetched ahead while earlier groups are written to SQLite
TCGCSV_PRICE_FIELDS = [('marketPrice','market'),('lowPrice','low'),('midPrice','mid'),
                       ('highPrice','high_raw'),('directLowPrice','direct_low')]
MTGJSON_BASE = 'https://mtgjson.com/api/v5'
# TCGplayer subTypeName for each MTGJSON finish; etched maps via tcgplayerEtchedProductId.
MTGJSON_FINISH_SUBTYPES = {'normal':'Normal','foil':'Foil','etched':'Foil'}
SHARPE_MIN_OBS_30D = 28  # daily observations required in the 30-day Sharpe window (up to 2 missing days)
# Ranking exclusions for moves that are almost certainly listing artifacts or thin-market noise.
RANK_PRICE_TYPE = 'market_Normal'  # default printing charted in Market History (every printing is ranked separately)
RANK_MIN_PRICE = 1.00        # USD; bulk-priced cards move on single sales
RANK_SCAN_DAYS = 100         # days of prices scanned: rankings use the latest 35, indices and forecasts all of them
SPIKE_MARKET_TO_LOW = 2.0    # market estimate at least this multiple of the cheapest current listing
SPIKE_LOW_TO_MARKET = 0.75   # ...or under this share of it: recent sales (often played copies) dragged TCGplayer's
                             # all-condition market price below every copy you can actually buy
SPIKE_JUMP_SHARE = 0.6       # one daily move is at least this share of the whole 30-day rise...
SPIKE_MIN_RETURN_30D = 25.0  # ...on a 30-day rise of at least this many percent
WINDOWS_TASK_NAME = 'CardMarketTerminal Daily Sync'
# Local times. TCGCSV publishes ~20:00 UTC; the late run catches delayed builds or a failed first run.
WINDOWS_TASK_TIMES = ('14:30','22:00')
_tcgcsv_budget_lock = threading.Lock()
_tcgcsv_pace_lock = threading.Lock()
_tcgcsv_last_request = 0.0
_tcgcsv_http = threading.local()  # per-thread keep-alive connections

def utc(): return datetime.now(timezone.utc).isoformat(timespec='seconds')
def money(n): return f'${n:,.2f}' if n is not None else '—'
def numeric(x):
    try:
        z = float(x)
        return z if 0 < z < 100000000 else None
    except (ValueError, TypeError): return None


def emit_progress(report, current, total, phase):
    """Send optional structured progress without breaking CLI/test report callbacks."""
    callback = getattr(report, 'progress', None)
    if callable(callback):
        callback(current, total, phase)

def _source_day(value):
    # Parse an ISO-like source timestamp to a UTC calendar date, if possible.
    try:
        raw=str(value).strip()
        dt=datetime.fromisoformat(raw.replace('Z','+00:00'))
        if dt.tzinfo is not None:
            dt=dt.astimezone(timezone.utc)
        return dt.date()
    except (ValueError,TypeError,OverflowError):
        return None


def calculate_net_profit(buy_price, resale_price, fee_percent, other_costs, quantity):
    """Calculate a simple hypothetical trade result; not a prediction or quote."""
    vals=(buy_price,resale_price,fee_percent,other_costs,quantity)
    if any(not isinstance(v,(int,float)) or not (-float('inf') < float(v) < float('inf')) for v in vals):
        raise ValueError('All inputs must be finite numbers')
    if quantity <= 0 or int(quantity) != quantity:
        raise ValueError('Quantity must be a positive whole number')
    if buy_price < 0 or resale_price < 0 or other_costs < 0:
        raise ValueError('Prices and costs cannot be negative')
    if not 0 <= fee_percent <= 100:
        raise ValueError('Selling fee must be between 0 and 100 percent')
    quantity=int(quantity)
    total_cost=buy_price*quantity+other_costs
    net_proceeds=resale_price*quantity*(1-fee_percent/100)
    profit=net_proceeds-total_cost
    roi=(profit/total_cost*100) if total_cost else None
    return profit,roi


def liquidity_label(changes):
    """Trading-activity proxy: days in the last 30 on which the market price moved (it moves on sales)."""
    if changes is None: return '—'
    return 'High' if changes>=15 else 'Medium' if changes>=6 else 'Low' if changes>=2 else 'Very low'


def fetch_risk_free_rate():
    """Latest 3-month US Treasury bill rate (FRED series DTB3), in percent."""
    req=urllib.request.Request(RISK_FREE_SOURCE,headers={'User-Agent':USER_AGENT,'Accept':'text/csv'})
    with urllib.request.urlopen(req,timeout=30) as r:
        lines=r.read().decode('utf-8-sig').strip().splitlines()
    for line in reversed(lines[1:]):
        day,_,value=line.partition(',')
        try: return float(value),day
        except ValueError: continue  # FRED marks holidays with '.'
    raise RuntimeError('FRED returned no 3-month T-bill rate')


_DAY_ORDINALS = {}

def _day_ordinal(stamp):
    """UTC calendar day of a source timestamp as a date ordinal (None if unparseable).

    Stored stamps are 'YYYY-MM-DD', '...T..:..:..' or '...+00:00'; those take a cached fast path,
    since parsing millions of them with fromisoformat dominated the ranking scan.
    """
    s=str(stamp)
    if len(s)==10 or (len(s)>10 and s[10]=='T' and (len(s)==19 or s.endswith('+00:00') or s.endswith('Z'))):
        key=s[:10]; o=_DAY_ORDINALS.get(key)
        if o is None:
            try: o=datetime.strptime(key,'%Y-%m-%d').date().toordinal()
            except ValueError: o=False
            if len(_DAY_ORDINALS)<20000: _DAY_ORDINALS[key]=o
        if o is not False: return o
    day=_source_day(s)
    return day.toordinal() if day else None

def _normal_cdf(x): return 0.5*(1.0+math.erf(x/math.sqrt(2.0)))

SIGNIFICANCE_FDR = 0.10  # a positive Sharpe counts as significant when its Benjamini–Hochberg q-value is at most this
SHARPE_NW_LAGS = 3  # Newey–West lags: TCGplayer "market" is a smoothed average of recent sales, so its returns autocorrelate

def daily_series(points):
    """Sorted (date ordinal, price) with one price per UTC day: the latest-stamped valid one."""
    by_day={}
    for stamp,raw_price in points:
        try: price=float(raw_price)
        except (TypeError,ValueError): continue
        if not 0<price<100000000: continue
        o=_day_ordinal(stamp)
        if o is None: continue
        s=str(stamp); prior=by_day.get(o)
        if prior is None or s>prior[0]: by_day[o]=(s,price)
    return sorted((o,item[1]) for o,item in by_day.items())

def calculate_market_metrics(points, today=None, risk_free=0.0, series=None):
    """Return/risk metrics for one printing's daily market prices.

    risk_free is an annual rate (0.0404 = 4.04%), subtracted from each daily log return as ln(1+rf)/365.
    Sharpe uses consecutive daily log returns from the latest 30-calendar-day window and is suppressed
    unless the window has SHARPE_MIN_OBS_30D observations and 20 one-day returns. It is annualized with a
    Newey–West long-run variance (Bartlett weights, SHARPE_NW_LAGS lags) rather than √365 alone: a smoothed
    price series has positively autocorrelated returns, which makes the naive √365 scaling overstate Sharpe.
    psr is the Probabilistic Sharpe Ratio (Bailey & López de Prado): the probability the true Sharpe is above
    zero given the sample length (deflated by the autocorrelation), skewness and kurtosis of the returns.
    series, if given, is a daily_series() result to use instead of parsing points.
    """
    today=today or datetime.now(timezone.utc).date()
    if isinstance(today,datetime): today=today.date()
    if series is None: series=daily_series(points)
    if not series: return {
        'observations':0,'obs_30d':0,'latest_date':None,'latest_price':None,
        'age_days':None,'return_7d':None,'return_30d':None,'drawdown_30d':None,
        'sharpe_30d':None,'opportunity_score':None,'consecutive_returns':0,'jump_share':None,
        'volatility_30d':None,'price_changes_30d':None,'psr':None,'autocorr_1':None,'return_sd_30d':None
    }
    days=[o for o,_ in series]
    latest_o,latest_price=series[-1]
    age_days=max(0,today.toordinal()-latest_o)

    def pct_change(back,tolerance):
        target=latest_o-back; best=None
        for i in range(bisect.bisect_left(days,target-tolerance),bisect.bisect_right(days,target+tolerance)):
            o,price=series[i]; cand=(abs(o-target),0 if o<=target else 1,o,price)
            if best is None or cand<best: best=cand
        if best is None: return None
        return (latest_price/best[3]-1.0)*100 if best[3]>0 else None

    return_7d=pct_change(7,2)
    return_30d=pct_change(30,3)
    recent=series[bisect.bisect_left(days,latest_o-29):]
    obs_30d=len(recent)
    high=max(price for _,price in recent)
    drawdown=((latest_price/high)-1.0)*100 if high>0 else None
    daily_returns=[]; changes=0
    for (o0,p0),(o1,p1) in zip(recent,recent[1:]):
        if abs(p1-p0)>1e-9: changes+=1
        if o1-o0==1: daily_returns.append(math.log(p1/p0))
    n=len(daily_returns)
    # Share of the window's total rise that came from its single largest one-day move.
    jump_share=None
    if n and recent[0][1]>0:
        total_log=math.log(latest_price/recent[0][1])
        if total_log>0: jump_share=max(daily_returns)/total_log
    sd=lrv=rho1=None
    if n>=2:
        mean=sum(daily_returns)/n
        dev=[r-mean for r in daily_returns]
        ss=sum(d*d for d in dev); sd=math.sqrt(ss/(n-1))
        lrv=1.0
        if ss>1e-18 and n>=8:
            rhos=[sum(dev[t]*dev[t-k] for t in range(k,n))/ss for k in range(1,SHARPE_NW_LAGS+1)]
            rho1=rhos[0]
            lrv=1.0+2.0*sum((1.0-k/(SHARPE_NW_LAGS+1.0))*rho for k,rho in enumerate(rhos,1))
            # Conservative: positive autocorrelation shrinks the Sharpe; a negative estimate from ~29 returns
            # is too noisy to be credited with raising it.
            lrv=max(1.0,lrv)
    sharpe=psr=None
    if obs_30d>=SHARPE_MIN_OBS_30D and n>=20 and sd and sd>1e-9:
        daily_rf=math.log1p(risk_free)/365.0
        sr=(mean-daily_rf)/sd  # per-day Sharpe
        sharpe=sr*math.sqrt(365.0/lrv)
        if not math.isfinite(sharpe): sharpe=None
        m2=ss/n
        if sharpe is not None and m2>0:
            skew=sum(d**3 for d in dev)/n/m2**1.5; kurt=sum(d**4 for d in dev)/n/m2**2
            n_eff=n/lrv; denom=1.0-skew*sr+(kurt-1.0)/4.0*sr*sr
            if n_eff>2 and denom>1e-12: psr=_normal_cdf(sr*math.sqrt(n_eff-1.0)/math.sqrt(denom))

    score=None
    if age_days<=3 and len(series)>=8:
        components=[]
        if return_7d is not None:
            components.append((max(0.0,min(100.0,(max(-20.0,min(20.0,return_7d))+20.0)*2.5)),0.45))
        if return_30d is not None:
            components.append((max(0.0,min(100.0,(max(-40.0,min(40.0,return_30d))+40.0)*1.25)),0.35))
        if sharpe is not None:
            components.append((max(0.0,min(100.0,(max(-1.0,min(3.0,sharpe))+1.0)*25.0)),0.20))
        weight=sum(w for _,w in components)
        if weight>0: score=sum(value*w for value,w in components)/weight
    return {
        'observations':len(series),'obs_30d':obs_30d,'latest_date':date.fromordinal(latest_o).isoformat(),
        'latest_price':latest_price,'age_days':age_days,'return_7d':return_7d,
        'return_30d':return_30d,'drawdown_30d':drawdown,'sharpe_30d':sharpe,
        'opportunity_score':score,'consecutive_returns':n,'jump_share':jump_share,
        # Annualized with the same long-run variance as the Sharpe, so Sharpe ≈ excess return ÷ volatility.
        'volatility_30d':sd*math.sqrt(365.0*(lrv or 1.0)) if sd is not None else None,
        'price_changes_30d':changes,'psr':psr,'autocorr_1':rho1,
        # Plain daily log-return standard deviation (no autocorrelation adjustment), the forecast's volatility input.
        'return_sd_30d':sd if n>=FORECAST_MIN_VOL_RETURNS else None
    }


def benjamini_hochberg(pvalues):
    """False-discovery-rate q-values (Benjamini–Hochberg) in the input order; None stays None."""
    ranked=sorted((p,i) for i,p in enumerate(pvalues) if p is not None)
    out=[None]*len(pvalues); m=len(ranked); running=1.0
    for rank in range(m,0,-1):
        p,i=ranked[rank-1]
        running=min(running,p*m/rank); out[i]=running
    return out


def wilson_interval(p, n, z=1.64):
    """~90% Wilson score interval for a proportion p observed over n (effective) samples."""
    if p is None or not n or n<=0: return None
    denom=1+z*z/n; centre=(p+z*z/(2*n))/denom
    half=z*math.sqrt(p*(1-p)/n+z*z/(4*n*n))/denom
    return max(0.0,centre-half),min(1.0,centre+half)


RISK_FREE_SOURCE = 'https://fred.stlouisfed.org/graph/fredgraph.csv?id=DTB3'  # 3-month T-bill, percent
DEFAULT_RISK_FREE_PCT = 4.04  # FRED DTB3 on 2026-10-23; refresh with Fetch T-bill rate in Settings
PRICE_SLIDER_MIN, PRICE_SLIDER_MAX = 0.10, 5000.0  # log-scaled price filter range (USD)
SHARPE_SLIDER_MIN, SHARPE_SLIDER_MAX = -5.0, 30.0

def slider_to_price(pos):
    return PRICE_SLIDER_MIN*(PRICE_SLIDER_MAX/PRICE_SLIDER_MIN)**(float(pos)/100.0)

def price_to_slider(price):
    return 100.0*math.log(price/PRICE_SLIDER_MIN)/math.log(PRICE_SLIDER_MAX/PRICE_SLIDER_MIN)

def filter_ranked_rows(rows, price_min=None, price_max=None, sharpe_min=None, sharpe_max=None, min_changes=None,
                       min_rise=None, min_win=None, buyable_only=False, significant_only=False):
    """Apply the ranking filters; None means unbounded. A Sharpe bound drops rows without a Sharpe, and
    forecast bounds (fractions) drop rows not yet annotated by annotate_with_pricing."""
    out=[]
    for r in rows:
        price=r.get('latest_price'); sharpe=r.get('sharpe_30d')
        if min_changes is not None and (r.get('price_changes_30d') or 0)<min_changes: continue
        if min_rise is not None and (r.get('p_rise') is None or r['p_rise']<min_rise): continue
        if min_win is not None and (r.get('win') is None or r['win']<min_win): continue
        if buyable_only and not r.get('buyable'): continue
        if significant_only and not (r.get('fdr_q') is not None and r['fdr_q']<=SIGNIFICANCE_FDR and (sharpe or 0)>0): continue
        if price_min is not None and (price is None or price<price_min): continue
        if price_max is not None and (price is None or price>price_max): continue
        if sharpe_min is not None and (sharpe is None or sharpe<sharpe_min): continue
        if sharpe_max is not None and (sharpe is None or sharpe>sharpe_max): continue
        out.append(r)
    return out

def parse_filter_value(text):
    """'$1,250.50' -> 1250.5; blank/'any'/'no max' -> None (unbounded); anything else raises ValueError."""
    raw=str(text).strip().lower().replace('$','').replace(',','').replace('%','')
    if raw in ('','any','no max','none','-'): return None
    return float(raw)


# --- Forecasting: empirical forward-return distributions from the local price history ---
# For each historical "anchor" day the model records what a printing's market price did over the
# next N days, bucketed by what it had done before (30-day and 7-day change), its price tier and
# whether it is a Normal or foil-type printing. A card's forecast is the outcome distribution of
# its bucket. The newest anchors are held out to measure accuracy out of sample.
FORECAST_HORIZONS = (7, 14, 30)
FORECAST_LOOKBACK_DAYS = 100
FORECAST_STEP_DAYS = 3
FORECAST_MODEL_VERSION = 10  # bump when the model format or method changes so cached models are rebuilt
FORECAST_MIN_PRICE = 0.50   # bulk printings never reach a buy decision and only add noise to the lowest tier
FORECAST_PRIOR = 300        # pseudo-samples: each bucket is shrunk toward its broader parent (Dirichlet prior)
FORECAST_TEST_SPAN = 21     # days of newest anchors held out for the backtest
_FORECAST_BIN = 0.005       # forward returns are histogrammed in 0.5% steps
_R30_EDGES = (-0.10,-0.02,0.02,0.10,0.30)
_R7_EDGES = (-0.03,0.03)
_PRICE_EDGES = (2.0,10.0,50.0)
DEFAULT_PRICING = {'fee_pct':13.25,'cost':0.25,'horizon':14,'win_pct':60.0,'risk_free':DEFAULT_RISK_FREE_PCT,
                   'sell_through':0.5,
                   # Selling: TCGplayer takes commission + payment processing as a percentage (fee_pct) plus a fixed fee
                   # per order; you pay outgoing shipping (plain envelope below the threshold, tracked at or above it).
                   'fee_fixed':0.30,'ship_plain':1.00,'ship_tracked':4.50,'ship_threshold':50.0,
                   # Small orders: the buyer pays your shipping rate below the free-shipping threshold (TCGplayer standard).
                   'ship_charge':0.99,'free_ship_from':5.0,
                   'ship_in':0.50,  # inbound shipping you pay per card bought
                   # Position sizing: trading capital, per-card and per-set limits, fraction of the Kelly stake.
                   'capital':5000.0,'max_card':250.0,'max_set_pct':15.0,'kelly':0.25,
                   'min_profit':1.00,  # expected profit per copy below this is not worth handling, so it is not suggested
                   'min_roi':10.0,     # ...nor below this % of the all-in cost (a $40 card needs $4)
                   # Condition: share of the Near Mint price a copy in each condition sells for, and how far below
                   # market the cheapest listing can sit before it is assumed to be a played copy.
                   'cond_LP':0.85,'cond_MP':0.70,'cond_HP':0.55,'cond_DMG':0.40,'played_ratio':0.80}
PRICING_VERSION = 2  # v2 split shipping and the per-order fee out of the per-card cost (was 0.75 all-in)
CONDITIONS = ('NM','LP','MP','HP','DMG')
PLAYED_MIN_GAP = 0.50  # a low within 50¢ of market is listing noise, not evidence of a played copy

def condition_share(pricing, cond):
    """Share of the Near Mint price a copy in this condition sells for."""
    return 1.0 if cond=='NM' else float(pricing.get('cond_'+cond,1.0))

def selling_costs(price, pricing):
    """Per-copy costs of a sale besides the percentage fee: the fixed per-order fee, outgoing shipping
    (tracked at or above the threshold, as TCGplayer requires for larger orders) and supplies, less the
    shipping the buyer pays on orders under the free-shipping threshold (the percentage fee applies to it too)."""
    ship=pricing['ship_tracked'] if price>=pricing['ship_threshold'] else pricing['ship_plain']
    if price<pricing.get('free_ship_from',0.0): ship-=pricing.get('ship_charge',0.0)*(1.0-pricing['fee_pct']/100.0)
    return pricing['fee_fixed']+ship+pricing['cost']

def sale_net(price, pricing):
    """What selling one copy at `price` leaves you after every selling cost."""
    return price*(1.0-pricing['fee_pct']/100.0)-selling_costs(price,pricing)

def implied_condition(low, market, pricing):
    """Most likely condition of the cheapest listing. TCGCSV's low covers every condition: within played_ratio of
    market it is taken as Near Mint; below that, the best condition whose usual discount it matches, rounding
    toward the worse condition so a played copy is never valued as a cleaner one."""
    if not low or not market or low/market>=pricing['played_ratio'] or market-low<=PLAYED_MIN_GAP: return 'NM'
    ratio=low/market
    for cond in CONDITIONS[1:]:
        if condition_share(pricing,cond)<=ratio+0.03: return cond
    return CONDITIONS[-1]

def suggested_quantity(t, buy, value, pricing, held_card=0.0, held_set=0.0, invested=0.0):
    """(copies, binding limit) to buy at `buy` each: the smallest of a fractional-Kelly stake, the per-card and
    per-set capital limits, the remaining budget and the copies likely to sell within the horizon.

    One copy is treated as a bet that sells with probability p_sold at the forecast price (value = the copy's
    Near-Mint-equivalent market price for its condition) and is otherwise held at about break-even. The Kelly
    fraction of capital is mean x cost / variance of that profit; only `kelly` of it is staked because the
    inputs are estimates (quarter-Kelly by default).
    """
    if not t or not buy or buy<=0: return 0,'no price'
    keep=1.0-pricing['fee_pct']/100.0; cost=buy+pricing['ship_in']
    gain=value*(1.0+t['mean_return'])*keep-selling_costs(value,pricing)-cost
    p=t['p_sold']; sd=value*keep*t['sigma_return']
    mu=p*gain; var=p*(sd*sd+gain*gain)-mu*mu
    if mu<=0: return 0,'no edge'
    capital=pricing['capital']
    dollars=[('Kelly',pricing['kelly']*mu*cost/var*capital if var>1e-12 else capital),
             ('card limit',pricing['max_card']-held_card),
             ('set limit',pricing['max_set_pct']/100.0*capital-held_set),
             ('budget',capital-invested)]
    options=[(int(max(0.0,d)//cost),name) for name,d in dollars]
    if t.get('max_qty') is not None: options.append((t['max_qty'],'sell-through'))
    return min(options,key=lambda o:o[0])

QTY_LIMIT_WORDS = {'sell-through':'sales pace','Kelly':'risk sizing','card limit':'per-card cap','set limit':'per-set cap',
                   'budget':'your cash','no edge':'no edge','no price':'no price'}

def portfolio_exposure(positions):
    """Dollars already committed per printing, per set and in total (cost basis, else market), for sizing."""
    cards={}; sets={}; total=0.0
    for p in positions or ():
        if not p.get('qty'): continue
        unit=p['cost'] if p.get('cost') is not None else (p.get('market') or 0.0)
        v=unit*p['qty']; total+=v
        cards[(p['card_id'],p.get('row_type') or p.get('price_type'))]=cards.get((p['card_id'],p.get('row_type') or p.get('price_type')),0.0)+v
        key=(p.get('game'),p.get('set_code')); sets[key]=sets.get(key,0.0)+v
    return {'cards':cards,'sets':sets,'total':total}

def _bucket(value, edges): return bisect.bisect_right(edges,value)  # number of edges at or below value

_VARIANT_NOISE = re.compile(r'^(?:#?\d+[a-z]?|[a-z]|\d+/\d+)$', re.I)

MAJOR_VARIANT_MIN = 500  # printings a treatment needs in the catalog before it gets its own forecast level

def major_variants(variants):
    """Treatments common enough to model separately; rarer ones use the general buckets until they grow."""
    counts={}
    for v in variants:
        if v and v!='Regular': counts[v]=counts.get(v,0)+1
    return frozenset(v for v,n in counts.items() if n>=MAJOR_VARIANT_MIN)

def set_release_days(store):
    """{(game, set code): release date ordinal}. Scryfall dates win; TCGCSV's dates on standing promo groups are only
    'last updated', so those groups get none."""
    out={}
    try:
        for game,code,name,day,source in store.q("SELECT game,code,name,released_on,source FROM set_info WHERE released_on IS NOT NULL ORDER BY source DESC"):
            if source=='tcgcsv' and _PERENNIAL_GROUP.search(name or ''): continue
            o=_day_ordinal(day)
            if o and (game,code) not in out: out[(game,code)]=o
    except sqlite3.OperationalError: pass
    return out

def variant_of(game, name, rarity=''):
    """The printing's treatment, read from TCGplayer's own naming so new treatments are picked up the day a set adds
    them: MTG uses the parenthetical notes ('Borderless', 'Serial Numbered', 'Showcase + Galaxy Foil'); Pokémon the
    rarity plus any notes ('Special Illustration Rare', 'Rare · Cosmos Holo'). Collector numbers and single-letter
    art codes are ignored. 'Regular' when there is nothing."""
    tags=[t.strip() for t in re.findall(r'\(([^)]*)\)',str(name or ''))]
    label=' + '.join(t for t in tags if t and not _VARIANT_NOISE.match(t))
    if game!='MTG':  # Pokémon, One Piece, Riftbound: the rarity names the treatment
        rare=str(rarity or '').strip()
        label=' · '.join(x for x in (rare if rare not in ('','None','Unconfirmed') else '',label) if x)
    return label or 'Regular'


_FORECAST_KEY_CACHE = {}

_LIQ_EDGES = (6,15)  # price-change days in the last 30: thin (<6), active (6-14), liquid (15+)
_VOL_EDGES = (0.01,0.03,0.08)  # sd of daily log returns over 30 days: calm, moderate, volatile, very volatile (~19/57/150%+ a year)
FORECAST_MIN_VOL_RETURNS = 10  # one-day returns needed in the 30-day window before a card's own volatility is used

_PHASE_EDGES = (0,14,42)   # days since the set's release: presale (<0), launch (0-13), slide (14-41), settling (42-90)
PHASE_MATURE_DAYS = 91     # from here a card is priced like any other (no release-phase level)
PHASE_NAMES = ('presale','release to day 14','days 14-42','days 42-90')

def release_phase(age):
    """Release-cycle phase index for a card `age` days after its set's release (negative = presale), None when mature."""
    return None if age is None or age>=PHASE_MATURE_DAYS else _bucket(age,_PHASE_EDGES)

def forecast_keys(r30, r7, price, printing, changes=None, sd=None, variant=None, age=None):
    """Bucket keys from most to least specific; r30/r7 are fractions (0.10 = +10%). Shared, do not mutate.

    changes (days with a price change in the last 30) adds the liquidity tier, and sd (the card's own daily
    return standard deviation over 30 days) the volatility tier, to every level: liquid and volatile printings
    move far more than thin, calm ones, and pooling them gave a 300%-a-year card the range of a stable one.
    age (days since the set's release) adds the release phase for cards under PHASE_MATURE_DAYS old: new cards
    follow a cycle (presale hype, a slide as supply opens, then settling) that mature cards do not.
    """
    sig=(-1 if r30 is None else _bucket(r30,_R30_EDGES),-1 if r7 is None else _bucket(r7,_R7_EDGES),
         _bucket(price,_PRICE_EDGES),'N' if printing in ('','Normal') else 'F',-1 if changes is None else _bucket(changes,_LIQ_EDGES),
         -1 if sd is None else _bucket(sd,_VOL_EDGES),variant if variant not in (None,'','Regular') else '',
         -1 if release_phase(age) is None else release_phase(age))
    keys=_FORECAST_KEY_CACHE.get(sig)
    if keys is None:
        r30b,r7b,tier,kind,liq,vol,treatment,phase=sig; keys=[]
        psfx='' if phase<0 else f'|P{phase}'
        sfx=('' if liq<0 else f'|L{liq}')+('' if vol<0 else f'|V{vol}')+psfx
        # The treatment is the most specific level: a new variant borrows its parents' behaviour (Dirichlet shrinkage)
        # until enough of its own outcomes accumulate, so it adapts as it trades.
        if treatment: keys.append(f'{r30b}|{tier}|{kind}{sfx}|T:{treatment}')
        if r30b>=0:
            if r7b>=0: keys.append(f'{r30b}|{r7b}|{tier}|{kind}{sfx}')
            keys.append(f'{r30b}|{tier}{sfx}')
        keys.append(f't{tier}{sfx}')
        if liq>=0 and vol>=0: keys.append(f'L{liq}|V{vol}{psfx}')
        if liq>=0:
            if psfx: keys.append(f'L{liq}{psfx}')
            keys.append(f'L{liq}')
        elif vol>=0: keys.append(f'V{vol}')
        if psfx and liq<0: keys.append(f'P{phase}')
        keys.append('all')
        keys=_FORECAST_KEY_CACHE[sig]=tuple(keys)
    return keys

def _days_by_closeness(day, tolerance):
    """Day ordinals around `day` (a date), nearest first."""
    o=day.toordinal()
    return [o+d for d in sorted(range(-tolerance,tolerance+1),key=abs)]

def build_forecast_model(store, horizon, latest_day, progress=None):
    return build_forecast_models(store,(horizon,),latest_day,progress)[horizon]

def build_forecast_models(store, horizons, latest_day, progress=None):
    """Learn forward-return distributions for each horizon from one pass over the last FORECAST_LOOKBACK_DAYS.

    Per horizon: anchors in the newest FORECAST_TEST_SPAN days form the test set; only anchors whose outcome
    falls before that window train the backtest model, so the reported accuracy is out of sample. The test
    set is split by time: an isotonic calibration map is fitted on its older half and kept only if it lowers
    the Brier score on the newer half (it corrects regime drift, e.g. a market that has turned down). The
    final model uses every anchor plus a calibration map fitted on the whole test set.
    """
    if isinstance(latest_day,str): latest_day=datetime.strptime(latest_day[:10],'%Y-%m-%d').date()
    releases=set_release_days(store)
    valid={card_key(cid):(variant_of(game,name,rarity),releases.get((game,code))) for cid,game,name,rarity,code in
           store.q("SELECT id,game,name,rarity,set_code FROM cards WHERE game IN ('MTG','Pokémon','One Piece','Riftbound') AND item_type='card'")}
    flush,finish=_forecast_collector(horizons,latest_day,major_variants(v for v,_r in valid.values())); cards=0
    for key,series in iter_daily_cards(store,latest_day.toordinal()-FORECAST_LOOKBACK_DAYS):
        if key not in valid: continue
        cards+=1
        if progress and cards%5000==0: progress(cards,0,f'Building forecast models: {cards:,} cards read')
        flush({printing:dict(parts[0]) for printing,parts in series.items()},*valid[key])
    return finish()

def build_market_views(store, risk_free, latest_day, horizons=FORECAST_HORIZONS, progress=None, pricing=None):
    """Rankings, indices, every forecast horizon and (given pricing) the strategy backtest from ONE pass over
    the price history (the daily precompute). Returns (data, models, backtest).

    latest_day is the expected newest price day (the synced dataset's date). If the scan finds a different
    newest day the models are dropped (None) and built separately, so they always match the rankings.
    """
    if isinstance(latest_day,str): latest_day=datetime.strptime(latest_day[:10],'%Y-%m-%d').date()
    variants=major_variants(variant_of(game,name,rarity) for game,name,rarity in
                            store.q("SELECT game,name,rarity FROM cards WHERE game IN ('MTG','Pokémon','One Piece','Riftbound') AND item_type='card'"))
    flush,finish=_forecast_collector(horizons,latest_day,variants)
    strategy=_strategy_collector(int(pricing['horizon']),latest_day,variants) if pricing else None
    def on_card(_cid,series,variant=None,release=None):
        flush({printing:dict(parts[0]) for printing,parts in series.items()},variant,release)
        if strategy: strategy[0](series,variant,release)
    data=build_market_rankings(store,progress=progress,risk_free=risk_free,
                               scan_days=BACKTEST_LOOKBACK_DAYS if pricing else FORECAST_LOOKBACK_DAYS,on_card=on_card)
    dates=[r['latest_date'] for r in data['fresh'] if r.get('latest_date')]
    current=bool(dates) and max(dates)==latest_day.isoformat()
    return data,(finish() if current else None),(strategy[1](pricing) if strategy and current else None)

def _return_prefix(days, prices):
    """Prefix (count, sum, sum of squares) of one-day log returns, indexed by the later day's position in days."""
    cnt=[0]; s1=[0.0]; s2=[0.0]
    for d0,d1 in zip(days,days[1:]):
        if d1-d0==1 and prices[d0]>0 and prices[d1]>0:
            r=math.log(prices[d1]/prices[d0]); cnt.append(cnt[-1]+1); s1.append(s1[-1]+r); s2.append(s2[-1]+r*r)
        else: cnt.append(cnt[-1]); s1.append(s1[-1]); s2.append(s2[-1])
    return cnt,s1,s2

def _window_sd(prefix, i0, i1):
    """Sample sd of the one-day returns with both days among days[i0:i1] (None below FORECAST_MIN_VOL_RETURNS)."""
    cnt,s1,s2=prefix
    if i1-i0<2: return None
    n=cnt[i1-1]-cnt[i0]
    if n<FORECAST_MIN_VOL_RETURNS: return None
    t=s1[i1-1]-s1[i0]; tt=s2[i1-1]-s2[i0]
    return math.sqrt(max(0.0,(tt-t*t/n)/(n-1)))

def _near_price(prices, o, tolerance):
    """Price on day ordinal o, else the nearest day within tolerance (earlier first on ties); None if none."""
    p=prices.get(o)
    if p: return p
    for d in range(1,tolerance+1):
        p=prices.get(o-d) or prices.get(o+d)
        if p: return p
    return None

def _forecast_collector(horizons, latest_day, variants=frozenset()):
    """(flush(series), finish() -> {horizon: model}) for streaming price series into the forecast models.

    All horizons share one grid of anchor days (every FORECAST_STEP_DAYS days), so each anchor's features -
    price, 30/7-day change and bucket - are computed once. Outcomes are counted only in the most specific
    bucket; finish() adds them up the bucket chain, which is the same as counting every level as it goes.
    """
    latest=latest_day.toordinal(); grid={}
    for horizon in horizons:
        first=-(-horizon//FORECAST_STEP_DAYS)*FORECAST_STEP_DAYS
        for offset in range(first,FORECAST_LOOKBACK_DAYS-33,FORECAST_STEP_DAYS):
            role=(('new' if offset<horizon+FORECAST_TEST_SPAN//2 else 'old') if offset<horizon+FORECAST_TEST_SPAN
                  else 'train' if offset>=2*horizon+FORECAST_TEST_SPAN else None)
            grid.setdefault(latest-offset,[]).append((horizon,role))
    plan=sorted(grid.items()); plan_days=[a for a,_t in plan]; chains={}
    leaf_hist={h:{} for h in horizons}; leaf_train={h:{} for h in horizons}; tests={h:{} for h in horizons}

    def flush(series, variant=None, release=None):
        if variant not in variants: variant=None
        for printing,prices in series.items():
            if not prices or max(prices.values())<FORECAST_MIN_PRICE: continue
            days=sorted(prices); changes=[0]; vol=_return_prefix(days,prices)
            for d0,d1 in zip(days,days[1:]): changes.append(changes[-1]+(abs(prices[d1]-prices[d0])>1e-9))
            for a,targets in plan[bisect.bisect_left(plan_days,days[0]+27):bisect.bisect_right(plan_days,days[-1]+1)]:
                p0=_near_price(prices,a,1)
                if not p0 or p0<FORECAST_MIN_PRICE: continue
                p30=_near_price(prices,a-30,3)
                if not p30: continue
                p7=_near_price(prices,a-7,2)
                if not p7: continue
                i0=bisect.bisect_left(days,a-29); i1=bisect.bisect_right(days,a)
                keys=forecast_keys(p0/p30-1.0,p0/p7-1.0,p0,printing,changes[i1-1]-changes[i0] if i1>i0 else 0,
                                   _window_sd(vol,i0,i1),variant,None if release is None else a-release); leaf=keys[0]
                if leaf not in chains: chains[leaf]=keys
                for horizon,role in targets:
                    ph=_near_price(prices,a+horizon,2)
                    if not ph: continue
                    r=ph/p0-1.0; b=int(round(max(-0.95,min(10.0,r))/_FORECAST_BIN))
                    h=leaf_hist[horizon].get(leaf)
                    if h is None: h=leaf_hist[horizon][leaf]={}
                    h[b]=h.get(b,0)+1
                    if role:
                        bucket=leaf_train[horizon] if role=='train' else tests[horizon]
                        k=leaf if role=='train' else (keys,role)
                        e=bucket.get(k)
                        if e is None: e=bucket[k]=[0,0,{}]
                        e[0]+=1; e[1]+=r>0; e[2][b]=e[2].get(b,0)+1

    def finish():
        models={}
        for horizon in horizons:
            hist={}; train={}; train_hist={}
            for leaf,counts in leaf_hist[horizon].items():
                for k in chains[leaf]:
                    t=hist.setdefault(k,{})
                    for b,c in counts.items(): t[b]=t.get(b,0)+c
            for leaf,(n,up,bins) in leaf_train[horizon].items():
                for k in chains[leaf]:
                    e=train.setdefault(k,[0,0]); e[0]+=n; e[1]+=up
                    t=train_hist.setdefault(k,{})
                    for b,c in bins.items(): t[b]=t.get(b,0)+c
            # Where did each held-out outcome land in the forecast of the train-only model? (PIT values)
            train_model={'horizon':horizon,'variants':sorted(variants),
                         'buckets':{k:{'n':sum(h.values()),'bins':sorted([b,c] for b,c in h.items())} for k,h in train_hist.items()}}
            pit={'old':{},'new':{}}
            for (keys,role),(_n,_up,bins) in tests[horizon].items():
                chain=tuple(k for k in keys if (train_model['buckets'].get(k) or {}).get('n'))
                if chain: pit[role].setdefault(_tier_of(keys),[]).extend(_pit_values(_blended_forecast(train_model,chain),bins))
            backtest,cal_map=_backtest_forecast(train,{k:(v[0],v[1]) for k,v in tests[horizon].items()},pit)
            buckets={k:{'n':sum(h.values()),'bins':sorted([b,c] for b,c in h.items())} for k,h in hist.items()}
            models[horizon]={'version':FORECAST_MODEL_VERSION,'horizon':horizon,'data_date':latest_day.isoformat(),'built_at':utc(),
                             'samples':buckets.get('all',{}).get('n',0),'buckets':buckets,'backtest':backtest,
                             'calibration_map':cal_map,'variants':sorted(variants)}
        return models
    return flush,finish

def _pit_values(fc, outcome_bins):
    """[(u, count)]: for each realized outcome bin, the forecast's chance of a higher return (plus half the chance of
    that very bin). If the forecast distribution is calibrated these PIT values are uniform on [0, 1]."""
    fc=_prepare_forecast(fc); values,cum,total=fc['values'],fc['cum'],fc['total']; out=[]
    for b,c in outcome_bins.items():
        i=bisect.bisect_left(values,b); below=cum[i-1] if i else 0.0
        at=(cum[i]-below) if i<len(values) and values[i]==b else 0.0
        out.append(((total-below-0.5*at)/total,c))
    return out

def pit_calibration(pits, points=40):
    """Recalibration map of a whole forecast distribution (Kuleshov et al. 2018): knots [[s, g(s)]] of the
    empirical CDF of PIT values, so the calibrated chance of beating any threshold is g(raw chance). Unlike a
    fit at one threshold (price up or not), this corrects the tails that Max buy and the price ranges use."""
    pits=sorted(pits); total=sum(c for _u,c in pits)
    if total<100: return None
    knots=[[0.0,0.0]]; run=0.0; j=0
    for k in range(1,points):
        s=k/points
        while j<len(pits) and pits[j][0]<s: run+=pits[j][1]; j+=1
        if run/total>=knots[-1][1]: knots.append([s,run/total])
    knots.append([1.0,1.0])
    return knots

def _tier_of(keys):
    """Liquidity tier key ('L0', 'L1', 'L2') in a bucket chain, '*' when the chain has none."""
    return next((k for k in keys if len(k)==2 and k[0]=='L' and k[1].isdigit()),'*')

def fit_tiered_calibration(old, new):
    """Distribution recalibration per liquidity tier: {tier: knots} for each tier whose map, fitted on its older
    outcomes, makes its newer PIT values more uniform (the final map uses both halves); plus the per-tier maps
    fitted on the older half only, for scoring. old/new: {tier: [(u, n)]}."""
    final={}; fitted={}
    for tier in set(old)|set(new):
        o=old.get(tier,[]); n=new.get(tier,[])
        f=pit_calibration(o) if o else None
        if f and n and pit_error(n,f)<pit_error(n):
            fitted[tier]=f; final[tier]=pit_calibration(o+n)
    return final,fitted

def pit_error(pits, knots=None):
    """Mean distance between the CDF of (recalibrated) PIT values and the uniform one: 0 = perfectly calibrated."""
    mapped=sorted((apply_calibration(knots,u) if knots else u,c) for u,c in pits); total=sum(c for _u,c in mapped)
    if not total: return None
    err=0.0; run=0.0; j=0
    for k in range(1,20):
        s=k/20
        while j<len(mapped) and mapped[j][0]<s: run+=mapped[j][1]; j+=1
        err+=abs(run/total-s)
    return err/19

def _backtest_forecast(train, test, pit=None):
    """Out-of-sample Brier scores and the calibration map; test is {(keys, 'old'|'new'): [n, rises]}.

    With pit ({'old': {tier: [(u, n)]}, 'new': {...}}) the map recalibrates the whole distribution separately for
    each liquidity tier (fit_tiered_calibration), fitted on the older half and kept only where it makes the newer
    half's PIT values more uniform; without it, an isotonic fit of the chance of a rise."""
    base_n,base_up=train.get('all',(0,0))
    if not base_n or not test: return None,None
    base=base_up/base_n; groups=[]
    tiers=[]
    for (keys,half),(tn,tup) in test.items():
        p=base  # same shrinkage as forecast_for: broadest bucket first, each narrower one pulled toward it
        for k in reversed(keys[:-1]):
            kn,kup=train.get(k,(0,0))
            if kn: p=(kup+FORECAST_PRIOR*p)/(kn+FORECAST_PRIOR)
        groups.append((p,tn,tup,half)); tiers.append(_tier_of(keys))
    brier=lambda rows,f: sum(up*(1-f(p))**2+(n-up)*f(p)**2 for p,n,up,_h in rows)/max(1,sum(n for _p,n,_u,_h in rows))
    n=sum(g[1] for g in groups); identity=lambda p:p
    brier_model=brier(groups,identity); brier_base=brier(groups,lambda _p:base)
    calibration={}
    for p,tn,tup,_h in groups:
        c=calibration.setdefault(min(9,int(p*10)),[0,0,0.0]); c[0]+=tn; c[1]+=tup; c[2]+=p*tn
    old=[g for g in groups if g[3]=='old']; new=[g for g in groups if g[3]=='new']
    recent=None; use_map=False; cal_map=None
    if pit and pit.get('old') and pit.get('new'):
        final,fitted=fit_tiered_calibration(pit['old'],pit['new'])
        raw_new=[g for pits in pit['new'].values() for g in pits]
        mapped=[(apply_calibration(fitted.get(t),u),c) for t,pits in pit['new'].items() for u,c in pits]
        new_t=[(g,t) for g,t in zip(groups,tiers) if g[3]=='new']
        cal_brier=sum(up*(1-apply_calibration(fitted.get(t),p))**2+(n-up)*apply_calibration(fitted.get(t),p)**2
                      for (p,n,up,_h),t in new_t)/max(1,sum(g[1] for g,_t in new_t))
        recent={'raw':brier(new,identity),'calibrated':cal_brier,'baseline':brier(new,lambda _p:base),
                'samples':sum(g[1] for g in new),'pit_raw':pit_error(raw_new),'pit_calibrated':pit_error(mapped),
                'tiers_calibrated':sorted(final)}
        use_map=bool(final); cal_map=final or None
    elif old and new:
        fitted=isotonic_calibration((p,tn,tup) for p,tn,tup,_h in old)
        recent={'raw':brier(new,identity),'calibrated':brier(new,lambda p:apply_calibration(fitted,p)),
                'baseline':brier(new,lambda _p:base),'samples':sum(g[1] for g in new)}
        use_map=recent['calibrated']<recent['raw']
        cal_map=isotonic_calibration((p,tn,tup) for p,tn,tup,_h in groups) if use_map else None
    return {'train_samples':base_n,'test_samples':n,'base_rate':base,
            'brier_model':brier_model,'brier_baseline':brier_base,
            'brier_skill':1.0-brier_model/brier_base if brier_base>0 else None,
            'recent_half':recent,'calibrated':use_map,
            'calibration':[[i/10,(i+1)/10,c[0],c[2]/c[0],c[1]/c[0]] for i,c in sorted(calibration.items())]},cal_map

def isotonic_calibration(groups):
    """Weighted pool-adjacent-violators fit of outcome rate on predicted probability.

    groups yields (predicted p, cases, rises). Returns increasing knots [[p, rate], ...] anchored at
    (0, 0) and (1, 1), interpolated linearly by apply_calibration.
    """
    pooled={}
    for p,n,up in groups:
        e=pooled.setdefault(round(p,2),[0.0,0,0]); e[0]+=p*n; e[1]+=n; e[2]+=up
    blocks=[]
    for k in sorted(pooled):
        if not pooled[k][1]: continue
        blocks.append(list(pooled[k]))
        while len(blocks)>1 and blocks[-2][2]/blocks[-2][1]>=blocks[-1][2]/blocks[-1][1]:
            b=blocks.pop(); a=blocks[-1]; a[0]+=b[0]; a[1]+=b[1]; a[2]+=b[2]
    knots=[[0.0,0.0]]
    for sp,n,up in blocks:
        p,rate=sp/n,up/n
        if 0<p<1 and p>knots[-1][0] and rate>=knots[-1][1]: knots.append([p,rate])
    if knots[-1][1]<=1.0: knots.append([1.0,1.0])
    return knots

def _calibration_xy(knots):
    return None if not knots else ([k[0] for k in knots],[k[1] for k in knots])

def _apply_xy(xy, p):
    xs,ys=xy; i=bisect.bisect_left(xs,p)
    if i<=0: return ys[0]
    if i>=len(xs): return ys[-1]
    x0,x1=xs[i-1],xs[i]
    return ys[i-1]+(p-x0)*(ys[i]-ys[i-1])/(x1-x0) if x1>x0 else ys[i]

def _invert_xy(xy, y):
    xs,ys=xy; i=bisect.bisect_left(ys,y)
    if i<=0: return xs[0]
    if i>=len(xs): return 1.0
    y0,y1=ys[i-1],ys[i]
    return xs[i-1] if y1<=y0 else xs[i-1]+(y-y0)*(xs[i]-xs[i-1])/(y1-y0)

def apply_calibration(knots, p):
    return p if not knots else _apply_xy(_calibration_xy(knots),p)

def invert_calibration(knots, y):
    """Smallest raw probability whose calibrated value reaches y."""
    return y if not knots else _invert_xy(_calibration_xy(knots),y)

def forecast_model_path(horizon): return ROOT/f'forecast_model_{horizon}d.json'

def load_forecast_model(horizon, data_date):
    path=forecast_model_path(horizon)
    try:
        model=json.loads(path.read_text(encoding='utf-8'))
        return model if (model.get('horizon')==horizon and model.get('data_date')==data_date
                         and model.get('version')==FORECAST_MODEL_VERSION) else None
    except (OSError,ValueError):
        return None

def save_forecast_model(model):
    path=forecast_model_path(model['horizon']); tmp=path.with_suffix('.json.partial')
    tmp.write_text(json.dumps({k:v for k,v in model.items() if not k.startswith('_')}),encoding='utf-8'); tmp.replace(path)

# --- Strategy backtest: replay the buy rules walk-forward on past prices, after every cost ---
BACKTEST_VERSION = 6
BACKTEST_LOOKBACK_DAYS = 400   # all the history kept (MTGJSON gives ~90 days; daily syncs add more)
BACKTEST_MIN_TRAIN = 5000      # past outcomes needed before a test day is traded
BACKTEST_MIN_PRICE = RANK_MIN_PRICE
BACKTEST_SAMPLE_EVERY = 3      # trade a fixed 1-in-3 sample of test cases (the model still learns from all of them)
BACKTEST_STEP_DAYS = 6         # replay every 6th day: thousands of test trades either way, at half the work

def _strategy_collector(horizon, latest_day, variants=frozenset()):
    """(on_series(series), finish(pricing)) collecting walk-forward test cases for the strategy backtest.

    Anchors every FORECAST_STEP_DAYS days. Each anchor's outcomes go into its own forecast histogram, so the
    model used on test day t is built only from anchors whose outcome was known by t (a + horizon <= t):
    nothing from the future leaks in. Test cases keep what a trader knew on day t (price, 30/7-day change,
    liquidity, cheapest listing if one was recorded) and what happened by t + horizon.
    """
    latest=latest_day.toordinal()
    anchors=list(range(latest-horizon,latest-BACKTEST_LOOKBACK_DAYS+30,-BACKTEST_STEP_DAYS))[::-1]
    hist={a:{} for a in anchors}; cases={a:[] for a in anchors}; chains={}; seen=[0]
    near=_near_price

    def on_series(series, variant=None, release=None):
        if variant not in variants: variant=None
        for printing,(market,lows,_buylist,_eu) in series.items():
            if len(market)<20 or max(v for _o,v in market)<FORECAST_MIN_PRICE: continue
            prices=dict(market); days=[o for o,_ in market]; vol=_return_prefix(days,prices)
            changes=[0]
            for (_o0,p0),(_o1,p1) in zip(market,market[1:]): changes.append(changes[-1]+(abs(p1-p0)>1e-9))
            low_by_day=dict(lows)
            # Only anchors this printing's own history can score (30 days back, one horizon ahead).
            for a in anchors[bisect.bisect_left(anchors,days[0]+27):bisect.bisect_right(anchors,days[-1]-horizon+2)]:
                p0=near(prices,a,1)
                if not p0 or p0<FORECAST_MIN_PRICE: continue
                ph=near(prices,a+horizon,2); p30=near(prices,a-30,3); p7=near(prices,a-7,2)
                if not (ph and p30 and p7): continue
                r=ph/p0-1.0; r30=p0/p30-1.0; r7=p0/p7-1.0
                i0=bisect.bisect_left(days,a-29); i1=bisect.bisect_right(days,a)
                n_changes=changes[i1-1]-changes[i0] if i1>i0 else 0; sd=_window_sd(vol,i0,i1); age=None if release is None else a-release
                keys=forecast_keys(r30,r7,p0,printing,n_changes,sd,variant,age); leaf=keys[0]
                if leaf not in chains: chains[leaf]=keys
                b=int(round(max(-0.95,min(10.0,r))/_FORECAST_BIN)); e=hist[a].get(leaf)  # leaf only; summed up the chain later
                if e is None: e=hist[a][leaf]={}
                e[b]=e.get(b,0)+1
                if p0>=BACKTEST_MIN_PRICE and n_changes>=2:
                    seen[0]+=1
                    if seen[0]%BACKTEST_SAMPLE_EVERY==0:
                        cases[a].append((printing,r30*100,r7*100,p0,ph,n_changes,low_by_day.get(a),sd,variant,age))

    def finish(pricing):
        return _run_strategies(anchors,hist,cases,horizon,latest_day,pricing,chains,variants)
    return on_series,finish

def _promise_table(promises):
    """Promised vs realized, by liquidity: [[label, trades, promised win, realized win, expected $/copy, realized $/copy], ...]."""
    groups={}
    for promise,changes,won,expected,pnl in promises:
        label='15+ trading days' if changes>=15 else '6–14 trading days' if changes>=6 else '2–5 trading days'
        g=groups.setdefault(label,[0,0.0,0,0.0,0.0]); g[0]+=1; g[1]+=promise; g[2]+=won; g[3]+=expected; g[4]+=pnl
    order=('15+ trading days','6–14 trading days','2–5 trading days')
    return [[k,g[0],g[1]/g[0],g[2]/g[0],g[3]/g[0],g[4]/g[0]] for k in order if (g:=groups.get(k))]

def _model_from_hist(total, horizon, variants=frozenset()):
    return {'horizon':horizon,'variants':sorted(variants),'buckets':{k:{'n':sum(h.values()),'bins':sorted([b,c] for b,c in h.items())} for k,h in total.items()}}

def _run_strategies(anchors, hist, cases, horizon, latest_day, pricing, chains=None, variants=frozenset()):
    """Trade every test day with the model known then, and score each strategy on what really happened.
    hist[a] holds each anchor's outcome counts by most specific bucket; chains maps that bucket to its parents.

    The model is recalibrated walk-forward like the live one: each anchor's outcomes are placed in the forecast of
    that day (PIT values), and on test day t a distribution recalibration is fitted on those whose outcomes were
    known by t (the last FORECAST_TEST_SPAN days of them), kept only if it makes the newer half more uniform.
    """
    ship_in=pricing['ship_in']; total={}; pending=list(anchors); results={}; known=[]
    chains=chains or {}
    names=('Buy-ins at Max buy · this model','Buy-ins at Max buy · no-skill forecast','Buy now at cheapest listing · this model',
           'Buy every card at market · no model')
    for name in names: results[name]={'trades':[],'pred':0.0,'promises':[]}
    for a in anchors:
        while pending and pending[0]+horizon<=a:  # outcome known by day a
            for leaf,h in hist[pending.pop(0)].items():
                for k in chains.get(leaf,(leaf,)):
                    t=total.setdefault(k,{})
                    for b,c in h.items(): t[b]=t.get(b,0)+c
        model=_model_from_hist(total,horizon,variants) if total.get('all') else None
        if model and hist[a]:
            # Where today's outcomes will land in today's forecast (PIT values), used once they are known.
            pits={}
            for leaf,h in hist[a].items():
                chain=tuple(k for k in chains.get(leaf,(leaf,)) if (model['buckets'].get(k) or {}).get('n'))
                if chain: pits.setdefault(_tier_of(chain),[]).extend(_pit_values(_blended_forecast(model,chain),h))
            known.append((a,pits))
        if not cases[a] or not model or model['buckets']['all']['n']<BACKTEST_MIN_TRAIN: continue
        flat={'horizon':horizon,'buckets':{'all':model['buckets']['all']}}
        window=[(b,pr) for b,pr in known if b+horizon<=a and b>=a-horizon-FORECAST_TEST_SPAN]
        if len(window)>=2:
            mid=window[len(window)//2][0]; old={}; new={}
            for b,pr in window:
                for tier,pits in pr.items(): (old if b<mid else new).setdefault(tier,[]).extend(pits)
            final,_fitted=fit_tiered_calibration(old,new)
            if final:
                model['calibration_map']=final; model.pop('_cal',None); model.pop('_prepared',None)
        sell_day=date.fromordinal(a+horizon).isoformat()
        for printing,r30,r7,p0,ph,n_changes,low0,sd,variant,age in cases[a]:
            proceeds=sale_net(ph,pricing)
            results[names[3]]['trades'].append((sell_day,proceeds-(p0+ship_in),p0+ship_in)); results[names[3]]['pred']+=0.0
            for name,mdl in ((names[0],model),(names[1],flat)):
                fc=forecast_for(mdl,r30,r7,p0,printing,n_changes,sd,variant,age)
                t=pricing_targets(p0,low0,fc,pricing,n_changes) if fc else None
                if not t: continue
                if t['max_buy'] and worth_it(t['exp_sale_net']-(t['max_buy']+ship_in),t['max_buy']+ship_in,pricing):
                    promise=t['profit_at_max_buy']; pnl=proceeds-(t['max_buy']+ship_in)
                    results[name]['trades'].append((sell_day,pnl,t['max_buy']+ship_in))
                    results[name]['pred']+=promise
                    results[name]['promises'].append((promise,n_changes,pnl>0,t['exp_sale_net']-(t['max_buy']+ship_in),pnl))
                if name==names[0] and low0:
                    cond=t['low_cond']; limit=t['max_buy_cond'].get(cond)
                    if limit and low0<=limit and worth_it(t['exp_sale_net_low']-(low0+ship_in),low0+ship_in,pricing):
                        sold=sale_net(ph*condition_share(pricing,cond),pricing)
                        results[names[2]]['trades'].append((sell_day,sold-(low0+ship_in),low0+ship_in))
                        promise=t['win_at_low']/t['p_sold'] if t['p_sold'] else 0.0
                        results[names[2]]['pred']+=promise
                        results[names[2]]['promises'].append((promise,n_changes,sold>low0+ship_in,t['exp_sale_net_low']-(low0+ship_in),sold-(low0+ship_in)))
    out={}
    for name in names:
        trades=results[name]['trades']
        if not trades: out[name]=None; continue
        by_day={}
        for day,pnl,cost in trades: by_day[day]=by_day.get(day,0.0)+pnl
        curve=[]; run=peak=dd=0.0
        for day in sorted(by_day):
            run+=by_day[day]; peak=max(peak,run); dd=min(dd,run-peak); curve.append([day,round(run,2)])
        cost=sum(c for _d,_p,c in trades); pnl=sum(p for _d,p,_c in trades); wins=sum(1 for _d,p,_c in trades if p>0)
        out[name]={'trades':len(trades),'win_rate':wins/len(trades),'pred_win':results[name]['pred']/len(trades) if name!=names[3] else None,
                   'avg_pnl':pnl/len(trades),'total_pnl':pnl,'roi':pnl/cost if cost else None,'max_drawdown':dd,'curve':curve,
                   'win_ci':wilson_interval(wins/len(trades),len(trades)/max(1.0,horizon/BACKTEST_STEP_DAYS)),
                   'by_promise':_promise_table(results[name]['promises'])}
    days=sorted({d for r in out.values() if r for d,_v in r['curve']})
    return {'version':BACKTEST_VERSION,'horizon':horizon,'data_date':latest_day.isoformat(),'built_at':utc(),
            'sell_days':[days[0],days[-1]] if days else None,'strategies':out,
            'pricing':{k:pricing[k] for k in ('fee_pct','fee_fixed','ship_plain','ship_tracked','ship_threshold','ship_charge',
                                              'free_ship_from','ship_in','cost','win_pct','sell_through','min_profit','min_roi')}}

def run_strategy_backtest(reader, pricing, latest_day, progress=None):
    """Separate scan for the backtest (when the rankings were loaded from cache)."""
    if isinstance(latest_day,str): latest_day=datetime.strptime(latest_day[:10],'%Y-%m-%d').date()
    releases=set_release_days(reader)
    valid={card_key(cid):(variant_of(game,name,rarity),releases.get((game,code))) for cid,game,name,rarity,code in
           reader.q("SELECT id,game,name,rarity,set_code FROM cards WHERE game IN ('MTG','Pokémon','One Piece','Riftbound') AND item_type='card'")}
    on_series,finish=_strategy_collector(int(pricing['horizon']),latest_day,major_variants(v for v,_r in valid.values())); n=0
    for key,series in iter_daily_cards(reader,latest_day.toordinal()-BACKTEST_LOOKBACK_DAYS):
        if key in valid:
            on_series(series,*valid[key]); n+=1
            if progress and n%5000==0: progress(n,0,f'Strategy backtest: {n:,} cards replayed')
    return finish(pricing)

def backtest_path(): return ROOT/'strategy_backtest.json'

def save_backtest(result):
    path=backtest_path(); tmp=path.with_suffix('.partial'); tmp.write_text(json.dumps(result),encoding='utf-8'); tmp.replace(path)

def load_backtest(data_date=None, pricing=None):
    """The saved backtest if it matches the data date and the cost/target assumptions (None otherwise)."""
    try: result=json.loads(backtest_path().read_text(encoding='utf-8'))
    except (OSError,ValueError): return None
    if result.get('version')!=BACKTEST_VERSION or (data_date and result.get('data_date')!=data_date): return None
    if pricing and (result.get('horizon')!=int(pricing['horizon']) or
                    any(abs(float(result['pricing'].get(k,0))-float(pricing.get(k,0)))>1e-9 for k in result.get('pricing',{}))): return None
    return result

def stored_pricing(store):
    pricing=dict(DEFAULT_PRICING)
    for key in DEFAULT_PRICING:
        try: pricing[key]=float(store.get_setting('pricing_'+key,DEFAULT_PRICING[key]))
        except ValueError: pass
    pricing['horizon']=int(pricing['horizon'])
    return pricing

# --- Trade log: what you actually bought and sold, realized P/L, and settings learned from it ---
TRADE_PRIOR = 5  # pseudo-trades pulling each learned setting toward its current value

def record_trade(store, card_id, price_type, side, qty, price, condition='NM', fees=None, shipping=None,
                 traded_on=None, market=None, predicted_profit=None, predicted_win=None, note='', changes=None):
    """Log a buy or sell and keep the portfolio position in step (average-cost basis, inbound shipping included)."""
    side=side.upper(); qty=int(qty)
    if side not in ('BUY','SELL') or qty<=0 or price is None or price<0: raise ValueError('side BUY/SELL, quantity ≥ 1, price ≥ 0')
    if condition not in CONDITIONS: raise ValueError('condition must be one of '+', '.join(CONDITIONS))
    held=store.q('SELECT qty,cost FROM portfolio WHERE card_id=? AND price_type=?',(card_id,price_type))
    old_qty,old_cost=(held[0][0] or 0,held[0][1]) if held else (0,None)
    if side=='SELL' and qty>old_qty: raise ValueError(f'you hold {old_qty} of this printing in the portfolio')
    store.execute("""INSERT INTO trades(card_id,price_type,side,qty,price,condition,fees,shipping,traded_on,market,
                     predicted_profit,predicted_win,note,created_at,changes) VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)""",
                  (card_id,price_type,side,qty,price,condition,fees,shipping,traded_on or date.today().isoformat(),market,
                   predicted_profit,predicted_win,note,utc(),changes))
    if side=='BUY':
        new_qty=old_qty+qty; unit=price+(shipping or 0.0)/qty
        cost=unit if not old_qty or old_cost is None else (old_qty*old_cost+qty*unit)/new_qty
        store.execute("""INSERT INTO portfolio(card_id,price_type,qty,cost,added_at) VALUES(?,?,?,?,?)
                         ON CONFLICT(card_id,price_type) DO UPDATE SET qty=excluded.qty,cost=excluded.cost""",
                      (card_id,price_type,new_qty,cost,utc()))
    else:
        store.execute('UPDATE portfolio SET qty=? WHERE card_id=? AND price_type=?',(old_qty-qty,card_id,price_type))

def trade_ledger(trades):
    """Realized results per sale on an average-cost basis, in date order.

    trades: dicts with card_id, price_type, side, qty, price, fees, shipping, traded_on, predicted_profit.
    Returns {'sales': [...], 'open': {printing: (qty, avg cost)}} where each sale has proceeds, cost basis,
    realized P/L, days held (from the average buy date) and the profit predicted when the copies were bought.
    """
    book={}; sales=[]
    for t in sorted(trades,key=lambda t:(t['traded_on'],t.get('id') or 0)):
        key=(t['card_id'],t['price_type']); qty,cost,day_sum,pred,chg,chg_n=book.get(key,(0,0.0,0.0,0.0,0.0,0))
        o=date.fromisoformat(t['traded_on'][:10]).toordinal()
        if t['side']=='BUY':
            unit=t['price']+(t.get('shipping') or 0.0)/t['qty']
            known=t.get('changes') is not None
            book[key]=(qty+t['qty'],cost+unit*t['qty'],day_sum+o*t['qty'],pred+(t.get('predicted_profit') or 0.0)*t['qty'],
                       chg+(t['changes']*t['qty'] if known else 0.0),chg_n+(t['qty'] if known else 0))
        elif qty>0:
            n=min(qty,t['qty']); avg=cost/qty
            proceeds=t['price']*n-(t.get('fees') or 0.0)-(t.get('shipping') or 0.0)
            sales.append({'card_id':t['card_id'],'price_type':t['price_type'],'qty':n,'proceeds':proceeds,'basis':avg*n,
                          'pnl':proceeds-avg*n,'days_held':o-day_sum/qty,'predicted':pred/qty*n,'traded_on':t['traded_on'],
                          'condition':t.get('condition'),'price':t['price'],'market':t.get('market'),
                          'fees':t.get('fees'),'shipping':t.get('shipping'),'changes':chg/chg_n if chg_n else None})
            share=n/qty
            book[key]=(qty-n,cost-avg*n,day_sum-day_sum*share,pred-pred*share,chg-chg*share,chg_n-chg_n*share)
    return {'sales':sales,'open':{k:(v[0],v[1]/v[0] if v[0] else None) for k,v in book.items() if v[0]}}

def learn_from_trades(trades, pricing):
    """Settings suggested by your own trades, each shrunk toward the current value with TRADE_PRIOR pseudo-trades.

    Condition shares: sale price ÷ the market price recorded at the sale, per condition, relative to Near Mint.
    Fee %: fees ÷ sale value. Shipping: outgoing per sale and inbound per card bought. Sell-through: copies sold per
    trading day, from how long your copies took to sell given how actively each card traded when you bought it.
    Returns {setting: (suggested value, trades used)} for settings with at least one trade.
    """
    shrink=lambda values,current: (sum(values)+TRADE_PRIOR*current)/(len(values)+TRADE_PRIOR)
    out={}
    sells=[t for t in trades if t['side']=='SELL']; buys=[t for t in trades if t['side']=='BUY']
    ratios={}
    for t in sells:
        if t.get('market') and t['market']>0: ratios.setdefault(t.get('condition') or 'NM',[]).append(t['price']/t['market'])
    nm=shrink(ratios['NM'],1.0) if ratios.get('NM') else 1.0  # NM may itself sell above or below "market"
    for cond in CONDITIONS[1:]:
        if ratios.get(cond):
            out['cond_'+cond]=(round(min(1.0,shrink([r/nm for r in ratios[cond]],pricing['cond_'+cond])),3),len(ratios[cond]))
    fee=[(t['fees'] or 0.0)/(t['price']*t['qty'])*100 for t in sells if t.get('fees') is not None and t['price']>0]
    if fee: out['fee_pct']=(round(shrink(fee,pricing['fee_pct']),2),len(fee))
    ship=[(t['shipping'] or 0.0) for t in sells if t.get('shipping') is not None]
    if ship: out['ship_plain']=(round(shrink(ship,pricing['ship_plain']),2),len(ship))
    inbound=[(t['shipping'] or 0.0)/t['qty'] for t in buys if t.get('shipping') is not None]
    if inbound: out['ship_in']=(round(shrink(inbound,pricing['ship_in']),2),len(inbound))
    # Sell-through: each sold copy took days_held; at rate λ copies per trading day and changes/30 trading days per day,
    # the Gamma-Poisson posterior mean is (copies + prior) / (exposure + prior / current λ).
    timed=[x for x in trade_ledger(trades)['sales'] if x.get('changes') and x['days_held']>=0]
    if timed:
        copies=sum(x['qty'] for x in timed); exposure=sum(x['qty']*max(1.0,x['days_held'])*x['changes']/30.0 for x in timed)
        out['sell_through']=(round((copies+TRADE_PRIOR)/(exposure+TRADE_PRIOR/pricing['sell_through']),2),len(timed))
    return out

# --- More free signals: Card Kingdom buylist + Cardmarket (MTGJSON), legality/EDHREC (Scryfall), reprint risk ---
MTGJSON_IDS_MAX_AGE_DAYS = 7
SCRYFALL_BULK = 'https://api.scryfall.com/bulk-data'
FORMAT_CODES = (('standard','Std'),('pioneer','Pio'),('modern','Mod'),('legacy','Leg'),('vintage','Vin'),('commander','EDH'),('pauper','Pau'))
BUYLIST_ARB_MARGIN = 0.25  # $ per copy left after inbound shipping when a listing sits under Card Kingdom's buylist

def mtgjson_ids(report=lambda _m: None):
    """MTGJSON uuid -> {finish: TCGplayer product id}, from a cached cardIdentifiers file refreshed weekly."""
    path=ROOT/'mtgjson_cardIdentifiers.csv.xz'
    if not path.exists() or time.time()-path.stat().st_mtime>MTGJSON_IDS_MAX_AGE_DAYS*86400:
        report('MTGJSON: refreshing card identifiers (~11 MB, weekly)'); download(f'{MTGJSON_BASE}/csv/cardIdentifiers.csv.xz',path,report)
    return load_mtgjson_tcgplayer_ids(path)

def mtgjson_vendor_rows(uuid_prices, ids, printing_id, valid_keys):
    """{'buylist': [...], 'eu': [...]} daily rows (cents) from MTGJSON price entries: Card Kingdom's buylist (USD) and
    Cardmarket's price (EUR) for MTG printings in the catalog."""
    out={'buylist':[],'eu':[]}
    for uuid,formats in uuid_prices:
        finishes=ids.get(uuid)
        if not finishes or not isinstance(formats,dict): continue
        paper=formats.get('paper') or {}
        for vendor,side,kind,currency in (('cardkingdom','buylist','buylist','USD'),('cardmarket','retail','eu','EUR')):
            block=paper.get(vendor) or {}
            if block.get('currency',currency)!=currency: continue
            for finish,series in (block.get(side) or {}).items():
                product=finishes.get(finish); subtype=MTGJSON_FINISH_SUBTYPES.get(finish)
                key=card_key(f'tcgcsv:1:{product}') if product else None
                if key is None or key not in valid_keys or not subtype or not isinstance(series,dict): continue
                pid=printing_id(subtype)
                for day,price in series.items():
                    val=numeric(price); o=_day_ordinal(day)
                    if val and val>0 and o: out[kind].append((key,pid,o,int(round(val*100))))
    return out

def sync_mtgjson_today(store, report=lambda _m: None):
    """Today's Card Kingdom buylist and Cardmarket prices for MTG (MTGJSON AllPricesToday, ~6 MB). Skips a day already done."""
    req=urllib.request.Request(f'{MTGJSON_BASE}/AllPricesToday.json.gz',headers={'User-Agent':USER_AGENT})
    with urllib.request.urlopen(req,timeout=120) as r: payload=json.loads(gzip.decompress(r.read()))
    day=str((payload.get('meta') or {}).get('date') or '')
    if day and store.get_setting('mtgjson_today_date','')==day:
        report(f'MTGJSON {day}: buylist and Cardmarket prices already imported'); return 0
    valid={card_key(cid) for (cid,) in store.q("SELECT id FROM cards WHERE id LIKE 'tcgcsv:1:%' AND item_type='card'")}
    rows=mtgjson_vendor_rows((payload.get('data') or {}).items(),mtgjson_ids(report),store.printing_id,valid)
    store.upsert_daily(rows); store.setting('mtgjson_today_date',day)
    report(f"MTGJSON {day}: {len(rows['buylist']):,} Card Kingdom buylist and {len(rows['eu']):,} Cardmarket prices")
    return len(rows['buylist'])+len(rows['eu'])

def mtg_name_keys(name):
    """Base-name keys to try for a TCGplayer product name, most specific first. Crossover printings are named
    'New name - Original card' ('Khan, Engineered Evil - Sheoldred, the Apocalypse'), so the original card's name
    after the last ' - ' is tried too."""
    base=mtg_base_name(name); keys=[base]
    if ' - ' in base: keys.append(base.rsplit(' - ',1)[1].strip())
    return keys

def mtg_base_name(name):
    """Card name without TCGplayer's printing notes: 'Sol Ring (Borderless)' -> 'sol ring'."""
    return re.sub(r'\s*[\(\[][^\)\]]*[\)\]]','',str(name)).strip().casefold()

def refresh_scryfall_oracle(store, report=lambda _m: None):
    """Format legality and EDHREC rank per card name from Scryfall's oracle bulk file (~25 MB, weekly), recording
    any legality change (a ban, unban or rotation) as a dated event."""
    req=urllib.request.Request(SCRYFALL_BULK,headers={'User-Agent':USER_AGENT,'Accept':'application/json'})
    with urllib.request.urlopen(req,timeout=60) as r: listing=json.load(r)
    entry=next((d for d in listing.get('data',[]) if d.get('type')=='oracle_cards'),None)
    url=entry and (entry.get('jsonl_download_uri') or entry.get('download_uri'))
    if not url: raise RuntimeError('Scryfall bulk-data listing has no oracle cards file')
    with tempfile.TemporaryDirectory(prefix='cmt_scryfall_') as tmp:
        path=Path(tmp)/'oracle.jsonl.gz'; download(url,path,report)
        old={name:(legal,banned) for name,legal,banned in store.q('SELECT name,legal,banned FROM mtg_oracle')}
        rows=[]; today=date.today().isoformat(); events=[]
        with gzip.open(path,'rt',encoding='utf-8') as f:
            for line in f:
                line=line.strip().rstrip(',')
                if not line or line in ('[',']'): continue
                card=json.loads(line); legal=card.get('legalities') or {}
                legal_s=','.join(code for fmt,code in FORMAT_CODES if legal.get(fmt)=='legal')
                banned_s=','.join(code for fmt,code in FORMAT_CODES if legal.get(fmt) in ('banned','restricted'))
                names={card.get('name','')}|{face.get('name','') for face in card.get('card_faces') or []}
                for name in names:
                    key=mtg_base_name(name)
                    if not key: continue
                    rows.append((key,legal_s,banned_s,card.get('edhrec_rank'),utc()))
                    prior=old.get(key)
                    if prior and prior!=(legal_s,banned_s):
                        gone=set(filter(None,prior[0].split(',')))-set(filter(None,legal_s.split(',')))
                        new_bans=set(filter(None,banned_s.split(',')))-set(filter(None,prior[1].split(',')))
                        if new_bans: events.append((today,'MTG','banned',card.get('name'),'Banned/restricted in '+', '.join(sorted(new_bans))))
                        elif gone: events.append((today,'MTG','legality',card.get('name'),'No longer legal in '+', '.join(sorted(gone))))
        store.executemany('INSERT INTO mtg_oracle(name,legal,banned,edhrec,updated_at) VALUES(?,?,?,?,?) ON CONFLICT(name) DO UPDATE SET '
                          'legal=excluded.legal,banned=excluded.banned,edhrec=excluded.edhrec,updated_at=excluded.updated_at',rows)
        if events: store.executemany('INSERT OR IGNORE INTO market_events(day,game,kind,subject,detail) VALUES(?,?,?,?,?)',events)
    store.setting('scryfall_oracle_epoch',time.time())
    report(f'Scryfall: legality and EDHREC rank for {len(rows):,} card names; {len(events)} legality change(s) recorded')
    return len(rows)

def mtg_card_facts(store, today=None):
    """{base name: {'formats', 'banned', 'edhrec', 'sets', 'reprint', 'legal_change'}} for MTG: legality and EDHREC rank (Scryfall), how
    many sets the card has been printed in, and any set with it releasing within 60 days (or in the last 14) - an
    announced reprint, the main thing that crashes a card's price."""
    today=today or date.today(); out={}
    try:
        for name,legal,banned,edhrec in store.q('SELECT name,legal,banned,edhrec FROM mtg_oracle'):
            out[name]={'formats':legal or '','banned':banned or '','edhrec':edhrec,'sets':0,'reprint':None}
    except sqlite3.OperationalError: pass
    releases={}
    try:
        # Scryfall dates win; TCGCSV dates on standing promo groups (Secret Lair, The List, ...) are just "last updated".
        for code,name,day,source in store.q("SELECT code,name,released_on,source FROM set_info WHERE game='MTG' AND released_on IS NOT NULL "
                                            "ORDER BY source DESC"):
            if source=='tcgcsv' and _PERENNIAL_GROUP.search(name or ''): continue
            releases.setdefault(code,day)
    except sqlite3.OperationalError: pass
    # A standing ban is already in the price; only a change detected in the last 30 days is still moving it.
    try:
        for day,subject,detail in store.q("SELECT day,subject,detail FROM market_events WHERE kind IN ('banned','legality') AND day>=?",
                                          ((today-timedelta(days=30)).isoformat(),)):
            out.setdefault(mtg_base_name(subject),{'formats':'','banned':'','edhrec':None,'sets':0,'reprint':None})['legal_change']=f'{detail} ({day})'
    except sqlite3.OperationalError: pass
    lo=(today-timedelta(days=14)).isoformat(); hi=(today+timedelta(days=60)).isoformat()
    sets={}
    for name,code in store.q("SELECT DISTINCT name,set_code FROM cards WHERE game='MTG' AND item_type='card'"):
        for key in mtg_name_keys(name): sets.setdefault(key,set()).add(code)
    for key,codes in sets.items():
        info=out.setdefault(key,{'formats':'','banned':'','edhrec':None,'sets':0,'reprint':None})
        info['sets']=len(codes)
        upcoming=sorted((releases[c],c) for c in codes if c in releases and lo<=releases[c]<=hi)
        if upcoming and len(codes)>1: info['reprint']=f'{upcoming[-1][1]} {upcoming[-1][0]}'
    return out

def attach_card_facts(rows, facts):
    """Copy legality, EDHREC rank, print count and reprint news onto MTG ranking rows (by base card name)."""
    for r in rows:
        if r.get('game')!='MTG': continue
        f=next((facts[k] for k in mtg_name_keys(r.get('card_name') or r.get('name','')) if k in facts and (facts[k]['formats'] or facts[k]['edhrec'])),
               facts.get(mtg_base_name(r.get('card_name') or r.get('name',''))))
        if f: r.update(formats=f['formats'],banned=f['banned'],edhrec=f['edhrec'],sets_printed=f['sets'],reprint=f['reprint'],
                       legal_change=f.get('legal_change'))

def buylist_signals(r, pricing):
    """Card Kingdom notes for a row: arbitrage when a Near Mint listing is under CK's cash buylist by at least your
    minimum profit (after inbound shipping and supplies), and a rising buylist (dealers paying more is an early demand signal)."""
    bl=r.get('buylist'); low=r.get('low_price'); notes=[]
    if not bl: return notes
    cost=(low or 0)+pricing['ship_in']+pricing['cost']
    # Within your per-card limit too: four-figure vintage copies are where grading and authenticity risk is largest.
    if (low and (r.get('low_cond') in (None,'NM')) and cost<=pricing.get('max_card',float('inf')) and bl-cost>=BUYLIST_ARB_MARGIN
            and worth_it(bl-cost,cost,pricing)):
        notes.append(f"ARB: CK pays {money(bl)} cash vs listing {money(low)}")
    if (r.get('buylist_change_30d') or 0)>=15 and (r.get('return_30d') or 0)<(r['buylist_change_30d']-10):
        notes.append(f"CK buylist {r['buylist_change_30d']:+.0f}% in 30d")
    return notes

# --- Long-run release cycle: months after release, from a small weekly PriceCharting sample per game ---
LONGRUN_CARDS_PER_SET = 25      # most valuable cards listed today, fetched per set (release-month chase cards rank here too)
LONGRUN_CHASE_PER_SET = 15      # ...of which the 15 priciest IN THE RELEASE MONTH form the sample (no hindsight)
LONGRUN_SETS_PER_RUN = 2        # sets refreshed per game per weekly run (about 120 requests)
LONGRUN_REFRESH_DAYS = 30
LONGRUN_MONTHS = (-1,24)
LONGRUN_MIN_SETS = 5            # sets a game's long-run curve needs before it drives any action (thinner curves are only charted)
LONGRUN_CATEGORY = {'MTG':'magic-cards','Pokémon':'pokemon-cards','One Piece':'one-piece-cards'}

def _norm_set(name):
    return re.sub(r'[^a-z0-9]+',' ',re.sub(r'^[A-Z0-9]+:\s*','',str(name or '')).lower()).strip()

def _pc_set_release(store, game, slug):
    """Release date for a PriceCharting set slug, matched to the official set lists already stored (Scryfall/TCGCSV)."""
    want=_norm_set(slug.replace('-',' ')); best=None
    for name,day,source in store.q("SELECT name,released_on,source FROM set_info WHERE game=? AND released_on IS NOT NULL ORDER BY source DESC",(game,)):
        if source=='tcgcsv' and _PERENNIAL_GROUP.search(name or ''): continue  # 'last updated', not a release
        n=_norm_set(name)
        if n==want: return day
        if best is None and want in n and not any(x in n for x in ('commander','promo','prerelease','release event','jumbo')): best=day
    return best

def refresh_longrun(store, report=lambda _m: None, sets_per_game=LONGRUN_SETS_PER_RUN):
    """Weekly: for each game, (re)fetch the sets whose monthly sample is missing or older than LONGRUN_REFRESH_DAYS,
    sets 3-30 months old first. Each set is one list page plus up to LONGRUN_CARDS_PER_SET card pages, 3 s apart.
    If the site rate-limits us the run stops politely; every finished set is already saved."""
    try: return _refresh_longrun(store,report,sets_per_game)
    except RateLimited as exc:
        report(str(exc)); return -1

def _refresh_longrun(store, report, sets_per_game):
    done=0; today=date.today()
    for game,category in LONGRUN_CATEGORY.items():
        prefix=PC_GAME_PREFIX[game]
        page=_pc_get(f'{PRICECHARTING}/category/{category}')
        slugs=sorted({m for m in re.findall(r'href="/console/('+re.escape(prefix)+r'[a-z0-9-]+)"',page)
                      if not any(x in m for x in ('japanese','chinese','korean','promo','topps','burger','mcdonald','celebrations-classic'))
                      and not _PERENNIAL_GROUP.search(m.replace('-',' ')) and not any(x in m for x in ('secret-lair','the-list','-slx','special-guests','starter-deck','deck-set','learn-together','theme-deck'))})
        fetched={slug:at for slug,at in store.q('SELECT slug,fetched_at FROM pc_sets WHERE game=?',(game,))}
        candidates=[]
        for console in slugs:
            slug=console[len(prefix):]; release=_pc_set_release(store,game,slug)
            if not release or not (today-timedelta(days=3*365)).isoformat()<=release<=today.isoformat(): continue
            age=(date.today()-date.fromisoformat((fetched.get(console) or '1970-01-01')[:10])).days
            # Sets 3-30 months old show the cycle; newer ones are refreshed later as they age.
            useful=(today-timedelta(days=30*30)).isoformat()<=release<=(today-timedelta(days=90)).isoformat()
            if age>=LONGRUN_REFRESH_DAYS: candidates.append((useful,console not in fetched,release,console))
        for _useful,_new,release,console in sorted(candidates,reverse=True)[:sets_per_game]:
            listing=_pc_get(f'{PRICECHARTING}/console/{console}'); links=[]
            for href,title in re.findall(r'<td class="title"[^>]*>\s*<a href="(/game/'+re.escape(console)+r'/[^"]+)">([^<]+)</a>',listing):
                if href not in [h for h,_t in links]: links.append((href,title))
            rows=[]
            recent={u for (u,) in store.q('SELECT url FROM pc_series WHERE slug=? AND fetched_at>=?',
                                          (console,(datetime.now(timezone.utc)-timedelta(days=LONGRUN_REFRESH_DAYS)).isoformat()))}
            for href,title in links[:LONGRUN_CARDS_PER_SET]:
                if href in recent: continue  # already fresh (for example from an earlier sample)
                card=_pc_get(PRICECHARTING+href); m=re.search(r'VGPC\.chart_data = (\{.*?\});',card)
                if not m: continue
                pts=[[datetime.fromtimestamp(ms/1000,timezone.utc).strftime('%Y-%m'),c/100.0] for ms,c in json.loads(m.group(1)).get('used') or [] if c]
                rows.append((href,game,console,release,title,json.dumps(pts),utc()))
            store.executemany('INSERT INTO pc_series(url,game,slug,release,title,points,fetched_at) VALUES(?,?,?,?,?,?,?) ON CONFLICT(url) DO UPDATE SET '
                              'release=excluded.release,title=excluded.title,points=excluded.points,fetched_at=excluded.fetched_at',rows)
            store.execute('INSERT INTO pc_sets(game,slug,release,fetched_at) VALUES(?,?,?,?) ON CONFLICT(slug) DO UPDATE SET release=excluded.release,fetched_at=excluded.fetched_at',
                          (game,console,release,utc()))
            done+=1; report(f'Long-run sample: {game} {console} ({release}), {len(rows)} cards')
    return done

def longrun_curves(store):
    """{game: {'sets','cards','curve': [[month, median, p25, p75, n], ...]}}: chase-card prices relative to the release month.
    Per set, the LONGRUN_CHASE_PER_SET cards that were priciest in the release month are used, so cards that only became
    valuable later (survivorship) do not inflate the later months."""
    groups={}
    try: rows=store.q('SELECT game,slug,release,points FROM pc_series WHERE release IS NOT NULL')
    except sqlite3.OperationalError: return {}
    by_set={}
    for game,slug,release,points in rows: by_set.setdefault((game,slug,release),[]).append(json.loads(points))
    for (game,slug,release),cards in by_set.items():
        r=date.fromisoformat(release); m0=r.year*12+r.month-1
        priced=[]
        for pts in cards:
            series={int(mo[:4])*12+int(mo[5:7])-1-m0:v for mo,v in pts}
            base=series.get(0) or series.get(1)
            if base: priced.append((base,series))
        chase=sorted(priced,key=lambda x:-x[0])[:LONGRUN_CHASE_PER_SET]
        if len(chase)<5: continue
        g=groups.setdefault(game,{'sets':set(),'cards':0,'months':{}}); g['sets'].add(slug); g['cards']+=len(chase)
        for base,series in chase:
            for k,v in series.items():
                if LONGRUN_MONTHS[0]<=k<=LONGRUN_MONTHS[1]: g['months'].setdefault(k,[]).append(v/base)
    out={}
    for game,g in groups.items():
        curve=[]
        for k in sorted(g['months']):
            v=sorted(g['months'][k])
            if len(v)>=20: curve.append([k,_median(v)-1.0,v[len(v)//4]-1.0,v[3*len(v)//4]-1.0,len(v)])
        if curve: out[game]={'sets':sorted(g['sets']),'cards':g['cards'],'curve':curve}
    return out

def longrun_note(r, curves):
    """For a printing whose game has no daily release curve yet: what chase cards of recent sets did in the months ahead."""
    age=r.get('days_since_release'); c=(curves.get('monthly') or {}).get(r.get('game'))
    if age is None or not c or age>=365 or len(c['sets'])<LONGRUN_MIN_SETS: return None
    m=max(0,age//30); pts={k:v for k,v,_a,_b,_n in c['curve']}
    if m not in pts: return None
    later=[(k,(1+pts[k])/(1+pts[m])-1) for k in (m+3,m+6,m+12) if k in pts]
    if not later: return None
    return ('chase cards of recent sets moved '+', '.join(f'{v*100:+.0f}% by month {k}' for k,v in later)+
            f' (month {m} now; {c["cards"]} cards from {len(c["sets"])} sets, monthly)')

# --- Release cycle: how new cards' prices move around their set's release, measured on your own history ---
RELEASE_CURVE_RANGE = (-30, 90)   # days from the release day
RELEASE_CURVE_MIN_CARDS = 30      # printings needed on a day before its median is shown

RELEASE_TRADES = (
    # (name, buy/sell day, later day, kind): 'presell' = sell then instead of at the later day; 'buy' = buy then, sell later
    ('Pre-sell 7 days before release (vs selling on day 14)',-7,14,'presell'),
    ('Pre-sell 3 days before release (vs selling on day 14)',-3,14,'presell'),
    ('Buy on release day, sell on day 30',0,30,'buy'),
    ('Buy the dip on day 21, sell on day 60',21,60,'buy'),
    ('Buy on day 42, sell on day 90',42,90,'buy'),
)

def _release_trade_stats(results):
    out=[]
    for name,(d0,d1,kind),pairs in results:
        if len(pairs)<RELEASE_CURVE_MIN_CARDS: continue
        rets=sorted(r for r,_d in pairs); dollars=[d for _r,d in pairs]
        out.append({'name':name,'from':d0,'to':d1,'kind':kind,'n':len(rets),'median':_median(rets),'median_dollars':_median(dollars),
                    'win':sum(1 for v in rets if v>0)/len(rets),'p25':rets[len(rets)//4],'p75':rets[3*len(rets)//4]})
    return out

def release_curves(reader, today=None, pricing=None):
    """Median price path of new printings ($1+ at release) relative to their release-day price, from 30 days before
    to 90 days after, per game and for regular cards vs special treatments, pooled over every set released within
    the last year that your history covers. {label: {'cards', 'sets', 'curve': [[day, median, p25, p75, n], ...],
    'trades': [...]}} where trades scores RELEASE_TRADES per card after every selling cost and inbound shipping:
    for a pre-sell, how much more a sale on the early day nets than one on the later day; for a buy, the return on
    the all-in cost of buying at market on one day and selling at market on the later one."""
    pricing=pricing or DEFAULT_PRICING
    today=today or datetime.now(timezone.utc).date(); t0=today.toordinal(); lo,hi=RELEASE_CURVE_RANGE
    releases={k:o for k,o in set_release_days(reader).items() if t0-365<=o<=t0-7}
    if not releases: return {}
    names={pid:name for pid,name in reader.q('SELECT id,name FROM printings')}
    groups={}
    for cid,game,name,code,rarity in reader.q("SELECT id,game,name,set_code,rarity FROM cards WHERE item_type='card' AND game IN ('MTG','Pokémon','One Piece','Riftbound')"):
        release=releases.get((game,code)); key=card_key(cid)
        if release is None or key is None: continue
        by_printing={}
        for pid,day,market in reader.q('SELECT printing,day,market FROM daily WHERE card=? AND market IS NOT NULL AND day BETWEEN ? AND ?',
                                       (key,release+lo,release+hi)):
            by_printing.setdefault(pid,{})[day]=market/100.0
        label=f"{game} · {'regular' if variant_of(game,name,rarity)=='Regular' or game!='MTG' and rarity in REGULAR_RARITIES else 'special treatments'}"
        for prices in by_printing.values():
            base=next((prices[release+d] for d in (0,1,2,-1) if prices.get(release+d)),None)
            if not base or base<RANK_MIN_PRICE: continue
            g=groups.setdefault(label,{'cards':0,'sets':set(),'days':{},'trades':{}}); g['cards']+=1; g['sets'].add(code)
            for day,price in prices.items(): g['days'].setdefault(day-release,[]).append(price/base)
            near=lambda d: next((prices[release+d+k] for k in (0,1,-1,2,-2) if prices.get(release+d+k)),None)
            for name,d0,d1,kind in RELEASE_TRADES:
                p0,p1=near(d0),near(d1)
                if not (p0 and p1): continue
                if kind=='presell':
                    dollars=sale_net(p0,pricing)-sale_net(p1,pricing); ret=dollars/p1  # extra net, per $ of the later price
                else:
                    cost=p0+pricing['ship_in']; dollars=sale_net(p1,pricing)-cost; ret=dollars/cost
                g['trades'].setdefault(name,((d0,d1,kind),[]))[1].append((ret,dollars))
    out={}
    for label,g in groups.items():
        curve=[]
        for d in sorted(g['days']):
            v=sorted(g['days'][d])
            if len(v)>=RELEASE_CURVE_MIN_CARDS:
                q=lambda f: v[min(len(v)-1,int(f*len(v)))]
                curve.append([d,_median(v)-1.0,q(0.25)-1.0,q(0.75)-1.0,len(v)])
        if curve: out[label]={'cards':g['cards'],'sets':sorted(g['sets']),'curve':curve,
                              'trades':_release_trade_stats([(n,spec,rets) for n,(spec,rets) in g['trades'].items()])}
    return out

def release_curves_path(): return ROOT/'release_curves.json'

def save_release_curves(curves, monthly=None):
    path=release_curves_path(); tmp=path.with_suffix('.partial')
    tmp.write_text(json.dumps({'built_at':utc(),'curves':curves,'monthly':monthly or {}}),encoding='utf-8'); tmp.replace(path)

_CURVE_CACHE = {'mtime':None,'curves':{},'monthly':{}}

def load_release_curves():
    try:
        path=release_curves_path(); mtime=path.stat().st_mtime
        if _CURVE_CACHE['mtime']!=mtime:
            saved=json.loads(path.read_text(encoding='utf-8'))
            _CURVE_CACHE.update(mtime=mtime,curves=saved.get('curves') or {},monthly=saved.get('monthly') or {})
    except (OSError,ValueError):
        _CURVE_CACHE.update(mtime=None,curves={},monthly={})
    return _CURVE_CACHE['curves']

def load_monthly_curves():
    load_release_curves(); return _CURVE_CACHE.get('monthly') or {}

def curve_change(curve, day_from, day_to):
    """Median % move between two days of a release curve (nearest measured days), or None."""
    pts={d:m for d,m,_q1,_q3,_n in curve}
    if not pts: return None
    near=lambda d: min(pts,key=lambda x:abs(x-d))
    a,b=near(day_from),near(day_to)
    if abs(a-day_from)>3 or abs(b-day_to)>3: return None
    return ((1+pts[b])/(1+pts[a])-1)*100

RELEASE_PRESELL_DROP = -15.0   # % the curve must expect from now to day 30 before a pre-sell is suggested
RELEASE_DIP_GAIN = 10.0        # % recovery the curve must show (after the next 30+ days) before a dip buy is suggested

def _curve_for(r, curves):
    regular=r.get('variant') in (None,'Regular') or r.get('game')!='MTG' and str(r.get('variant')).split(' · ')[0] in REGULAR_RARITIES
    return curves.get(f"{r.get('game')} · {'regular' if regular else 'special treatments'}")

def _older_printing_floor(rows):
    """{(game, base name): median market of that card's regular printings in sets over 90 days old}. A reprint tends to
    settle near what its older printings trade at, so this caps how far a pre-sell estimate may fall (the median, not
    the cheapest, so one unusually cheap printing does not exaggerate the drop)."""
    prices={}
    for r in rows:
        age=r.get('days_since_release')
        if r.get('flags') or r.get('variant') not in (None,'Regular') or r.get('printing') not in ('Normal','') or (age is not None and age<PHASE_MATURE_DAYS): continue
        for name in mtg_name_keys(r.get('card_name') or r.get('name','')):
            if r.get('latest_price'): prices.setdefault((r.get('game'),name),[]).append(r['latest_price'])
    return {k:_median(v) for k,v in prices.items()}

def release_opportunities(rows, pricing, curves=None):
    """Actions for printings in sets that are in presale or under 90 days old, from what similar new cards did:
    PRE-SELL (sell copies you hold or will open now: similar cards fell a lot by day 30), WAIT (still in the slide:
    do not buy yet) and BUY THE DIP (similar cards recovered from this age; only when the curve shows it).
    Each row: dict(row=..., action, move %, by_day, value $ per copy at stake, note)."""
    curves=load_release_curves() if curves is None else curves; out=[]; floors=_older_printing_floor(rows)
    for r in rows:
        age=r.get('days_since_release'); price=r.get('latest_price') or 0
        if age is None or age>=PHASE_MATURE_DAYS or age<-60 or r.get('flags') or price<RANK_MIN_PRICE: continue
        c=_curve_for(r,curves)
        if not c:
            o=_monthly_opportunity(r,pricing,load_monthly_curves())
            if o: out.append(o)
            continue
        start=max(age,RELEASE_CURVE_RANGE[0])
        if age<14:
            target=max(30,age+14); move=curve_change(c['curve'],start,target)
            older=min((floors[(r.get('game'),k)] for k in mtg_name_keys(r.get('card_name') or r.get('name','')) if (r.get('game'),k) in floors),default=None)
            if move is not None and older and price*(1+move/100)<older:
                move=(min(price,older)/price-1)*100  # a reprint is expected to settle near its older printings, not below
            if move is not None and move<=RELEASE_PRESELL_DROP:
                at_stake=sale_net(price,pricing)-sale_net(price*(1+move/100),pricing)
                out.append({'row':r,'action':'PRE-SELL','move':move,'by_day':target,'value':at_stake,
                            'note':f"sell copies you hold or will open now (~{money(sale_net(price,pricing))} net each); expected "
                                   f"{move:+.0f}% by day {target}"+(f" (older printings trade at {money(older)})" if older else '')+
                                   f", i.e. ~{money(at_stake)} less per copy"})
            continue
        move=curve_change(c['curve'],start,min(90,max(age+30,60)))
        if move is None: continue
        if move>=RELEASE_DIP_GAIN and r.get('max_buy'):
            out.append({'row':r,'action':'BUY THE DIP','move':move,'by_day':min(90,max(age+30,60)),'value':price*move/100,
                        'note':f"similar new cards recovered {move:+.0f}% from day {age}; buy ≤ {money(r['max_buy'])}"})
        elif move<0:
            out.append({'row':r,'action':'WAIT','move':move,'by_day':min(90,max(age+30,60)),'value':-price*move/100,
                        'note':f"still in the post-release slide: similar cards moved {move:+.0f}% more by day {min(90,max(age+30,60))}; don't buy yet"})
    out.sort(key=lambda o:(o['action']!='PRE-SELL',-o['value']))
    return out

LONGRUN_BUY_GAIN = 0.15     # a long-run buy zone needs chase cards to have gained at least this much over the next 12 months
LONGRUN_PRESELL_DROP = -0.10

def _monthly_opportunity(r, pricing, monthly):
    """Release-cycle action from the monthly long-run curve (games without a daily curve yet)."""
    c=monthly.get(r.get('game')); age=r.get('days_since_release'); price=r.get('latest_price') or 0
    if not c or age is None or price<RANK_MIN_PRICE*5 or len(c['sets'])<LONGRUN_MIN_SETS: return None  # the long-run sample is chase cards: apply it to $5+ cards
    pts={k:v for k,v,_a,_b,_n in c['curve']}; m=max(0,age//30)
    if m not in pts: return None
    ahead=lambda k: (1+pts[k])/(1+pts[m])-1 if k in pts else None
    soon=ahead(m+3); year=ahead(m+12)
    if age<45 and soon is not None and soon<=LONGRUN_PRESELL_DROP:
        return {'row':r,'action':'PRE-SELL','move':soon*100,'by_day':(m+3)*30,'value':sale_net(price,pricing)-sale_net(price*(1+soon),pricing),
                'note':f"sell copies you hold or will open now: chase cards of recent {r['game']} sets moved {soon*100:+.0f}% over the next 3 months"}
    if 60<=age<=270 and year is not None and year>=LONGRUN_BUY_GAIN and r.get('max_buy'):
        return {'row':r,'action':'LONG-TERM BUY','move':year*100,'by_day':(m+12)*30,'value':price*year,
                'note':f"long-term buy zone (hold ~12 months): chase cards from month {m} gained {year*100:+.0f}% a year later; "
                        f"buy ≤ {money(r['max_buy'])}; not a 14-day trade"}
    if age<90 and soon is not None and soon<0:
        return {'row':r,'action':'WAIT','move':soon*100,'by_day':(m+3)*30,'value':-price*soon,
                'note':f"still early: chase cards of recent {r['game']} sets moved {soon*100:+.0f}% more over the next 3 months"}
    return None

def release_note(r):
    """For a printing in a set released within 42 days (or still in presale): what similar new cards did next."""
    age=r.get('days_since_release')
    if age is None or age>=42: return None
    curves=load_release_curves()
    if not any(k.startswith(f"{r.get('game')} ·") for k in curves):
        monthly=longrun_note(r,{'monthly':load_monthly_curves()})
        return f'new set ({age}d after release): {monthly}' if monthly else None
    regular=r.get('variant') in (None,'Regular') or r.get('game')!='MTG' and str(r.get('variant')).split(' · ')[0] in REGULAR_RARITIES
    c=curves.get(f"{r.get('game')} · {'regular' if regular else 'special treatments'}")
    if not c: return None
    later=min(90,max(age+30,30)); move=curve_change(c['curve'],max(age,RELEASE_CURVE_RANGE[0]),later)
    if move is None: return None
    when='presale' if age<0 else f'day {age} after release'
    return f"new set ({when}): similar new cards moved {move:+.0f}% by day {later} (median of {c['cards']:,})"

# --- Long-term history on demand: PriceCharting's monthly ungraded prices for one card (small, polite lookups) ---
PRICECHARTING = 'https://www.pricecharting.com'
PRICECHARTING_INTERVAL = 3.0       # seconds between requests, one at a time (1 s gets HTTP 429 from the site)
PRICECHARTING_CACHE_DAYS = 7
PC_GAME_PREFIX = {'MTG':'magic-','Pokémon':'pokemon-','One Piece':'one-piece-'}  # Riftbound is not listed there
_PC_LOCK = threading.Lock(); _PC_LAST = [0.0]

class RateLimited(RuntimeError):
    """A site asked us to slow down: stop the current batch and keep what was saved."""

def _pc_get(url):
    with _PC_LOCK:
        wait=PRICECHARTING_INTERVAL-(time.time()-_PC_LAST[0])
        if wait>0: time.sleep(wait)
        _PC_LAST[0]=time.time()
    req=urllib.request.Request(url,headers={'User-Agent':USER_AGENT})
    try:
        with urllib.request.urlopen(req,timeout=30) as r: return r.read().decode('utf-8','ignore')
    except urllib.error.HTTPError as exc:
        if exc.code==429: raise RateLimited('PriceCharting asked us to slow down (HTTP 429); stopping until the next run') from exc
        raise

def _pc_cache_path(): return ROOT/'pricecharting_cache.json'

def _pc_pick(page, prefix, number):
    """Best product link on a PriceCharting search page: the game's English sets, preferring the collector number."""
    seen=[]
    for url,console,slug in re.findall(r'href="(https://www\.pricecharting\.com/game/([a-z0-9-]+)/([a-z0-9-]+))"',page):
        if not console.startswith(prefix) or any(x in console for x in ('japanese','chinese','korean')) or url in seen: continue
        seen.append(url)
    num=(re.match(r'\d+',str(number or '')) or [None])[0]
    if num:
        for url in seen:
            if url.rsplit('-',1)[-1]==num.lstrip('0') or url.endswith('-'+num): return url
    return seen[0] if seen else None

def pricecharting_history(store, card_id, refresh=False):
    """{'url','title','points': [[YYYY-MM, dollars], ...]} of monthly ungraded prices for a catalog card, or None.
    Cached for a week; one search and one product request when not cached."""
    try: cache=json.loads(_pc_cache_path().read_text(encoding='utf-8'))
    except (OSError,ValueError): cache={}
    hit=cache.get(card_id)
    if hit and not refresh and time.time()-hit.get('fetched',0)<PRICECHARTING_CACHE_DAYS*86400: return hit.get('result')
    row=store.q('SELECT game,name,set_code,collector_number FROM cards WHERE id=?',(card_id,))
    if not row: return None
    game,name,code,number=row[0]; prefix=PC_GAME_PREFIX.get(game)
    if not prefix: return None
    set_name=next((n for (n,) in store.q("SELECT name FROM set_info WHERE game=? AND code=? ORDER BY source='tcgcsv' DESC",(game,code))),'') or ''
    set_name=re.sub(r'^[A-Z0-9]+:\s*','',set_name)
    query=' '.join(x for x in (re.sub(r'\s*\([^)]*\)','',name).split(' - ')[0],set_name) if x)
    page=_pc_get(f'{PRICECHARTING}/search-products?q={urllib.parse.quote_plus(query)}&type=prices')
    url=None if 'VGPC.chart_data' in page else _pc_pick(page,prefix,number)
    if url: page=_pc_get(url)
    m=re.search(r'VGPC\.chart_data = (\{.*?\});',page)
    result=None
    if m:
        data=json.loads(m.group(1)); title=re.search(r'<h1[^>]*id="product_name"[^>]*>\s*([^<]+)',page)
        points=[[datetime.fromtimestamp(ms/1000,timezone.utc).strftime('%Y-%m'),cents/100.0] for ms,cents in data.get('used') or [] if cents]
        result={'url':url or '','title':(title.group(1).strip() if title else query),'points':points}
    cache[card_id]={'fetched':time.time(),'result':result}
    try: _pc_cache_path().write_text(json.dumps(cache),encoding='utf-8')
    except OSError: pass
    return result

def history_summary(result):
    """Plain sentence on a long-term monthly history: latest, 3/6/12-month change and the 12-month range."""
    pts=(result or {}).get('points') or []
    if len(pts)<2: return None
    latest=pts[-1][1]; change=lambda k: (latest/pts[-1-k][1]-1)*100 if len(pts)>k and pts[-1-k][1] else None
    last12=[v for _m,v in pts[-12:]]
    parts=[f"{k} months {c:+.0f}%" for k,c in ((3,change(3)),(6,change(6)),(12,change(12))) if c is not None]
    return (f"PriceCharting (ungraded, monthly, all sellers) for '{result['title']}': {money(latest)} now; "+', '.join(parts)+
            f"; 12-month range {money(min(last12))}–{money(max(last12))}. Check the match before relying on it.")

# --- Glossary: every column, tile and action in plain words (click a column heading, the Glossary button, or GLOSSARY) ---
GLOSSARY = (
    # (term, other names it appears under, meaning)
    ('Market', ('Market price','Price','Market then'),
     "TCGplayer's market price: the average of recent real sales (all conditions). 'Market then' is the market price on the day you logged a trade."),
    ('Low', ('Low listing','Lowest listing','Cheapest listing'),
     'The cheapest copy listed on TCGplayer right now, in any condition. A low far below market is usually a played copy.'),
    ('Low ≈', ('Low cond','Cond (low)'),
     'The condition the cheapest listing is probably in, judged by how far below market it is (NM, LP, MP, HP, DMG).'),
    ('Cond', ('Condition',),
     'Card condition: NM Near Mint, LP Lightly Played, MP Moderately Played, HP Heavily Played, DMG Damaged.'),
    ('Max buy', ('Max buy NM · LP · MP','Max buy NM/LP/MP','Pay ≤ NM · LP · MP','Max buy (that condition)'),
     'The most you should pay for one copy in that condition and still meet your targets: your win chance and your $ / % minimum profit, after every fee and shipping. Use it as your buylist / trade-in price.'),
    ('Exp. profit', ('E[profit]','E[profit]/copy','Expected profit','Avg P/L per copy','$ per copy'),
     'Expected profit per copy after selling fees, shipping both ways and supplies, if it sells at the forecast price. "now" = buying the cheapest listing; "at max" = buying at your Max buy.'),
    ('Win', ('Win @ low','Win % at low','Win rate','Win rate (90% range)','Better/profitable'),
     'Chance the trade ends in profit within your horizon (it must sell AND beat your all-in cost). The range in brackets is the likely spread of that estimate. In the backtest, Win rate is what actually happened.'),
    ('Promised win', ('Promised',),
     'What the app predicted the win chance would be, so you can compare it with what actually happened (Win rate).'),
    ('Sells', ('Chance it sells',),
     "Chance one copy sells within your horizon, from how often the card's price changes (it changes when copies sell)."),
    ('Liquidity', ('Liq.','Trading days','Min trading days /30'),
     'How actively a card trades: days in the last 30 its price changed. High = 15+, Medium = 6–14, Low = 2–5, Very low = 0–1.'),
    ('Qty', ('Suggested qty','Buy qty'),
     'How many copies to buy: the smallest of what is likely to sell, your per-card and per-set limits, your remaining capital and a cautious (quarter-Kelly) stake. The reason in brackets is the limit that applied.'),
    ('Max qty', ('Sellable qty',),
     'Copies with at least an even chance of all selling within your horizon at the current trading pace.'),
    ('Target sell', ('List at','List at (target)'),
     'The asking price with the best expected profit: high enough to earn more, low enough to still sell. The % is its chance to sell within your horizon.'),
    ('Quick sale', (),
     'A price just under the cheapest Near Mint listing: sells fastest, earns least.'),
    ('Break-even sell', ('Min sell',),
     'The sale price that exactly covers what you paid plus every fee and shipping. Below it you lose money.'),
    ('Range 80%', ('80% range',),
     'Where the market price is expected to be at the end of your horizon, 8 times out of 10.'),
    ('Forecast median', ('Median',),
     'The middle forecast for the market price at the end of your horizon (half the time higher, half lower). In release-trade tables, Median is the typical result.'),
    ('Chance of rise', ('P(rise)',),
     'Chance the market price is higher at the end of your horizon than today (before costs).'),
    ('Vol /yr', ('30-day volatility','Volatility'),
     'How much the price swings, scaled to a year. 20% is calm; 150%+ is very jumpy.'),
    ('7d %', ('7-day','7 days','7d'),
     'Price change over the last 7 days.'),
    ('30d %', ('30-day','30 days','30d'),
     'Price change over the last 30 days.'),
    ('1 day', (), 'Change since the previous day.'),
    ('30-day high', ('At 30-day high',), 'The highest price in the last 30 days; "At 30-day high" counts cards trading at it now.'),
    ('30-day drawdown', ('Drawdown',), 'How far today is below the 30-day high.'),
    ('Market ÷ low', (), 'Market price divided by the cheapest listing. Far above 1 (2×+) or below 0.75 means the market price is unreliable.'),
    ('Sharpe', ('30-day Sharpe','Significant Sharpe','Gain vs swings (Sharpe)','Steady risers'),
     'Return per unit of risk over 30 days, after the Treasury-bill rate (advanced). Ignores fees. "Significant" = unlikely to be luck across 200,000 cards.'),
    ('P(SR>0)', ('P(Sharpe>0)','PSR>0','Trend is real (chance)'), 'Chance the true Sharpe is above zero given how short and noisy the history is (advanced).'),
    ('Score', ('Opportunity score',), 'A 0–100 blend of 7-day and 30-day momentum and Sharpe (advanced; not a buy signal).'),
    ('Ranking', ('State','Excluded'),
     'Whether a card is used in rankings and buy lists. Excluded: under $1, market price far above or below every listing, or a rise from one odd day.'),
    ('CK buylist', ('Card Kingdom buylist',), "Cash Card Kingdom pays for a Near Mint copy: a safety exit if it doesn't sell."),
    ('Formats', ('Legal',), 'MTG formats the card is legal in (Std, Pio, Mod, Leg, Vin, EDH, Pau). Only a recent change affects advice.'),
    ('EDHREC', ('EDHREC rank',), 'Commander popularity rank (1 = most played). Lower numbers mean steadier demand.'),
    ('Recommendation', ('Why','Note','Detail','Details'), 'The plain-language action and its main reason or caution.'),
    ('Confidence', (), 'How sure the app is: High (80%+ chance), Medium (65–80%), Low (under 65% or thin data).'),
    ('Do this', ('Action','Signal'),
     'BUY NOW: the listing is under your limit. TRADE-IN PRICE: pay up to this through trade-ins/collections. PRE-SELL / SELL NOW: sell new-set copies before the usual drop. '
     'WAIT: new set still falling. BUY THE DIP / LONG-TERM BUY: new set likely to recover (a multi-month hold). BUY → SELL TO CK: listing under Card Kingdom\'s cash price. '
     'SELL / SELL SOME (TRIM): your holding should be sold or reduced. BUNDLE: worth less than the cost of selling one copy, so sell it in a lot or with a bigger order. '
     'HOLD: keep it. CHECK: your price alert fired.'),
    ('Age', ('Days since release',), 'Days since the card\'s set released ("before" = presale).'),
    ('Typical move', (), 'What similar new cards did from this age onward (measured on your price history).'),
    ('Variant', (), 'The printing\'s treatment (Borderless, Showcase, Serial Numbered, Special Illustration Rare…), read from TCGplayer\'s naming.'),
    ('Printings', ('Cards',), 'How many card printings are counted in that row.'),
    ('Set 7d %', ('Set change',), 'Price change of holding one copy of every card in the set.'),
    ('Rising 7d', (), 'Share of the set\'s cards up over 7 days.'),
    ('Value (1 each)', ('Value 1 each',), 'What one copy of every card in the set is worth at market.'),
    ('Index', ('Market index',), 'A daily price index for the game, like a stock index: it starts at 100 and each day moves by the average price change of '
     'cards worth $1+ (a single day\'s jump is capped at 25% so one spike can\'t distort it). 110 means prices are up about 10% since the start of the chart. '
     '"Every card counts equally" treats a $2 and a $200 card the same; "Pricier cards count more" follows where the money is.'),
    ('Up / down 7d', ('Cards up / down 7 days',), 'How many cards rose vs fell over 7 days.'),
    ('Buy now', ('Buy now (count)','Under your max buy'), 'How many printings have a listing under your limit right now.'),
    ('Strategy', (), 'A buying rule tested in the backtest.'),
    ('Trades', (), 'How many test trades (backtest) or real trades (your log).'),
    ('ROI', ('Return',), 'Profit as a % of what was spent, after every cost.'),
    ('Total P/L (1 each)', ('Total P/L',), 'Total profit if one copy were bought per signal.'),
    ('Worst drawdown', (), 'The biggest fall in running profit along the way. $0 means it never dipped.'),
    ('Avg cost', ('Cost',), 'What you paid per copy, including inbound shipping.'),
    ('Worth if sold', ('Liquidation value','Liquidation'), 'What your copies would put in your pocket if sold quickly now, after fees and shipping (finance term: liquidation value).'),
    ('Profit if sold', ('Unrealized P/L','P/L','Unrealized'), 'Worth if sold minus what you paid, on copies you still hold (finance term: unrealized P/L).'),
    ('Predicted P/L', ('Predicted profit',), 'The profit the app predicted when you logged the buy.'),
    ('Realized P/L', ('Actual profit',), 'Your actual profit on a sale: what the buyer paid minus fees, shipping and your average cost (finance term: realized P/L).'),
    ('Alerts', (), 'Your price alerts: market at or above / at or below your chosen price.'),
    ('Fees', (), 'Platform fees you paid on that sale.'),
    ('Shipping', (), 'Shipping you paid on that trade (inbound on buys, outgoing on sales).'),
    ('Side', (), 'BUY or SELL.'),
    ('Kelly fraction', (), 'How cautious the quantity sizing is: 0.25 = a quarter of the mathematically optimal stake, because forecasts are estimates.'),
    ('Min profit per copy $', ('Min profit',), 'No trade is suggested unless it should earn at least this per copy.'),
    ('Min return %', ('Min return',), 'No trade is suggested unless it should earn at least this % of what you pay.'),
    ('Capital $', ('Capital',), 'Your total trading budget; limits are a share of it.'),
    ('Max per card $', ('Max per card',), 'The most money you want in any single printing.'),
    ('Max per set %', ('Max per set',), 'The most of your capital you want in any one set (reprint and set-crash risk).'),
    ('Selling fee %', (), "Marketplace commission + payment processing (TCGplayer about 13.25%)."),
    ('Per-order fee $', (), 'The fixed fee per order (TCGplayer $0.30).'),
    ('Plain shipping $', (), 'Your cost to mail an ordinary sale (stamp, envelope, toploader).'),
    ('Tracked shipping $', ('Tracked from sale $',), 'Your cost for tracked shipping, used for sales at or above the "tracked from" price.'),
    ('Buyer pays shipping $', ('…on orders under $',), 'Shipping the buyer pays on small orders (under the free-shipping threshold).'),
    ('Inbound shipping per card bought $', ('Inbound shipping',), 'What shipping costs you per card you buy.'),
    ('Supplies per card $', ('Supplies',), 'Sleeves, toploaders and labour per card sold.'),
    ('Target win %', (), 'The chance of profit you require before the app suggests a buy (60% by default).'),
    ('Copies sold per trading day', ('Sell-through',), 'How many of your copies sell per day the card trades; learned from your logged sales.'),
    ('Horizon (days)', ('Horizon',), 'How far ahead forecasts and trades look (7, 14 or 30 days).'),
    ('Risk-free rate %', (), 'The Treasury-bill rate, used only for Sharpe (advanced).'),
    ('LP ×', ('MP ×','HP ×','DMG ×'), 'Share of the Near Mint price a copy in that condition sells for (e.g. LP 0.85 = 85%).'),
    ('Low counts as NM if ≥ × market', ('played_ratio',), 'A cheapest listing at least this share of market is treated as Near Mint; lower ones as played.'),
    ('ID', ('Key',), 'Internal identifier (hidden).'),
    ('Card', ('Name',), 'The card and printing (Foil, Borderless and other treatments are in brackets).'),
    ('Game', (), 'MTG, Pokémon, One Piece or Riftbound.'),
    ('Set', (), "The set's TCGplayer code (in the Sets view: the set or variant)."),
    ('Date', ('Time','When','Source time'), "When it happened. Source time = when TCGplayer's data was published."),
    ('Type', ('Item',), 'What the row is: a card, a set type (expansion, commander…) or an alert type.'),
    ('Kind', (), 'Which price the row is: market (recent sales), low (cheapest listing), mid (middle listing), high, or direct low.'),
    ('Source', (), 'Where the price came from: TCGCSV (daily TCGplayer data), MTGJSON (90-day MTG history), Scryfall or the release calendar.'),
    ('Collected at', (), 'When your computer downloaded that price.'),
    ('Currency', (), 'USD unless noted (Cardmarket is in euros).'),
    ('Collector', ('Status','Records'), 'Data-collection runs: what ran, whether it finished, and how many records it handled.'),
    ('Trade', (), 'A release-cycle trade tested on your history (buy or pre-sell on one day, compare with a later day).'),
)

def _gloss_key(text): return re.sub(r'[^a-z0-9%$×÷≈/]+','',str(text).casefold())

_GLOSS_INDEX = {}
for _term,_aliases,_meaning in GLOSSARY:
    for _name in (_term,*_aliases): _GLOSS_INDEX.setdefault(_gloss_key(_name),(_term,_meaning))

def glossary_lookup(name):
    """(term, meaning) for a column/tile/label name, or None."""
    return _GLOSS_INDEX.get(_gloss_key(name))

# --- Plain-language decisions for the Today tab: "should I buy at this price?", "what should I sell it for?" ---
def confidence_label(p):
    return '—' if p is None else 'High' if p>=0.8 else 'Medium' if p>=0.65 else 'Low'

def _row_forecast(model, r):
    return forecast_for(model,r.get('return_30d'),r.get('return_7d'),r.get('latest_price'),r.get('printing',''),r.get('price_changes_30d'),
                        r.get('return_sd_30d'),r.get('variant'),r.get('days_since_release'))

def _row_warnings(r):
    """(hard stops, cautions) in plain words for a ranked row."""
    hard=[]; soft=[]
    for flag in r.get('flags') or ():
        hard.append({'market ≪ low':"TCGplayer's market price is below every listing (dragged down by cheap played-copy sales), so it can't be trusted",
                     'market ≫ low':'copies are listed far below the market price, so the market price is unreliable',
                     'single jump':'the recent rise came from a single day, which is usually a listing glitch'}.get(flag,f'excluded: {flag}'))
    if r.get('reprint'): hard.append(f"a reprint was announced ({r['reprint']}): prices usually fall")
    if r.get('legal_change'): soft.append(f"its legality just changed — {r['legal_change']} — so the price may still be adjusting")
    age=r.get('days_since_release')
    if age is not None and age<42: hard.append('new set: new cards keep falling for weeks after release (see CYCLE)')
    if (r.get('price_changes_30d') or 0)<6: soft.append(f"it trades on only {r.get('price_changes_30d') or 0} of the last 30 days, so it can take a while to sell")
    return hard,soft

HISTORY_READY_DAYS = 30  # daily prices a printing needs before its own trend and liquidity can be trusted

def _history_note(r):
    """Plain explanation when a printing's own history is too short to judge (None when it is long enough)."""
    obs=r.get('observations') or 0
    if obs>=HISTORY_READY_DAYS: return None
    ready=(date.fromisoformat(r['latest_date'])+timedelta(days=HISTORY_READY_DAYS-obs)).isoformat() if r.get('latest_date') else 'in a few weeks'
    why=f" ({r.get('game')} price history only started with your daily syncs)" if r.get('game')!='MTG' else ''
    return f"only {obs} day(s) of prices so far{why}; judgments need about {HISTORY_READY_DAYS}, ready around {ready}"

def decide_buy(r, model, pricing, cond, price):
    """Verdict for buying one copy of a ranked printing in `cond` at `price`: {'verdict','headline','details'}."""
    h=pricing['horizon']; fc=_row_forecast(model,r) if r and model else None
    young=_history_note(r) if r else None
    if young:
        return {'verdict':'NOT YET','headline':f"NOT ENOUGH HISTORY YET — {young}.",
                'details':[f"Market price {money(r.get('latest_price'))}, cheapest listing {money(r.get('low_price'))}.",
                           "Until then, only buy well under market (for example at a typical shop buylist of 50–60%) and check condition."]}
    if not fc:
        return {'verdict':'NO DATA','headline':'Not enough price history to judge this card yet.','details':[]}
    market=r['latest_price']; value=market*condition_share(pricing,cond); ship_in=pricing['ship_in']
    base=pricing_targets(market,r.get('low_price'),fc,pricing,r.get('price_changes_30d'))
    mine=pricing_targets(value,price,fc,dict(pricing,played_ratio=0.0),r.get('price_changes_30d'))
    limit=base['max_buy_cond'].get(cond); profit=mine['exp_sale_net_low']-(price+ship_in); win=mine['win_at_low'] or 0.0
    ask=best_list_price(fc,fc['_stats'],value,price+ship_in,pricing,base['p_sold'])
    hard,soft=_row_warnings(r)
    if hard:
        verdict,headline='NO',f"DON'T BUY — {hard[0]}."
    elif limit and price<=limit+0.005:
        verdict,headline='YES',f"YES — buy at {money(price)} or less (your limit for {cond} is {money(limit)})."
    elif profit>0 and win>=0.5:
        verdict,headline='MAYBE',(f"MAYBE — thin margin: about {money(profit)} expected profit, under your minimum. "
                                  f"Your limit for {cond} is {money(limit) if limit else 'none'}.")
    else:
        verdict,headline='NO',(f"NO — at {money(price)} you'd expect to {'lose' if profit<0 else 'make only'} {money(abs(profit))} per copy. "
                               +(f"Offer at most {money(limit)}." if limit else "No price meets your targets right now."))
    details=[f"Market price {money(market)} · a {cond} copy is worth about {money(value)} · cheapest listing {money(r.get('low_price'))}.",
             f"Buying at {money(price)}: expected profit {money(profit) if profit>=0 else '−'+money(-profit)} after fees, both shipping legs "
             f"and supplies; {win*100:.0f}% chance it sells at a profit within {h} days.",
             f"Then list it at {money(ask[0])} ({ask[1]*100:.0f}% chance to sell within {h} days), or {money(base['quick_sell'])} for a quick sale.",
             ('Most you should pay: '+max_buy_text(base,('NM','LP','MP','HP'))+'.' if base.get('max_buy') else
              f"Most you should pay: nothing — after fees and shipping no price leaves your {money(pricing.get('min_profit',0))} / "
              f"{pricing.get('min_roi',0):g}% minimum on this card."),
             f"Next {h} days: 80% chance the market ends between {money(value*base['q10_price']/market)} and {money(value*base['q90_price']/market)}."]
    if r.get('buylist'): details.append(f"Card Kingdom pays {money(r['buylist'])} cash for a Near Mint copy: your safety exit.")
    details+=[w[0].upper()+w[1:]+'.' for w in hard[1:]+soft]
    if hard and 'new set' not in hard[0]: details.append("Why the NO when the numbers above look fine: they assume today's price data is right, and for this card it may not be. "
                            "Check recent sold listings on the platforms you use before buying.")
    return {'verdict':verdict,'headline':headline,'details':details}

def decide_sell(r, model, pricing, cond, cost=None, qty=1):
    """Where to list a copy you own (what you paid is sunk; it only sets the profit shown)."""
    h=pricing['horizon']; fc=_row_forecast(model,r) if r and model else None
    young=_history_note(r) if r else None
    if young:
        anchor=min(x for x in (r.get('latest_price'),r.get('low_price')) if x) if r.get('latest_price') else None
        return {'verdict':'NOT YET','headline':f"LIST NEAR {money(anchor)} — not enough history to optimize yet ({young}).",
                'details':[f"Market price {money(r.get('latest_price'))}, cheapest listing {money(r.get('low_price'))}: listing at or just under the cheapest "
                           "Near Mint copy sells fastest."]}
    if not fc:
        return {'verdict':'NO DATA','headline':'Not enough price history to price this card yet.','details':[]}
    market=r['latest_price']; value=market*condition_share(pricing,cond)
    base=pricing_targets(market,r.get('low_price'),fc,pricing,r.get('price_changes_30d'))
    ask,fill,_ev=best_list_price(fc,fc['_stats'],value,0.0,pricing,base['p_sold'])
    quick=min(value,(r.get('low_price') or value))*0.99 if cond=='NM' else value*0.95
    hold=value*(1+base['mean_return'])
    opp=next((o for o in release_opportunities([r],pricing) if o['action']=='PRE-SELL'),None)
    if opp:
        ask=min(ask,value)  # the details below quote the same price as the headline
        verdict,headline='SELL NOW',f"SELL NOW — new cards like this usually drop {abs(opp['move']):.0f}% by day {opp['by_day']}. List at {money(ask)} today."
    elif sale_net(quick,pricing)>=sale_net(hold,pricing):
        verdict,headline='SELL',f"SELL — list at {money(ask)} ({fill*100:.0f}% chance to sell within {h} days); prices aren't expected to rise, so don't wait."
    else:
        rising=value*base['median_price']/market>value*1.01
        floor=max(quick,value*base['median_price']/market)
        if floor>=ask*0.99: floor=quick  # never "lower" toward a price above the listing
        verdict,headline='LIST HIGH',(f"LIST AT {money(ask)} — {fill*100:.0f}% chance to sell within {h} days. "+
            ("Prices lean up, so if it doesn't sell, keep it listed rather than cutting the price." if rising else
             f"If it hasn't sold in about a week, lower it toward {money(floor)}."))
    details=[f"Quick sale: {money(quick)} (nets {money(sale_net(quick,pricing))} after fees and shipping).",
             f"At {money(ask)} you'd net {money(sale_net(ask,pricing))} per copy"+
             ((f": {money(sale_net(ask,pricing)-cost)} profit on your {money(cost)} cost." if sale_net(ask,pricing)>=cost else
               f": a {money(cost-sale_net(ask,pricing))} loss on your {money(cost)} cost (what you paid is spent either way; this is still the best price to ask)."
               ) if cost else '.'),
             f"Next {h} days: median {money(value*base['median_price']/market)}, 80% range {money(value*base['q10_price']/market)}–{money(value*base['q90_price']/market)}."]
    if cost: details.append(f"Break-even list price for your cost: {money((cost+selling_costs(value,pricing))/(1-pricing['fee_pct']/100))}.")
    if r.get('buylist'): details.append(f"Card Kingdom would pay {money(r['buylist'])} cash (Near Mint) if it doesn't sell.")
    if base.get('max_qty') is not None and qty>max(1,base['max_qty']): details.append(f"Only about {base['max_qty']} copies are likely to sell within {h} days at today's activity.")
    hard,soft=_row_warnings(r); details+=[w[0].upper()+w[1:]+'.' for w in hard+soft]
    return {'verdict':verdict,'headline':headline,'details':details}

def todays_actions(rows, positions, pricing, limit=60):
    """One plain-language to-do list: sells first (your holdings), then new-set pre-sells, buy-now listings, Card Kingdom
    arbitrage and trade-in targets. Each: {'action','id','name','price','qty','why','confidence'}."""
    h=pricing['horizon']; out=[]; by_id={f"{r['card_id']}#{r['price_type']}":r for r in rows}
    for pos in positions:
        alert=('your price alert hit: '+', '.join(pos['alerts'])) if pos.get('alerts') else None
        if not pos.get('qty'):  # watchlist: only its alerts matter
            if alert: out.append({'action':'CHECK','id':pos['id'],'name':pos['name'],'price':pos.get('market'),'qty':None,
                                  'why':alert+' (watchlist) — check it before buying','confidence':'—'})
            continue
        r=by_id.get(pos['id']) or {}
        price=r.get('target_sell') or pos.get('market')
        if pos['signal'] in ('SELL','TRIM') and price and sale_net(price,pricing)<pricing.get('min_profit',1.0):  # not worth a single sale
            out.append({'action':'BUNDLE','id':pos['id'],'name':pos['name'],'price':price,'qty':pos['qty'],
                        'why':f"one copy on its own nets only {money(sale_net(price,pricing))} after fees and shipping; "
                              "sell these in a lot or add them to a bigger order",'confidence':'Medium'})
        elif pos['signal'] in ('SELL','TRIM'):
            out.append({'action':'SELL' if pos['signal']=='SELL' else 'SELL SOME','id':pos['id'],'name':pos['name'],
                        'price':price,'qty':pos['qty'],'why':pos['detail'],'confidence':'Medium'})
        if alert and out and out[-1]['id']==pos['id']: out[-1]['why']+=' · '+alert  # one row per card
        elif alert:
            out.append({'action':'CHECK','id':pos['id'],'name':pos['name'],'price':pos.get('market'),'qty':pos['qty'],
                        'why':alert,'confidence':'—'})
    held={p['id'] for p in positions if p.get('qty')}
    curves=load_release_curves()
    presell_win={label:next((t['win'] for t in c.get('trades') or () if t['kind']=='presell' and t['from']==-7),None) for label,c in curves.items()}
    for o in release_opportunities(rows,pricing,curves):
        if o['action']!='PRE-SELL': continue
        r=o['row']; rid=f"{r['card_id']}#{r['price_type']}"; c=_curve_for(r,curves)
        label=next((k for k,v in curves.items() if v is c),None)
        out.append({'action':'SELL NOW' if rid in held else 'PRE-SELL','id':rid,'name':r['name'],'price':r['latest_price'],
                    'qty':next((p['qty'] for p in positions if p['id']==rid),None),
                    'why':f"new set: expected {o['move']:+.0f}% by day {o['by_day']} — sell copies you have or will open now",
                    'confidence':confidence_label(presell_win.get(label))})
        if sum(1 for a in out if a['action']=='PRE-SELL')>=8: break  # the CYCLE view lists them all
    for o in [o for o in release_opportunities(rows,pricing,curves) if o['action']=='LONG-TERM BUY'][:10]:
        r=o['row']
        out.append({'action':'LONG-TERM BUY','id':f"{r['card_id']}#{r['price_type']}",'name':r['name'],'price':r.get('max_buy'),'qty':r.get('qty'),
                    'why':o['note'],'confidence':'Low'})
    for r in buy_list(rows,'Expected profit buying now ($/copy)',price_min=RANK_MIN_PRICE,min_changes=6,buyable_only=True,limit=10,hide_reprints=True):
        out.append({'action':'BUY NOW','id':f"{r['card_id']}#{r['price_type']}",'name':r['name'],'price':r.get('low_price'),'qty':r.get('qty'),
                    'why':f"listing is under your {r.get('low_cond') or 'NM'} limit; about {money(r.get('exp_profit_low'))} profit per copy expected; "
                          f"then list at {money(r.get('target_sell'))}",'confidence':confidence_label(r.get('win'))})
    arb=sorted((r for r in rows if not r.get('flags') and any(n.startswith('ARB') for n in buylist_signals(r,pricing))),
               key=lambda r:-(r['buylist']-r['low_price']))[:8]
    for r in arb:
        out.append({'action':'BUY → SELL TO CK','id':f"{r['card_id']}#{r['price_type']}",'name':r['name'],'price':r['low_price'],'qty':1,
                    'why':f"Card Kingdom pays {money(r['buylist'])} cash — about {money(r['buylist']-r['low_price']-pricing['ship_in']-pricing['cost'])} profit "
                          "after inbound shipping and supplies; check the listing is Near Mint and CK is still buying",'confidence':'Medium'})
    for r in buy_list(rows,'Expected profit at Max buy ($/copy)',price_min=RANK_MIN_PRICE,min_changes=6,limit=60,hide_reprints=True):
        if r.get('buyable'): continue
        out.append({'action':'TRADE-IN PRICE','id':f"{r['card_id']}#{r['price_type']}",'name':r['name'],'price':r['max_buy'],'qty':r.get('qty'),
                    'why':f"pay up to {max_buy_text(r)} for trade-ins/collections; about {money(r.get('exp_profit_max_buy'))} profit per copy; "
                          f"list at {money(r.get('target_sell'))}",'confidence':confidence_label(r.get('win'))})
        if sum(1 for a in out if a['action']=='TRADE-IN PRICE')>=20: break
    return out[:limit]

# --- Saved rankings: computed once per data change, reloaded at startup ---
RANKINGS_CACHE_VERSION = 6   # bump when ranking rules change so stale caches are recomputed
RANKINGS_CACHE_MAX_AGE_DAYS = 3
_RANKING_FIELDS = ('card_id','card_name','name','game','printing','price_type','latest_price','low_price','latest_date',
                   'age_days','observations','obs_30d','series_count','return_7d','return_30d','drawdown_30d','sharpe_30d',
                   'opportunity_score','consecutive_returns','jump_share','volatility_30d','price_changes_30d','flags',
                   'set_code','psr','autocorr_1','fdr_q','buylist','buylist_change_30d','eu_price','eu_change_30d','return_sd_30d','variant',
                   'days_since_release')

def rankings_path(): return ROOT/'rankings_cache.json.gz'

def rankings_signature(store, risk_free):
    """Fingerprint of everything rankings depend on: synced data, MTGJSON import, risk-free rate, rule version."""
    return json.dumps([RANKINGS_CACHE_VERSION,store.get_setting('tcgcsv_dataset_marker',''),store.get_setting('tcgcsv_categories',''),
                       store.get_setting('mtgjson_history_import',''),round(float(risk_free),6)])

def save_rankings(data, signature):
    """Persist the fresh ranking rows compactly (gzip JSON); the GUI never needs the stale ones."""
    rows=data['fresh']; index={id(r):i for i,r in enumerate(rows)}
    payload={'signature':signature,'saved_at':utc(),'saved_epoch':time.time(),'fields':_RANKING_FIELDS,
             'rows':[[r.get(f) for f in _RANKING_FIELDS] for r in rows],
             'sharpe_all':[index[id(r)] for r in data['sharpe_all']],
             'opportunities_all':[index[id(r)] for r in data['opportunities_all']],
             'diagnostics':data.get('diagnostics',{}),'indices':data.get('indices',{})}
    path=rankings_path(); tmp=path.with_suffix('.partial')
    with gzip.open(tmp,'wt',encoding='utf-8',compresslevel=1) as f: json.dump(payload,f,separators=(',',':'))
    tmp.replace(path)

def load_rankings(signature):
    """Saved rankings if they match `signature` and are recent enough, else None."""
    try:
        with gzip.open(rankings_path(),'rt',encoding='utf-8') as f: payload=json.load(f)
    except (OSError,ValueError,EOFError):
        return None
    if (payload.get('signature')!=signature or payload.get('fields')!=list(_RANKING_FIELDS)
            or time.time()-float(payload.get('saved_epoch',0))>RANKINGS_CACHE_MAX_AGE_DAYS*86400):
        return None
    rows=[dict(zip(_RANKING_FIELDS,values)) for values in payload['rows']]
    sharpe_all=[rows[i] for i in payload['sharpe_all']]; opportunities_all=[rows[i] for i in payload['opportunities_all']]
    return {'all':rows,'fresh':rows,'sharpe_all':sharpe_all,'opportunities_all':opportunities_all,
            'sharpe':[r for r in sharpe_all if not r['flags']],
            'opportunities':[r for r in opportunities_all if not r['flags']],
            'excluded':[r for r in rows if r['flags']],
            'diagnostics':payload.get('diagnostics',{}),'indices':payload.get('indices',{}),'saved_at':payload.get('saved_at')}

def compute_market_views(store, risk_free, progress=None):
    """Build and save the rankings; forecast models and the strategy backtest that are missing for today's data
    are built in the same scan."""
    hint=str(store.get_setting('tcgcsv_dataset_time','') or '')[:10]
    models=backtest=None; pricing=stored_pricing(store)
    ensure_daily_history(store,lambda msg: progress(0,0,msg) if progress else None)
    with ReadOnlyStore() as reader:
        need_models=hint and any(load_forecast_model(h,hint) is None for h in FORECAST_HORIZONS)
        need_backtest=hint and load_backtest(hint,pricing) is None
        if need_models or need_backtest:
            data,models,backtest=build_market_views(reader,risk_free,hint,progress=progress,pricing=pricing if need_backtest else None)
        else:
            data=build_market_rankings(reader,progress=progress,risk_free=risk_free)
    save_rankings(data,rankings_signature(store,risk_free))
    for model in (models or {}).values(): save_forecast_model(model)
    if backtest: save_backtest(backtest)
    record_new_variants(store,data['fresh'])
    with ReadOnlyStore() as reader: save_release_curves(release_curves(reader,pricing=pricing),longrun_curves(reader))
    return data,models

def precompute_market_views(store, report=print):
    """Build and save rankings and today's forecast model if the data changed (used by the background sync)."""
    risk_free=float(store.get_setting('pricing_risk_free',DEFAULT_RISK_FREE_PCT))/100.0
    horizon=int(float(store.get_setting('pricing_horizon',DEFAULT_PRICING['horizon'])))
    ensure_daily_history(store,report)
    signature=rankings_signature(store,risk_free)
    data=load_rankings(signature)
    if data is None:
        report('Precomputing rankings, indices and forecast models in one pass so the app opens with them ready…')
        data,models=compute_market_views(store,risk_free)
        report(f"Rankings saved: {len(data['fresh']):,} priced printings"+(f"; forecast models saved" if models else ''))
    dates=[r['latest_date'] for r in data['fresh'] if r.get('latest_date')]
    if dates and any(load_forecast_model(h,max(dates)) is None for h in FORECAST_HORIZONS):
        report('Building the 7/14/30-day forecast models (one pass over the price history)…')
        with ReadOnlyStore() as reader:
            for model in build_forecast_models(reader,FORECAST_HORIZONS,max(dates)).values(): save_forecast_model(model)
        report('Forecast models saved')
    pricing=stored_pricing(store)
    if dates and load_backtest(max(dates),pricing) is None:
        report('Replaying the buy rules on past prices (strategy backtest)…')
        with ReadOnlyStore() as reader: save_backtest(run_strategy_backtest(reader,pricing,max(dates)))
        report('Strategy backtest saved')
    # The buy/sell prices for every printing, so the app opens with today's list in seconds (same inputs the app uses).
    model=load_forecast_model(horizon,max(dates)) if dates else None
    if model:
        data['signature']=signature; rows=data['fresh']
        row_index={(r['card_id'],r['price_type']):r for r in rows}; by_card={}
        for r in rows: by_card.setdefault(r['card_id'],[]).append(r)
        exposure=portfolio_exposure(compute_positions(store,row_index,by_card,model,pricing))
        key=pricing_cache_key(data,model,pricing,exposure,rows)
        if key and load_pricing_cache(key,len(rows)) is None:
            report('Working out buy/sell prices for every printing so the app opens quickly…')
            save_pricing_cache(key,annotate_with_pricing(rows,model,pricing,exposure)); report('Buy/sell prices saved')

def forecast_for(model, return_30d, return_7d, price, printing, changes=None, sd=None, variant=None, age=None):
    """Forecast distribution for a printing: its most specific bucket, shrunk toward the broader ones.

    Each bucket's outcome counts get FORECAST_PRIOR pseudo-samples drawn from its parent's (already
    shrunk) distribution, so a thin bucket leans on the broader evidence and a large one keeps its own
    shape. This is the posterior mean under a Dirichlet prior and fixes the overconfidence of raw buckets.
    Inputs are percentages, as in the metrics.
    """
    if not model or not price: return None
    vset=model.get('_vset')
    if vset is None: vset=model['_vset']=frozenset(model.get('variants') or ())
    keys=forecast_keys(None if return_30d is None else return_30d/100.0,
                       None if return_7d is None else return_7d/100.0,price,printing,changes,sd,variant if variant in vset else None,age)
    chain=tuple(k for k in keys if (model['buckets'].get(k) or {}).get('n'))
    return _blended_forecast(model,chain) if chain else None

def _blended_forecast(model, chain):
    prepared=model.setdefault('_prepared',{})  # one prepared distribution per bucket chain, shared by every row using it
    fc=prepared.get(chain)
    if fc is None:
        bucket=model['buckets'][chain[0]]; parent=_blended_forecast(model,chain[1:]) if len(chain)>1 else None
        weights={b:float(c) for b,c in bucket['bins']}; total=float(bucket['n'])
        if parent:
            scale=FORECAST_PRIOR/parent['total']
            for b,w in parent['bins']: weights[b]=weights.get(b,0.0)+w*scale
            total+=FORECAST_PRIOR
        h=model['horizon']
        fc=_prepare_forecast({'key':chain[0],'n':bucket['n'],'total':total,'bins':sorted([b,w] for b,w in weights.items()),
                              'horizon':h,'ess':bucket['n']*min(1.0,FORECAST_STEP_DAYS/h),
                              'cal':_model_calibration(model,chain)})
        prepared[chain]=fc
    return fc

def _model_calibration(model, chain=()):
    """Interpolation table of the model's recalibration map for this bucket chain: per liquidity tier when the map is
    a {tier: knots} dict (falling back to '*'), or one global list of knots from older models."""
    cache=model.get('_cal')
    if not isinstance(cache,dict): cache=model['_cal']={}
    cal=model.get('calibration_map'); tier=_tier_of(chain) if isinstance(cal,dict) else '*'
    if tier not in cache:
        cache[tier]=_calibration_xy((cal.get(tier) or cal.get('*')) if isinstance(cal,dict) else cal)
    return cache[tier]

def _prepare_forecast(fc):
    """Add cumulative weights so quantile and tail lookups are binary searches (ranking 200k rows needs this)."""
    if 'cum' not in fc:
        values=[b for b,_ in fc['bins']]; cum=[]; run=0.0
        for _,c in fc['bins']:
            run+=c; cum.append(run)
        total=fc.setdefault('total',float(fc['n'])); cal=fc.get('cal')
        if cal:
            # Mean of the calibrated distribution: calibrated survival S'(v) = g(S(v)) gives each bin its mass.
            mean=0.0; before=1.0
            for b,c in zip(values,cum):
                after=_apply_xy(cal,max(0.0,(total-c)/total)); mean+=b*(before-after); before=after
            mean*=_FORECAST_BIN
        else:
            mean=sum(b*c for b,c in fc['bins'])*_FORECAST_BIN/total
        fc.update(values=values,cum=cum,mean=mean)
    return fc

def _raw_quantile(fc, q):
    return fc['values'][min(bisect.bisect_left(fc['cum'],q*fc['total']-1e-9),len(fc['values'])-1)]*_FORECAST_BIN

def forecast_quantile(fc, q):
    """Forward return with calibrated probability q of ending at or below it."""
    fc=_prepare_forecast(fc)
    return _raw_quantile(fc,1.0-_invert_xy(fc['cal'],1.0-q) if fc.get('cal') else q)

def forecast_prob_above(fc, threshold):
    """Calibrated probability the forward return is above threshold."""
    fc=_prepare_forecast(fc)
    i=bisect.bisect_right(fc['values'],(threshold+1e-12)/_FORECAST_BIN)
    raw=(fc['total']-(fc['cum'][i-1] if i else 0.0))/fc['total']
    return _apply_xy(fc['cal'],raw) if fc.get('cal') else raw

def forecast_mean(fc): return _prepare_forecast(fc)['mean']

_EMPTY_ANNOTATION = {'p_rise':None,'win':None,'buyable':False,'max_buy':None,'p_sold':None,'max_qty':None,
                     'exp_profit_low':None,'exp_profit_max_buy':None,'target_sell':None,'target_fill':None,'quick_sell':None,'min_sell':None,
                     'low_cond':None,'max_buy_cond':None,'qty':None,'qty_limit':None,'q10_price':None,'q90_price':None}

def worth_it(profit, cost, pricing):
    """Expected profit per copy clears both floors: min_profit dollars and min_roi percent of the all-in cost."""
    return profit is not None and profit>=pricing.get('min_profit',0.0) and profit>=pricing.get('min_roi',0.0)/100.0*cost

def annotate_with_pricing(rows, model, pricing, exposure=None):
    """Per-row trade arithmetic for filtering and the buy list (runs off the GUI thread).

    win is Win @ low (or at market when there is no low), valuing the cheapest listing at its inferred
    condition; buyable means that listing is at or under the Max buy for that condition; exp_profit_* is the
    expected net per copy (after every selling cost and inbound shipping) if it sells at the forecast mean,
    buying at the cheapest listing or at the Near Mint Max buy. qty is the suggested number of copies after
    the Kelly, per-card, per-set, budget and sell-through limits, given what the portfolio already holds.
    """
    exposure=exposure or {'cards':{},'sets':{},'total':0.0}; ship_in=pricing['ship_in']; out=[]
    for r in rows:
        fc=forecast_for(model,r.get('return_30d'),r.get('return_7d'),r.get('latest_price'),r.get('printing',''),r.get('price_changes_30d'),
                        r.get('return_sd_30d'),r.get('variant'),r.get('days_since_release'))
        t=pricing_targets(r['latest_price'],r.get('low_price'),fc,pricing,r.get('price_changes_30d')) if fc else None
        if not t:
            out.append(_EMPTY_ANNOTATION); continue
        low=r.get('low_price'); cond=t['low_cond']; by_cond=t['max_buy_cond']
        buyable=bool(low and by_cond.get(cond) and low<=by_cond[cond])
        buy,value=(low,r['latest_price']*condition_share(pricing,cond)) if buyable else (t['max_buy'],r['latest_price'])
        if buy and not buyable:
            fc_stats=fc['_stats']; target=best_list_price(fc,fc_stats,value,buy+ship_in,pricing,t['p_sold'])
        else: target=(t['target_sell'],t['target_fill'],t['target_ev'])
        qty,limit=suggested_quantity(t,buy,value,pricing,exposure['cards'].get((r['card_id'],r['price_type']),0.0),
                                     exposure['sets'].get((r.get('game'),r.get('set_code')),0.0),exposure['total']) if buy else (None,None)
        profit=t['exp_sale_net_low']-(low+ship_in) if buyable else t['exp_sale_net']-(t['max_buy']+ship_in) if t['max_buy'] else None
        cost=(low if buyable else t['max_buy'] or 0.0)+ship_in
        out.append({'p_rise':t['p_rise'],
                    # Win shown for what you would do: buy the listing now, or buy in at Max buy.
                    'win':t['win_at_low'] if buyable else t['p_sold']*t['profit_at_max_buy'] if t['max_buy'] else t['win_at_market'],
                    'worth':worth_it(profit,cost,pricing),
                    'buyable':buyable,'max_buy':t['max_buy'],'p_sold':t['p_sold'],'max_qty':t['max_qty'],
                    'exp_profit_low':t['exp_sale_net_low']-(low+ship_in) if low else None,
                    'exp_profit_max_buy':t['exp_sale_net']-(t['max_buy']+ship_in) if t['max_buy'] else None,
                    'target_sell':target[0],'target_fill':target[1],'quick_sell':t['quick_sell'],'min_sell':t['min_sell'],
                    'low_cond':cond if low else None,'max_buy_cond':by_cond,'qty':qty,'qty_limit':limit,
                    'q10_price':t['q10_price'],'q90_price':t['q90_price']})
    return out

# The buy/sell arithmetic for ~200k printings takes about half a minute; it is saved and reused until the prices,
# forecast, your settings or your holdings change, so the app opens with today's list in seconds.
PRICING_CACHE_VERSION = 1
def _pricing_cache_path(): return ROOT/'pricing_cache.pickle'

def pricing_cache_key(data, model, pricing, exposure, rows):
    if not data.get('signature') or not model or not rows: return None
    parts=(PRICING_CACHE_VERSION,FORECAST_MODEL_VERSION,data['signature'],model.get('data_date'),model.get('samples'),model.get('horizon'),
           model.get('built_at'),sorted(pricing.items()),sorted((str(k),round(v,2)) for k,v in exposure['cards'].items()),
           sorted((str(k),round(v,2)) for k,v in exposure['sets'].items()),round(exposure['total'],2),
           len(rows),rows[0].get('card_id'),rows[-1].get('card_id'))
    return hashlib.sha1(json.dumps(parts,default=str).encode('utf-8')).hexdigest()

def load_pricing_cache(key, count):
    if not key: return None
    try:
        with open(_pricing_cache_path(),'rb') as f: saved=pickle.load(f)  # written only by this app, in its own data folder
    except (OSError,pickle.UnpicklingError,EOFError,AttributeError,ValueError): return None
    if saved.get('key')!=key or len(saved.get('results') or ())!=count: return None
    return saved['results']

def save_pricing_cache(key, results):
    if not key: return
    tmp=_pricing_cache_path().with_suffix('.tmp')
    try:
        with open(tmp,'wb') as f: pickle.dump({'key':key,'results':results},f,protocol=pickle.HIGHEST_PROTOCOL)
        os.replace(tmp,_pricing_cache_path())
    except OSError: pass

BUY_LIST_SORTS = {
    'Expected profit buying now ($/copy)':lambda r:r['exp_profit_low'] if r.get('exp_profit_low') is not None else -1e9,
    'Expected return buying now (%)':lambda r:r['exp_profit_low']/r['low_price'] if r.get('exp_profit_low') is not None and r.get('low_price') else -1e9,
    'Expected profit at Max buy ($/copy)':lambda r:r.get('exp_profit_max_buy') or -1e9,
    'Win @ low':lambda r:r.get('win') or 0.0,
    'Chance of rise':lambda r:r.get('p_rise') or 0.0,
    'Liquidity (trading days)':lambda r:r.get('price_changes_30d') or 0,
    'Max buy as % of market (easiest to source)':lambda r:(r.get('max_buy') or 0.0)/r['latest_price'] if r.get('latest_price') else 0.0,
    'Card Kingdom buylist above listing ($/copy)':lambda r:(r['buylist']-r['low_price']) if r.get('buylist') and r.get('low_price') else -1e9,
    'Card Kingdom buylist rising (30d %)':lambda r:r['buylist_change_30d'] if r.get('buylist_change_30d') is not None else -1e9,
    'EDHREC popularity (Commander demand)':lambda r:-(r.get('edhrec') or 1e9),
    'Cardmarket lead (EU 30d − US 30d)':lambda r:(r['eu_change_30d']-(r.get('return_30d') or 0.0)) if r.get('eu_change_30d') is not None else -1e9,
}

def buy_list(rows, sort_key, game='All', price_min=None, price_max=None, min_changes=None, buyable_only=False, limit=300, set_code=None,
             hide_reprints=False, variant=None):
    """Cards worth acquiring: annotated, not excluded, with a Max buy that meets the win target and room to buy."""
    keyfunc=BUY_LIST_SORTS[sort_key]; picked=[]
    for r in rows:
        if r.get('flags') or not r.get('max_buy') or (buyable_only and not r.get('buyable')): continue
        if r.get('qty')==0 and r.get('qty_limit') in ('card limit','set limit','budget'): continue  # no room left to buy
        if hide_reprints and r.get('reprint'): continue
        age=r.get('days_since_release')
        if hide_reprints and age is not None and -60<=age<42: continue  # new sets slide for weeks after release: see release curves
        if r.get('worth') is False: continue  # expected profit under your minimum per copy
        if r.get('observations') is not None and _history_note(r): continue  # the card checker would say NOT ENOUGH HISTORY YET
        if game!='All' and r.get('game')!=game: continue
        if set_code and str(r.get('set_code') or '').upper()!=set_code.upper(): continue
        if variant and variant.casefold() not in str(r.get('variant') or 'Regular').casefold(): continue
        price=r.get('latest_price') or 0
        if (price_min is not None and price<price_min) or (price_max is not None and price>price_max): continue
        if min_changes is not None and (r.get('price_changes_30d') or 0)<min_changes: continue
        picked.append(r)
    return sorted(picked,key=lambda r:(-keyfunc(r),r['name']))[:limit]

def max_buy_text(r, conds=('NM','LP','MP')):
    by=r.get('max_buy_cond') or {'NM':r.get('max_buy')}
    return ' · '.join(f"{c} {money(by[c]) if by.get(c) else '—'}" for c in conds if c in by)

def row_notes(r, pricing=None, eu=False):
    """Caveats and side signals for a row: announced reprint, ban, Card Kingdom buylist, Cardmarket lead."""
    notes=[]
    if r.get('reprint'): notes.append(f"REPRINT announced ({r['reprint']}): prices usually fall")
    cycle=release_note(r)
    if cycle: notes.append(cycle)
    if r.get('legal_change'): notes.append(f"legality just changed: {r['legal_change']}")
    notes+=buylist_signals(r,pricing or DEFAULT_PRICING)
    if eu and r.get('eu_change_30d') is not None and r['eu_change_30d']>=15 and r['eu_change_30d']-(r.get('return_30d') or 0)>=10:
        notes.append(f"Cardmarket {r['eu_change_30d']:+.0f}% in 30d vs US {r.get('return_30d') or 0:+.0f}%")
    return notes

def buy_recommendation(r, horizon, pricing=None, eu=False):
    """One-line action for a buy-list row, followed by its caveats and side signals."""
    notes=row_notes(r,pricing,eu)
    return _buy_action(r,horizon)+(' · '+' · '.join(notes) if notes else '')

def _buy_action(r, horizon):
    # Prices, quantity and target sell have their own columns; this states the action and its caveat.
    if r.get('buyable'):
        cond=r.get('low_cond') or 'NM'; low=r.get('low_price'); limit=(r.get('max_buy_cond') or {}).get(cond) or r['max_buy']
        if cond=='NM':
            return (f"BUY NOW: listing {money(low)} ≤ NM max buy {money(limit)} — confirm it is Near Mint; list at "
                    f"{money(r.get('target_sell'))} (about {(r.get('target_fill') or 0)*100:.0f}% chance it sells within {horizon} days; keep it listed if not), break-even {money(r.get('min_sell'))}")
        return (f"BUY NOW if {cond} or better: listing {money(low)} is {low/r['latest_price']*100:.0f}% of market, priced like {cond}; "
                f"{cond} max buy {money(limit)}, break-even {money(r.get('min_sell'))}")
    return (f"BUY-IN TARGET: pay up to {max_buy_text(r)} for trade-ins/collections; "
            f"then list at {money(r.get('target_sell'))} (about {(r.get('target_fill') or 0)*100:.0f}% chance it sells within {horizon} days; keep it listed if not)")


# --- Terminal analytics: movers, breadth, sets, positions and alerts (all from the ranked rows) ---
MOVER_MIN_PRICE = 5.0     # movers lists skip cheap printings, whose % moves are mostly noise
MOVER_MIN_CHANGES = 6     # ...and printings that trade on fewer than 6 of 30 days

def _median(values):
    values=sorted(v for v in values if v is not None)
    if not values: return None
    mid=len(values)//2
    return values[mid] if len(values)%2 else (values[mid-1]+values[mid])/2

def market_movers(rows, limit=15, min_price=MOVER_MIN_PRICE, min_changes=MOVER_MIN_CHANGES, game='All'):
    """(gainers, losers) by 7-day change among tradeable, non-excluded printings."""
    pool=[r for r in rows if not r.get('flags') and r.get('return_7d') is not None
          and (r.get('latest_price') or 0)>=min_price and (r.get('price_changes_30d') or 0)>=min_changes
          and (game=='All' or r.get('game')==game)]
    pool.sort(key=lambda r:(r['return_7d'],r['name']))
    return [r for r in pool[::-1][:limit] if r['return_7d']>0],[r for r in pool[:limit] if r['return_7d']<0]

def index_summary(index_rows):
    """Level and 1/7/30-day changes (%) of a chained index, plus the latest day's breadth."""
    if not index_rows: return None
    last=index_rows[-1]; by_day={row[0]:row for row in index_rows}
    def change(days,col):
        target=(date.fromisoformat(last[0])-timedelta(days=days)).isoformat()
        prior=max((d for d in by_day if d<=target),default=None)
        return None if prior is None else (last[col]/by_day[prior][col]-1)*100
    return {'day':last[0],'ew':last[1],'pw':last[2],'n':last[3],'adv':last[4],'dec':last[5],
            **{f'ew_{d}d':change(d,1) for d in (1,7,30)},**{f'pw_{d}d':change(d,2) for d in (1,7,30)}}

def market_breadth(rows):
    """Per game: printings $1+, share up over 7 days, and how many sit at a 30-day high or are buyable now."""
    out={}
    for r in rows:
        if r.get('flags') or (r.get('latest_price') or 0)<RANK_MIN_PRICE: continue
        g=out.setdefault(r['game'],{'n':0,'up_7d':0,'down_7d':0,'at_high':0,'buyable':0,'significant':0})
        g['n']+=1
        r7=r.get('return_7d')
        if r7 is not None and r7>0.05: g['up_7d']+=1
        elif r7 is not None and r7<-0.05: g['down_7d']+=1
        if r.get('drawdown_30d') is not None and r['drawdown_30d']>-0.01 and (r.get('obs_30d') or 0)>=20: g['at_high']+=1
        if r.get('buyable'): g['buyable']+=1
        if r.get('fdr_q') is not None and r['fdr_q']<=SIGNIFICANCE_FDR and (r.get('sharpe_30d') or 0)>0: g['significant']+=1
    return out

def _basket_change(items, key):
    """Price-weighted % change of holding one copy of each printing (most printings do not trade in a given week,
    so a median move is usually 0 and says nothing)."""
    now=then=0.0
    for r in items:
        change=r.get(key)
        if change is None or change<=-100: continue
        now+=r['latest_price']; then+=r['latest_price']/(1+change/100.0)
    return (now/then-1)*100 if then>0 else None

def set_summary(rows, names=None):
    """Sector view: one row per (game, set) of non-excluded $1+ printings, with basket moves and breadth."""
    names=names or {}; groups={}
    for r in rows:
        if r.get('flags') or (r.get('latest_price') or 0)<RANK_MIN_PRICE: continue
        groups.setdefault((r['game'],r.get('set_code') or '?'),[]).append(r)
    out=[]
    for (game,code),items in groups.items():
        r7=[r['return_7d'] for r in items if r.get('return_7d') is not None]
        out.append({'game':game,'set_code':code,'set_name':names.get((game,code),''),'printings':len(items),
                    'change_7d':_basket_change(items,'return_7d'),'change_30d':_basket_change(items,'return_30d'),
                    'up_share':sum(1 for v in r7 if v>0.05)/len(r7) if r7 else None,
                    'value':sum(r['latest_price'] for r in items),
                    'median_liquidity':_median(r.get('price_changes_30d') for r in items),
                    'median_rise':_median(r.get('p_rise') for r in items),
                    'buyable':sum(1 for r in items if r.get('buyable'))})
    return out

def variant_summary(rows):
    """Market view by treatment (game, variant): printings, basket moves, liquidity and buy-now count, plus an example."""
    groups={}
    for r in rows:
        if r.get('flags') or (r.get('latest_price') or 0)<RANK_MIN_PRICE: continue
        groups.setdefault((r['game'],r.get('variant') or 'Regular'),[]).append(r)
    out=[]
    for (game,variant),items in groups.items():
        r7=[r['return_7d'] for r in items if r.get('return_7d') is not None]
        example=max(items,key=lambda r:r['latest_price'])
        out.append({'game':game,'set_code':variant,'set_name':f"e.g. {example['name']} [{example.get('set_code') or ''}]",
                    'printings':len(items),'change_7d':_basket_change(items,'return_7d'),'change_30d':_basket_change(items,'return_30d'),
                    'up_share':sum(1 for v in r7 if v>0.05)/len(r7) if r7 else None,'value':sum(r['latest_price'] for r in items),
                    'median_liquidity':_median(r.get('price_changes_30d') for r in items),
                    'median_rise':_median(r.get('p_rise') for r in items),'buyable':sum(1 for r in items if r.get('buyable'))})
    return out

def record_new_variants(store, rows, report=lambda _m: None):
    """Note each treatment seen for the first time (a set introducing a new variant) as a dated market event."""
    seen={}
    for r in rows:
        if r.get('variant') and r['variant']!='Regular': seen.setdefault((r['game'],r['variant']),[]).append(r)
    try: known={tuple(x) for x in json.loads(store.get_setting('known_variants','[]') or '[]')}
    except ValueError: known=set()
    fresh=[k for k in seen if k not in known]
    if known and fresh:
        today=date.today().isoformat(); events=[]
        for game,variant in fresh:
            ex=max(seen[(game,variant)],key=lambda r:r['latest_price'] or 0)
            events.append((today,game,'new variant',variant,f"{len(seen[(game,variant)])} printing(s), e.g. {ex['name']} [{ex.get('set_code') or ''}] "
                                                              f"at {money(ex['latest_price'])}; forecasts lean on similar cards until it has its own history"))
        store.executemany('INSERT OR IGNORE INTO market_events(day,game,kind,subject,detail) VALUES(?,?,?,?,?)',events)
        report(f'{len(events)} new variant(s): '+', '.join(v for _g,v in fresh[:8]))
    store.setting('known_variants',json.dumps(sorted(known|set(seen))))
    return fresh if known else []

def position_signal(market, low, qty, cost, t, pricing):
    """Hold/sell guidance for a held printing from the forecast; returns (signal, explanation).

    Selling now nets the quick-sale price (just under the cheapest listing) after fees and per-card cost;
    holding nets the forecast mean price at the horizon after the same costs. TRIM when you hold more
    copies than are expected to sell within the horizon.
    """
    if not market: return 'NO DATA','no current market price'
    if not t: return 'HOLD','no forecast for this printing yet'
    h=pricing['horizon']
    sell_now=sale_net(t['quick_sell'],pricing); hold=t['exp_sale_net']
    edge=hold-sell_now
    if qty and t.get('max_qty') is not None and qty>max(1,t['max_qty']):
        likely=(f"only about {t['max_qty']} {'is' if t['max_qty']==1 else 'are'} likely to sell" if t['max_qty'] else 'this card rarely sells; none are likely to sell')
        return 'TRIM',f"you hold {qty} but {likely} in {h} days; list the extras at {money(t['quick_sell'])}"
    if edge<=0:
        return 'SELL',f"a quick sale now puts {money(sell_now)} in your pocket vs about {money(hold)} if you wait {h} days"
    gain='' if cost is None else (f"; selling now would make {money(sell_now-cost)} per copy" if sell_now>=cost else
                                  f"; selling now would lose {money(cost-sell_now)} per copy")
    return 'HOLD',f"waiting {h} days should net about {money(hold)} vs {money(sell_now)} now (+{money(edge)}){gain}"

def alert_hits(market, alert_above, alert_below):
    hits=[]
    if market is not None and alert_above is not None and market>=alert_above: hits.append(f'≥ {money(alert_above)}')
    if market is not None and alert_below is not None and market<=alert_below: hits.append(f'≤ {money(alert_below)}')
    return hits

# --- Catalysts: set releases from TCGCSV groups (both games) and Scryfall (MTG), both free ---
SCRYFALL_SETS = 'https://api.scryfall.com/sets'
# TCGCSV re-stamps ongoing promo/product groups whenever an item is added, so they are not releases.
_PERENNIAL_GROUP = re.compile(r'promo|series|box sets|\bcards\b|decks|reprints|exclusive|miscellaneous|oversize|playtest|'
                              r'partner pack|art series|player rewards|special guests|\bpop\b', re.I)
SCRYFALL_SET_TYPES = {'core','expansion','masters','draft_innovation','commander','funny','starter','eternal','alchemy'}

def store_set_info(store, rows):
    """rows: (game, code, name, released_on, set_type, source)."""
    now=utc()
    store.executemany('''INSERT INTO set_info(game,code,name,released_on,set_type,source,updated_at) VALUES(?,?,?,?,?,?,?)
        ON CONFLICT(game,code,source) DO UPDATE SET name=excluded.name,released_on=excluded.released_on,
        set_type=excluded.set_type,updated_at=excluded.updated_at''',[(*r,now) for r in rows])

def tcgcsv_group_set_rows(game, groups):
    rows=[]
    for g in groups:
        if not isinstance(g,dict) or g.get('groupId') is None: continue
        rows.append((game,str(g.get('abbreviation') or g['groupId']),str(g.get('name') or ''),
                     str(g.get('publishedOn') or '')[:10] or None,None,'tcgcsv'))
    return rows

def fetch_scryfall_sets():
    req=urllib.request.Request(SCRYFALL_SETS,headers={'User-Agent':USER_AGENT,'Accept':'application/json'})
    with urllib.request.urlopen(req,timeout=30) as r: payload=json.loads(r.read().decode('utf-8'))
    return [('MTG',str(s['code']).upper(),s.get('name') or '',s.get('released_at'),s.get('set_type'),'scryfall')
            for s in payload.get('data',[]) if not s.get('digital') and s.get('released_at') and s.get('set_type') in SCRYFALL_SET_TYPES]

def refresh_catalysts(store, report=lambda _m: None, include_tcgcsv=True):
    """Release calendar: Scryfall's MTG set list and TCGCSV's group lists (3 requests). Failures are reported, not raised."""
    count=0
    try:
        rows=fetch_scryfall_sets(); store_set_info(store,rows); count+=len(rows)
    except Exception as exc: report(f'Scryfall set list unavailable: {exc}')
    if include_tcgcsv:
        for category_id,game in TCGCSV_CATEGORIES:
            try:
                rows=tcgcsv_group_set_rows(game,tcgcsv_results(tcgcsv_json(f'{TCGCSV_BASE}/{category_id}/groups'),f'{game} groups'))
                store_set_info(store,rows); count+=len(rows)
            except Exception as exc: report(f'TCGCSV {game} group list unavailable: {exc}')
    store.setting('catalysts_epoch',time.time())
    return count

def catalyst_calendar(store, today=None, back_days=30, ahead_days=120):
    """Set releases from back_days ago to ahead_days ahead, one row per (game, set), Scryfall preferred for MTG."""
    today=today or datetime.now(timezone.utc).date()
    lo=(today-timedelta(days=back_days)).isoformat(); hi=(today+timedelta(days=ahead_days)).isoformat()
    rows=store.q('''SELECT game,code,name,released_on,set_type,source FROM set_info
                    WHERE released_on BETWEEN ? AND ? ORDER BY source''',(lo,hi))
    picked={}
    for game,code,name,released,set_type,source in rows:
        if source=='tcgcsv' and _PERENNIAL_GROUP.search(name or ''): continue
        # The same set often appears under both sources; 'scryfall' sorts first, so it wins for MTG.
        picked.setdefault((game,code),{'game':game,'set_code':code,'set_name':name,'released_on':released,
                                       'set_type':set_type or '','source':source,'days':(date.fromisoformat(released)-today).days})
    return sorted(picked.values(),key=lambda c:(c['released_on'],c['game'],c['set_name']))

def set_names(store):
    """{(game, set_code): set name} from TCGCSV groups, falling back to the catalog's stored group names."""
    try: names={(g,c):n for g,c,n in store.q("SELECT game,code,name FROM set_info WHERE source='tcgcsv' AND name<>''")}
    except sqlite3.OperationalError: names={}  # database not yet upgraded by this version
    if not names:
        for g,c,n in store.q("""SELECT game,set_code,json_extract(details,'$.group_name') FROM cards
                                WHERE item_type='card' AND game IN ('MTG','Pokémon','One Piece','Riftbound') GROUP BY game,set_code"""):
            if n: names[(g,c)]=n
    return names


def compute_positions(store, row_index, rows_by_card, model, pricing):
    """Portfolio rows with marks, liquidation value after costs, P/L, hold/sell signal, size-limit checks and alerts."""
    out=[]
    for cid,price_type,qty,cost,above,below,_added,name,game in store.q(
            "SELECT f.card_id,f.price_type,f.qty,f.cost,f.alert_above,f.alert_below,f.added_at,c.name,c.game "
            "FROM portfolio f JOIN cards c ON c.id=f.card_id ORDER BY f.qty>0 DESC,f.added_at DESC"):
        if price_type: r=row_index.get((cid,price_type))
        else:
            options=rows_by_card.get(cid) or []
            r=min(options,key=lambda x:_price_type_priority(x['price_type'])) if options else None
        market=r['latest_price'] if r else None; low=r.get('low_price') if r else None
        fc=forecast_for(model,r.get('return_30d'),r.get('return_7d'),market,r.get('printing',''),r.get('price_changes_30d'),
                        r.get('return_sd_30d'),r.get('variant'),r.get('days_since_release')) if r else None
        t=pricing_targets(market,low,fc,pricing,r.get('price_changes_30d')) if fc else None
        signal,detail=position_signal(market,low,qty,cost,t,pricing)
        cycle=release_note(r) if r else None
        if cycle and qty: detail=detail+' · '+cycle
        unit=sale_net(t['quick_sell'] if t else (low or market or 0),pricing) if market else None
        value=None if unit is None else max(0.0,unit)*qty
        out.append({'id':f"{cid}#{(r or {}).get('price_type') or price_type}",'card_id':cid,'price_type':price_type,
                    'row_type':(r or {}).get('price_type') or price_type,'set_code':(r or {}).get('set_code'),
                    'name':r['name'] if r else printing_label(name,price_type or RANK_PRICE_TYPE),'game':game,'qty':qty,'cost':cost,
                    'market':market,'low':low,'value':value,'pnl':None if value is None or cost is None or not qty else value-cost*qty,
                    'signal':signal,'detail':detail,'alerts':alert_hits(market,above,below),
                    'p_rise':t.get('p_rise') if t else None,'return_7d':r.get('return_7d') if r else None,
                    'return_30d':r.get('return_30d') if r else None,'alert_above':above,'alert_below':below})
    apply_position_limits(out,pricing)
    return out

def apply_position_limits(positions, pricing):
    """Turn HOLD into TRIM where a holding breaks the per-card or per-set capital limit (valued at market)."""
    capital=pricing['capital']; per_set={}
    for p in positions:
        if p['qty'] and p['market']: per_set[(p['game'],p.get('set_code'))]=per_set.get((p['game'],p.get('set_code')),0.0)+p['market']*p['qty']
    for p in positions:
        if not p['qty'] or not p['market'] or p['signal'] not in ('HOLD',): continue
        held=p['market']*p['qty']; in_set=per_set.get((p['game'],p.get('set_code')),0.0)
        if held>pricing['max_card']+0.005:
            p['signal']='TRIM'; p['detail']=(f"{money(held)} in this printing is over your {money(pricing['max_card'])} per-card limit; "
                                             f"sell {math.ceil((held-pricing['max_card'])/p['market'])}. "+p['detail'])
        elif capital>0 and in_set/capital*100>pricing['max_set_pct']+0.05:
            p['signal']='TRIM'; p['detail']=(f"set {p.get('set_code') or '?'} is {in_set/capital*100:.0f}% of capital "
                                             f"(limit {pricing['max_set_pct']:g}%). "+p['detail'])

def daily_brief_html(data, model, pricing, positions, catalysts, names=None, generated=None, health=()):
    """A self-contained HTML morning brief: indices, breadth, alerts, best buys, movers, releases, hot sets."""
    esc=lambda v: xml_escape(str(v))
    pct=lambda v: '—' if v is None else f'{v:+.1f}%'
    cls=lambda v: '' if v is None or abs(v)<0.05 else ('up' if v>0 else 'down')
    rows=data.get('fresh') or []; out=[]
    def table(title, heads, body):
        if not body: return
        out.append(f'<h2>{esc(title)}</h2><div class="wrap"><table><tr>'+''.join(f'<th>{esc(h)}</th>' for h in heads)+'</tr>')
        for cells in body:
            out.append('<tr>'+''.join(f'<td class="{c}">{esc(v)}</td>' for v,c in cells)+'</tr>')
        out.append('</table></div>')
    dates=[r['latest_date'] for r in rows if r.get('latest_date')]
    out.append(f"<h1>Card Market Terminal — daily brief</h1><p class='muted'>Prices as of {esc(max(dates) if dates else '—')} · "
               f"made {esc(generated or utc())}. Uses your settings: {pricing['fee_pct']:g}% + ${pricing['fee_fixed']:.2f} selling fee, shipping ${pricing['ship_plain']:.2f} "
               f"(${pricing['ship_tracked']:.2f} tracked from ${pricing['ship_threshold']:g}), ${pricing['cost']:.2f} supplies per card, "
               f"selling within {pricing['horizon']} days, aiming for a {pricing['win_pct']:g}% chance of profit. "
               "Every profit shown is after those costs. Estimates from past prices, not guarantees.</p>")
    for warning in health or ():
        out.append(f"<p class='down'><b>DATA:</b> {esc(warning)}</p>")
    try: todo=todays_actions(rows,positions,pricing,limit=25)
    except Exception: todo=[]  # the to-do list needs the annotated rows; the market sections below still work without it
    tone={'BUY NOW':'up','BUY → SELL TO CK':'up','LONG-TERM BUY':'up','TRADE-IN PRICE':''}
    table('What to do today (same list as the Today tab)',['Do this','Card','Price','Qty','Why','Confidence'],
          [[(a['action'],tone.get(a['action'],'down')),(a['name'],''),(money(a['price']),''),('—' if a['qty'] is None else a['qty'],''),
            (a['why'],''),(a['confidence'],'')] for a in todo])
    breadth=market_breadth(rows); body=[]
    for game,index_rows in (data.get('indices') or {}).items():
        s=index_summary(index_rows); b=breadth.get(game,{})
        if s: body.append([(game,''),(f"{s['ew']:.1f}",''),(pct(s['ew_1d']),cls(s['ew_1d'])),(pct(s['ew_7d']),cls(s['ew_7d'])),
                           (pct(s['ew_30d']),cls(s['ew_30d'])),(f"{b.get('up_7d',0):,} / {b.get('down_7d',0):,}",''),(f"{b.get('buyable',0):,}",'')])
    table('Market index (average price change of cards worth $1+; 100 = start of the chart)',
          ['Game','Index','1 day','7 days','30 days','Cards up / down 7 days','Under your max buy'],body)
    alerts=[p for p in positions if p['alerts'] or (p['qty'] and p['signal'] in ('SELL','TRIM'))]
    table('Portfolio alerts & signals',['Card','Qty','Market','Signal','Detail'],
          [[(p['name'],''),(p['qty'],''),(money(p['market']),''),(('ALERT '+', '.join(p['alerts'])) if p['alerts'] else {'TRIM':'SELL SOME'}.get(p['signal'],p['signal']),'down'),
            (p['detail'],'')] for p in alerts])
    held=[p for p in positions if p['qty']]
    if held:
        value=sum(p['value'] or 0 for p in held); cost=sum((p['cost'] or 0)*p['qty'] for p in held)
        out.append(f"<p>Holdings: {sum(p['qty'] for p in held):,} copies · worth if sold now {money(value)} · cost {money(cost)} · "
                   f"profit if sold <b class='{cls(value-cost)}'>{money(value-cost) if value>=cost else '−'+money(cost-value)}</b></p>")
    by_id={f"{r['card_id']}#{r['price_type']}":r for r in rows}
    held=[(p,by_id.get(p['id']) or {}) for p in positions if p['qty']]
    table('Holdings at risk (announced reprint or ban)',['Card','Qty','Market','Risk'],
          [[(p['name'],''),(p['qty'],''),(money(p['market']),''),('; '.join(row_notes({k:r.get(k) for k in ('reprint','legal_change')})),'down')]
           for p,r in held if r.get('reprint') or r.get('legal_change')])
    arb=sorted((r for r in rows if not r.get('flags') and any(n.startswith('ARB') for n in buylist_signals(r,pricing))),
               key=lambda r:-(r['buylist']-r['low_price']))[:15]
    table('Buy cheap, sell to Card Kingdom (listed for less than CK pays in cash; check it is Near Mint and CK is still buying)',
          ['Card','Set','Cheapest listing','CK pays','Difference (before shipping)'],
          [[(r['name'],''),(r.get('set_code') or '',''),(money(r['low_price']),''),(money(r['buylist']),''),(money(r['buylist']-r['low_price']),'up')] for r in arb])
    buys=buy_list(rows,'Expected profit buying now ($/copy)',price_min=RANK_MIN_PRICE,min_changes=6,buyable_only=True,limit=25,hide_reprints=True)
    table('Buy now (a listing is under your max buy for its likely condition; check the condition)',
          ['Card','Set','Market','Cheapest listing','Likely condition','Max buy (that condition)','Exp. profit','Chance of profit','Buy qty','List at'],
          [[(r['name'],''),(r.get('set_code') or '',''),(money(r['latest_price']),''),(money(r.get('low_price')),''),(r.get('low_cond') or '',''),
            (money((r.get('max_buy_cond') or {}).get(r.get('low_cond') or 'NM') or r['max_buy']),''),
            (money(r.get('exp_profit_low')),'up'),(f"{(r.get('win') or 0)*100:.0f}%",''),
            (f"{r.get('qty')} ({QTY_LIMIT_WORDS.get(r.get('qty_limit'),r.get('qty_limit'))})" if r.get('qty') is not None else '—',''),(money(r.get('target_sell')),'')] for r in buys])
    opps=[o for o in release_opportunities(rows,pricing) if o['action']!='WAIT'][:20]
    table('New sets (how similar new cards moved after release)',['Action','Card','Set','Age','Market','Typical move','Note'],
          [[(o['action'],'up' if o['action']=='BUY THE DIP' else 'down'),(o['row']['name'],''),(o['row'].get('set_code') or '',''),
            (f"{-o['row']['days_since_release']} days before" if o['row']['days_since_release']<0 else f"day {o['row']['days_since_release']}",''),
            (money(o['row']['latest_price']),''),(f"{o['move']:+.0f}% by day {o['by_day']}",''),(o['note'],'')] for o in opps])
    targets=buy_list(rows,'Expected profit at Max buy ($/copy)',price_min=RANK_MIN_PRICE,min_changes=6,limit=25,hide_reprints=True)
    table('Trade-in prices (most to pay for trade-ins and collections; cards that sell on 6+ days a month)',
          ['Card','Set','Market','Pay ≤ NM · LP · MP','Exp. profit','Chance of profit','List at (chance it sells)','Likely price range'],
          [[(r['name'],''),(r.get('set_code') or '',''),(money(r['latest_price']),''),(max_buy_text(r),''),(money(r.get('exp_profit_max_buy')),'up'),
            (f"{(r.get('win') or 0)*100:.0f}%",''),(f"{money(r.get('target_sell'))} ({(r.get('target_fill') or 0)*100:.0f}%)",''),
            ('—' if r.get('q10_price') is None else f"{money(r['q10_price'])}–{money(r['q90_price'])}",'')] for r in targets if not r.get('buyable')])
    gainers,losers=market_movers(rows,limit=10)
    for title,items in (('Top gainers · 7 days',gainers),('Top losers · 7 days',losers)):
        table(title,['Card','Price','7 days','30 days','Days sold of last 30'],
              [[(r['name'],''),(money(r['latest_price']),''),(pct(r['return_7d']),cls(r['return_7d'])),(pct(r.get('return_30d')),cls(r.get('return_30d'))),
                (r.get('price_changes_30d'),'')] for r in items])
    table('Release calendar (next 30 days)',['Date','Game','Set','Type'],
          [[(c['released_on'],''),(c['game'],''),(c['set_name'],''),(c['set_type'].replace('_',' '),'')] for c in catalysts if 0<=c['days']<=30])
    sets=sorted((s for s in set_summary(rows,names) if s['printings']>=20 and s['change_7d'] is not None),key=lambda s:-s['change_7d'])[:10]
    table('Hottest sets this week (one copy of each card)',['Game','Set','Name','7 days','30 days','Cards'],
          [[(s['game'],''),(s['set_code'],''),(s['set_name'],''),(pct(s['change_7d']),cls(s['change_7d'])),(pct(s['change_30d']),cls(s['change_30d'])),
            (s['printings'],'')] for s in sets])
    if model and model.get('backtest'):
        bt=model['backtest']; skill=(1-bt['brier_model']/bt['brier_baseline'])*100 if bt.get('brier_baseline') else None
        verdict=('—' if skill is None else f"{skill:.0f}% more accurate than a plain guess" if skill>0 else 'no better than a plain guess yet')
        out.append(f"<p class='muted'>Forecast check on prices it had not seen: {verdict} "
                   f"(finance detail: Brier {bt['brier_model']:.4f} vs {bt['brier_baseline']:.4f} baseline).</p>")
    out.append("<p class='muted'>How to read this: Max buy is the most to pay and still expect a profit after every cost. "
               "Chance of profit is how often similar buys made money in the past. Confidence: High = at least 80% of the time, "
               "Medium = 65–80%, Low = less or too little data. Open the app and click any column heading for more.</p>")
    style=('body{background:#0d1523;color:#dbe7fa;font:14px Segoe UI,Helvetica,sans-serif;margin:24px;max-width:1100px}'
           'h1{color:#ffb000;font-size:22px}h2{font-size:15px;margin:22px 0 6px;color:#ffb000}'
           'table{border-collapse:collapse;width:100%}th,td{padding:4px 8px;text-align:left;border-bottom:1px solid #22364f}'
           'th{background:#182337;font-weight:600}.up{color:#5fd38d}.down{color:#ff7b7b}.muted{color:#95aac7}'
           '.wrap{overflow-x:auto}@media(max-width:700px){body{margin:10px;font-size:13px}th,td{padding:3px 5px}}')
    return f'<!doctype html><html><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>Card market brief</title><style>{style}</style></head><body>{"".join(out)}</body></html>'

def brief_path(): return ROOT/'daily_brief.html'

def write_daily_brief(store, report=lambda _m: None):
    """Headless: build today's brief from the saved rankings and forecast; returns (path, buy-now count, alert count) or None."""
    risk_free=float(store.get_setting('pricing_risk_free',DEFAULT_RISK_FREE_PCT))/100.0
    data=load_rankings(rankings_signature(store,risk_free))
    if not data: return None
    pricing=stored_pricing(store)
    dates=[r['latest_date'] for r in data['fresh'] if r.get('latest_date')]
    model=load_forecast_model(pricing['horizon'],max(dates)) if dates else None
    row_index={(r['card_id'],r['price_type']):r for r in data['fresh']}; by_card={}
    for r in data['fresh']: by_card.setdefault(r['card_id'],[]).append(r)
    positions=compute_positions(store,row_index,by_card,model,pricing)
    if model:
        for row,values in zip(data['fresh'],annotate_with_pricing(data['fresh'],model,pricing,portfolio_exposure(positions))): row.update(values)
    with ReadOnlyStore() as reader:
        names=set_names(reader); attach_card_facts(data['fresh'],mtg_card_facts(reader))
    html=daily_brief_html(data,model,pricing,positions,catalyst_calendar(store),names,health=data_health(store))
    path=brief_path(); tmp=path.with_suffix('.partial'); tmp.write_text(html,encoding='utf-8'); tmp.replace(path)
    buy_now=sum(1 for r in data['fresh'] if r.get('buyable') and not r.get('flags'))
    alerts=sum(1 for p in positions if p['alerts'] or (p['qty'] and p['signal'] in ('SELL','TRIM')))
    report(f'Daily brief written: {path} ({buy_now:,} buy-now printings, {alerts} portfolio alert(s))')
    return path,buy_now,alerts

def notify_desktop(title, message):
    """Best-effort Windows toast (PowerShell + WinRT, no extra installs); silently does nothing elsewhere or on failure."""
    if not sys.platform.startswith('win'): return False
    ps_text=lambda t: xml_escape(str(t)).replace("'","''")  # inside a single-quoted PowerShell string
    app_id=r'{1AC14E77-02E7-4E5D-B744-2EB1AE5198B7}\WindowsPowerShell\v1.0\powershell.exe'
    script=('[Windows.UI.Notifications.ToastNotificationManager, Windows.UI.Notifications, ContentType = WindowsRuntime] > $null;'
            '[Windows.Data.Xml.Dom.XmlDocument, Windows.Data.Xml.Dom.XmlDocument, ContentType = WindowsRuntime] > $null;'
            '$x = New-Object Windows.Data.Xml.Dom.XmlDocument;'
            f"$x.LoadXml('<toast><visual><binding template=\"ToastGeneric\"><text>{ps_text(title)}</text><text>{ps_text(message)}</text></binding></visual></toast>');"
            f"[Windows.UI.Notifications.ToastNotificationManager]::CreateToastNotifier('{app_id}').Show([Windows.UI.Notifications.ToastNotification]::new($x))")
    try:
        flags=getattr(subprocess,'CREATE_NO_WINDOW',0)
        return subprocess.run(['powershell','-NoProfile','-NonInteractive','-Command',script],
                              capture_output=True,timeout=30,creationflags=flags).returncode==0
    except Exception:
        return False

def poisson_even_odds_count(rate):
    """Largest k with P(at least k sales) >= 50% when sales are Poisson(rate): copies likely to sell."""
    k=0; term=cum=math.exp(-rate)  # cum = P(N <= k)
    while 1.0-cum>=0.5:
        k+=1; term*=rate/k; cum+=term
    return k

SELL_GRID = tuple(i/20 for i in range(1,19))  # forecast quantiles tried as list prices (5% .. 90%)

def best_list_price(fc, stats, value, cost, pricing, p_sold):
    """(list price, chance it sells within the horizon, expected profit) that maximizes expected profit per copy.

    A listing at price p is taken to sell if the (calibrated) forecast puts the market at or above p by the horizon,
    and the card trades at all (p_sold). A copy that does not sell is still yours, worth a later sale at the median
    forecast price, so a cheap ask that sells fast is only worth it if the extra certainty beats that. The expected
    profit is what the sale (or the later sale) nets after every cost minus what the copy cost you. When no ask is
    profitable it returns the best of the losing ones, so the caller can say so.
    """
    grid=stats.get('grid')
    if grid is None: grid=stats['grid']=[(q,forecast_quantile(fc,q)) for q in SELL_GRID]
    keep=1.0-pricing['fee_pct']/100.0; best=None
    later=sale_net(value*(1.0+stats['q'][50]),pricing)  # an unsold copy, sold later at the median forecast
    for q,r in grid:
        price=value*(1.0+r)
        if price<=0: continue
        fill=(1.0-q)*p_sold
        ev=fill*(price*keep-selling_costs(price,pricing))+(1.0-fill)*later-cost
        if best is None or ev>best[2]: best=(price,fill,ev)
    return best or (value,0.0,0.0)

def pricing_targets(market, low, fc, pricing, changes_30d=None):
    """Buy/sell price guides implied by a forecast distribution, liquidity, costs and condition. Estimates, not offers or advice.

    A copy bought for b (plus inbound shipping) and sold at the forecast market price p after the horizon nets
    p × (1 − fee%) − fixed selling costs (per-order fee, outgoing shipping by value, supplies): see sale_net.
    Worse-condition copies sell for a fixed share of the Near Mint price (cond_* settings), so every condition
    gets its own Max buy from the same forecast; the cheapest listing is valued at its inferred condition.
    Liquidity: the market price only moves when copies sell, so days-with-a-price-change (of the last
    30) approximate trading days. Expected copies you can sell within the horizon is
    active days × sell_through, and the chance one copy sells is 1 − e^(−that), assuming Poisson sales.
    A win needs both a sale and a profit, so Max buy is the highest price at which
    P(sells) × P(profit | sells) still reaches win_pct AND the expected profit (if it sells at the forecast mean)
    still clears min_profit dollars and min_roi percent of the all-in cost; None means no price does.
    """
    if not fc or not market: return None
    keep=1.0-pricing['fee_pct']/100.0; ship_in=pricing['ship_in']
    # Everything that depends only on the distribution is computed once per bucket and shared by its rows.
    stats=fc.get('_stats')
    if stats is None:
        stats=fc['_stats']={'q':{p:forecast_quantile(fc,p/100.0) for p in (10,25,50,75,90)},'mean':forecast_mean(fc),
                            'p_rise':forecast_prob_above(fc,0.0),'need_q':{}}
        stats['p_rise_ci']=wilson_interval(stats['p_rise'],fc.get('ess') or fc['n'])
    q=stats['q']; mean=stats['mean']
    expected_sales=None if changes_30d is None else changes_30d*fc['horizon']/30.0*pricing['sell_through']  # Poisson rate
    p_sold=1.0 if expected_sales is None else 1.0-math.exp(-expected_sales)
    net=lambda value,r: value*(1.0+r)*keep-selling_costs(value,pricing)
    # value = what a copy in that condition sells for today; profit when its forecast sale beats the all-in cost.
    profit_if_sold=lambda buy,value: forecast_prob_above(fc,(buy+ship_in+selling_costs(value,pricing))/(value*keep)-1.0) if keep>0 else 0.0
    needed=pricing['win_pct']/100.0/p_sold if p_sold>0 else float('inf')
    r_need=None
    if needed<=1.0:
        key=round(needed,9); r_need=stats['need_q'].get(key)
        if r_need is None: r_need=stats['need_q'][key]=forecast_quantile(fc,1.0-needed)
    max_buy={}
    roi=pricing.get('min_roi',0.0)/100.0; floor=pricing.get('min_profit',0.0)
    for cond in CONDITIONS:
        value=market*condition_share(pricing,cond)
        b=None if r_need is None else net(value,r_need)-ship_in
        if b is not None:
            # Also leave the minimum expected profit: E[net] − cost ≥ max(min_profit, min_roi × cost).
            expected=net(value,mean)
            b=min(b,min(expected/(1.0+roi),expected-floor)-ship_in)
        max_buy[cond]=b if b is not None and b>0 else None
    low_cond=implied_condition(low,market,pricing); low_value=market*condition_share(pricing,low_cond)
    liquidity=liquidity_label(changes_30d)
    buy_ref,ref_value=(low,low_value) if low else (market,market)
    # Where to list a copy bought at the cheapest listing (or at market): the profit-maximizing ask, not "market".
    target_sell,target_fill,target_ev=best_list_price(fc,stats,ref_value,buy_ref+ship_in,pricing,p_sold)
    ess=fc.get('ess') or fc['n']; profit_low=profit_if_sold(low,low_value) if low else None
    win_low=p_sold*profit_low if low else None
    ci=wilson_interval(profit_low,ess)
    break_even=net(market,mean)-ship_in
    return {'p_rise':stats['p_rise'],'samples':fc['n'],'ess':ess,'bucket':fc['key'],'horizon':fc['horizon'],
            'p_rise_ci':stats['p_rise_ci'],
            'win_low_ci':None if ci is None else (p_sold*ci[0],p_sold*ci[1]),
            **{f'q{p}_price':market*(1+r) for p,r in q.items()},
            'median_price':market*(1+q[50]),
            'max_buy':max_buy['NM'],'max_buy_cond':max_buy,'low_cond':low_cond,
            'break_even_buy':break_even if break_even>0 else None,
            'win_at_low':win_low,'win_at_market':p_sold*profit_if_sold(market,market),
            # Chance of profit if it sells, buying a Near Mint copy at Max buy (above the target when the profit floor binds).
            'profit_at_max_buy':profit_if_sold(max_buy['NM'],market) if max_buy['NM'] else None,
            'liquidity':liquidity,'p_sold':p_sold,
            'max_qty':None if expected_sales is None else poisson_even_odds_count(expected_sales),
            'min_sell':(buy_ref+ship_in+selling_costs(ref_value,pricing))/keep if keep>0 else None,
            'exp_sale_net':net(market,mean),'exp_sale_net_low':net(low_value,mean),
            'mean_return':mean,'sigma_return':max(1e-6,(q[90]-q[10])/2.563),
            # A Near Mint copy sells just under the cheapest listing when that listing is NM; otherwise just under market.
            'target_sell':target_sell,'target_fill':target_fill,'target_ev':target_ev,
            'quick_sell':(low if low and low_cond=='NM' else market*0.96)*0.99 if low else market*0.99}


def spike_flags(row):
    """Reasons a ranked move is almost certainly not a tradeable price change."""
    flags=[]
    price=row.get('latest_price'); low=row.get('low_price'); share=row.get('jump_share')
    if price is not None and price<RANK_MIN_PRICE:
        flags.append(f'under ${RANK_MIN_PRICE:,.0f}')
    if low and price and price>=SPIKE_MARKET_TO_LOW*low:
        flags.append('market ≫ low')  # copies are still listed far below the "market" estimate
    if low and price and price<SPIKE_LOW_TO_MARKET*low:
        flags.append('market ≪ low')  # no copy is listed anywhere near the "market" estimate
    if (row.get('return_30d') or 0)>=SPIKE_MIN_RETURN_30D and share is not None and share>=SPIKE_JUMP_SHARE:
        flags.append('single jump')
    return flags


def printing_label(name, price_type):
    """'Astral Dragon' for the Normal printing, 'Astral Dragon (Foil)' / '(Holofoil)' otherwise."""
    subtype=str(price_type).partition('_')[2]
    return name if subtype in ('','Normal') else f'{name} ({subtype})'


def _price_type_priority(price_type):
    subtype=str(price_type).partition('_')[2].strip().lower()
    preferred=['normal','nonfoil','non-foil','holofoil','foil','reverse holofoil','etched']
    try: return preferred.index(subtype)
    except ValueError: return len(preferred)+1


def build_market_rankings(store, today=None, progress=None, risk_free=0.0, scan_days=None, on_card=None):
    """Rank every (card, printing) and build the market indices in one streaming pass over recent prices.

    The cheapest current listing (low_*) is read in the same scan rather than with one query per
    printing. Indices chain each day's cross-section of one-day moves for printings worth $1+ the day
    before: 'ew' is equal-weighted (mean log return, each move winsorized to ±25% so a single listing
    artifact cannot swing it) and 'pw' is price-weighted (the value of holding one copy of each).
    on_card(card_id, {printing: (market, low, buylist, eu)}) sees every card's series, so other models can
    share this scan (see build_market_views). Reads the compact daily table (see ensure_daily_history).
    """
    today=today or datetime.now(timezone.utc).date()
    if isinstance(today,datetime): today=today.date()
    scan_days=scan_days or RANK_SCAN_DAYS
    metrics_from=today.toordinal()-35  # rankings use the latest 35 days; indices use the whole scan
    cards={}; releases=set_release_days(store)
    for cid,game,name,set_code,rarity in store.iter_q("SELECT id,game,name,set_code,rarity FROM cards WHERE game IN ('MTG','Pokémon','One Piece','Riftbound') AND item_type='card'"):
        key=card_key(cid)
        if key is not None: cards[key]=(cid,game,name,set_code,variant_of(game,name,rarity),releases.get((game,set_code)))
    total_cards=len(cards)
    if progress: progress(0,total_cards,'Scanning recent daily prices')
    ranked=[]; index_acc={}; seen_cards=0

    def flush_card(info, series):
        # Each printing (Normal, Foil, Holofoil, ...) is ranked as its own row.
        cid,game,name,set_code,variant,release=info; acc=index_acc.setdefault(game,{})
        for printing,(full,lows,buylist,eu) in series.items():
            # Only printings that were worth $1+ enter the indices; most of the catalog is bulk and never does.
            for (o0,p0),(o1,p1) in (zip(full,full[1:]) if full and max(v for _o,v in full)>=RANK_MIN_PRICE else ()):
                if o1-o0!=1 or p0<RANK_MIN_PRICE: continue
                r=max(-0.25,min(0.25,math.log(p1/p0)))
                a=acc.get(o1)
                if a is None: a=acc[o1]=[0.0,0,0.0,0.0,0,0]
                a[0]+=r; a[1]+=1; a[2]+=p1-p0; a[3]+=p0
                if p1>p0+1e-9: a[4]+=1
                elif p1<p0-1e-9: a[5]+=1
            recent=full[bisect.bisect_left(full,(metrics_from,)):]
            if not recent: continue
            metrics=calculate_market_metrics(None,today,risk_free,series=recent)
            latest_o=recent[-1][0]; fresh=lambda pts: pts and pts[-1][0]>=latest_o-3
            low_price=lows[-1][1] if fresh(lows) and metrics['latest_price']>=RANK_MIN_PRICE else None
            bl,bl_change=_latest_and_change(buylist) if fresh(buylist) else (None,None)
            eu_price,eu_change=_latest_and_change(eu) if fresh(eu) else (None,None)
            ranked.append({**metrics,'card_id':cid,'game':game,'card_name':name,
                           'name':printing_label(name,'market_'+printing),'printing':printing,'set_code':set_code,
                           'price_type':'market_'+printing,'series_count':metrics['observations'],'low_price':low_price,'variant':variant,
                           'days_since_release':None if release is None else today.toordinal()-release,
                           'buylist':bl,'buylist_change_30d':bl_change,'eu_price':eu_price,'eu_change_30d':eu_change})

    for key,series in iter_daily_cards(store,today.toordinal()-scan_days):
        info=cards.get(key)
        if info is None: continue
        seen_cards+=1
        if progress and seen_cards%5000==0: progress(seen_cards,total_cards,'Calculating Sharpe, opportunities and indices')
        flush_card(info,series)
        if on_card: on_card(info[0],series,info[4],info[5])
    if progress: progress(total_cards,total_cards,'Ranking calculations complete')
    all_rows=ranked
    fresh=[r for r in all_rows if r['age_days'] is not None and r['age_days']<=3]
    for r in all_rows: r['flags']=spike_flags(r)
    # One Sharpe test per printing: control the false-discovery rate across all of them.
    for r,q in zip(fresh,benjamini_hochberg([None if r.get('psr') is None else 1.0-r['psr'] for r in fresh])):
        r['fdr_q']=q
    sharpe_all=sorted((r for r in fresh if r['sharpe_30d'] is not None),
                      key=lambda r:(-r['sharpe_30d'],-(r['return_30d'] or -1e9),r['name']))
    opportunity_all=sorted((r for r in fresh if r['opportunity_score'] is not None),
                           key=lambda r:(-r['opportunity_score'],-(r['return_7d'] or -1e9),r['name']))
    # The diagnostics are several full scans of the price table and only explain empty results.
    diagnostics = market_data_diagnostics(store, today) if not fresh else {}
    return {'all':all_rows,'fresh':fresh,
            'sharpe':[r for r in sharpe_all if not r['flags']],
            'opportunities':[r for r in opportunity_all if not r['flags']],
            'sharpe_all':sharpe_all,'opportunities_all':opportunity_all,
            'excluded':[r for r in fresh if r['flags']],'diagnostics':diagnostics,
            'indices':_chain_indices(index_acc)}


INDEX_MIN_MOVES = 25  # printings needed on a day for its index move to count

def _chain_indices(index_acc):
    """{game: [[day, equal-weighted level, price-weighted level, printings, advancers, decliners], ...]} from 100."""
    out={}
    for game,acc in index_acc.items():
        ew=pw=100.0; rows=[]
        for o in sorted(acc):
            total_r,n,dp,p0,adv,dec=acc[o]
            if n<INDEX_MIN_MOVES: continue
            if not rows: rows.append([date.fromordinal(o-1).isoformat(),100.0,100.0,0,0,0])
            ew*=math.exp(total_r/n); pw*=1.0+dp/p0 if p0>0 else 1.0
            rows.append([date.fromordinal(o).isoformat(),ew,pw,n,adv,dec])
        if rows: out[game]=rows
    return out


def market_data_diagnostics(store, today=None):
    """Summarize local source coverage so an empty ranking is explainable."""
    today=today or datetime.now(timezone.utc).date()
    if isinstance(today,datetime): today=today.date()
    cutoff=(today-timedelta(days=35)).isoformat()+'T00:00:00'
    total_cards=store.q("SELECT COUNT(*) FROM cards WHERE game IN ('MTG','Pokémon','One Piece','Riftbound')")[0][0]
    item_types={str(kind or 'unknown'):count for kind,count in store.q(
        "SELECT item_type,COUNT(*) FROM cards WHERE game IN ('MTG','Pokémon','One Piece','Riftbound') GROUP BY item_type")}
    total_prices=store.q("SELECT COUNT(*) FROM prices p JOIN cards c ON c.id=p.card_id WHERE c.game IN ('MTG','Pokémon','One Piece','Riftbound')")[0][0]
    tcgcsv_prices=store.q("SELECT COUNT(*) FROM prices p JOIN cards c ON c.id=p.card_id WHERE c.game IN ('MTG','Pokémon','One Piece','Riftbound') AND p.source='tcgcsv_tcgplayer'")[0][0]
    market_prices=store.q("SELECT COUNT(*) FROM prices p JOIN cards c ON c.id=p.card_id WHERE c.game IN ('MTG','Pokémon','One Piece','Riftbound') AND p.source IN ('tcgcsv_tcgplayer','mtgjson_tcgplayer') AND p.price_type LIKE 'market_%' AND p.price>0")[0][0]
    recent_market_prices=store.q("SELECT COUNT(*) FROM prices p JOIN cards c ON c.id=p.card_id WHERE c.game IN ('MTG','Pokémon','One Piece','Riftbound') AND p.source IN ('tcgcsv_tcgplayer','mtgjson_tcgplayer') AND p.price_type LIKE 'market_%' AND p.price>0 AND p.source_time>=?",(cutoff,))[0][0]
    recent_singles=store.q("""SELECT COUNT(*) FROM prices p JOIN cards c ON c.id=p.card_id
        WHERE c.game IN ('MTG','Pokémon','One Piece','Riftbound') AND c.item_type='card' AND p.source IN ('tcgcsv_tcgplayer','mtgjson_tcgplayer') AND p.price_type LIKE 'market_%'
          AND p.price>0 AND p.source_time>=?""",(cutoff,))[0][0]
    latest=store.q("SELECT MAX(p.source_time) FROM prices p JOIN cards c ON c.id=p.card_id WHERE c.game IN ('MTG','Pokémon','One Piece','Riftbound') AND p.source IN ('tcgcsv_tcgplayer','mtgjson_tcgplayer') AND p.price_type LIKE 'market_%' AND p.price>0")
    return {'total_cards':total_cards,'item_types':item_types,'total_prices':total_prices,
            'tcgcsv_prices':tcgcsv_prices,'market_prices':market_prices,
            'recent_market_prices':recent_market_prices,'recent_singles_price_rows':recent_singles,
            'latest_market_source_time':latest[0][0] if latest else None}

def ensure_daily_history(store, report=lambda _m: None):
    """Fill the compact daily table from the raw prices once (and catch up a sync made by an older app version).

    Upserts are order-independent (TCGCSV overrides, MTGJSON fills gaps), so the raw rows stream in storage order.
    Returns True when it wrote anything.
    """
    with _DAILY_MIGRATION_LOCK:
        marker=store.get_setting('tcgcsv_dataset_marker','')
        if store.get_setting('daily_version','')==str(DAILY_VERSION):
            if store.get_setting('daily_marker','')==marker: return False
            # An older version synced without writing daily rows: copy that dataset's day.
            stamp=store.get_setting('tcgcsv_dataset_time','')
            sql=("SELECT card_id,source,price_type,currency,price,source_time,collected_at FROM prices "
                 "WHERE source='tcgcsv_tcgplayer' AND source_time=? AND (price_type LIKE 'market_%' OR price_type LIKE 'low_%')")
            args=(stamp,); label='Catching up the compact daily history with the latest sync'
        else:
            sql=("SELECT card_id,source,price_type,currency,price,source_time,collected_at FROM prices "
                 "WHERE (source IN ('tcgcsv_tcgplayer','mtgjson_tcgplayer') AND price_type LIKE 'market_%' "
                 "OR source='tcgcsv_tcgplayer' AND price_type LIKE 'low_%') AND price>0 ORDER BY id")
            args=(); label='One-time upgrade: building the compact daily price history'
        report(label+'…'); emit_progress(report,0,0,label)
        chunk=[]; done=0
        with ReadOnlyStore() as reader:
            for row in reader.iter_q(sql,args,fetch_size=20000):
                chunk.append(row)
                if len(chunk)>=200000:
                    store.upsert_daily(daily_rows_from_prices(chunk,store.printing_id)); done+=len(chunk); chunk.clear()
                    emit_progress(report,0,0,f'{label}: {done:,} prices copied')
        if chunk: store.upsert_daily(daily_rows_from_prices(chunk,store.printing_id)); done+=len(chunk)
        store.setting('daily_version',DAILY_VERSION); store.setting('daily_marker',marker)
        report(f'{label}: {done:,} prices copied'); return True

def iter_daily_cards(reader, since_ordinal):
    """Yield (card key, {printing name: (market, low, buylist, eu)}) per card, each a [(day ordinal, price)] list in
    day order (prices in dollars; eu in euros), from the compact daily table.

    SQLite concatenates each printing's days and prices itself (group_concat skips NULLs, so the day list built
    with the same condition stays aligned) and walks the table in key order, so Python handles ~200k rows
    instead of every daily point; that is most of the scan's speed.
    """
    names={pid:name for pid,name in reader.q('SELECT id,name FROM printings')}
    cols=('market','low','buylist','eu')
    sql=('SELECT card,printing,'+','.join(f'group_concat(CASE WHEN {c} IS NOT NULL THEN day END),group_concat({c})' for c in cols)+
         ' FROM daily WHERE day>=? GROUP BY card,printing')
    def points(days,values):
        if not days: return []
        d=list(map(int,days.split(','))); v=[x/100.0 for x in map(int,values.split(','))]
        pairs=list(zip(d,v))
        if d!=sorted(d): pairs.sort()
        return pairs
    current=None; series={}
    for row in reader.iter_q(sql,(since_ordinal,),fetch_size=5000):
        key=row[0]
        if key!=current:
            if series: yield current,series
            current=key; series={}
        series[names.get(row[1])]=tuple(points(row[2+2*i],row[3+2*i]) for i in range(4))
    if series: yield current,series

def _latest_and_change(points, back=30, tolerance=3):
    """(latest value, % change over `back` days or None) of a [(day, value)] list; (None, None) when empty."""
    if not points: return None,None
    o,v=points[-1]; target=o-back
    prior=[p for d,p in points if abs(d-target)<=tolerance]
    return v,((v/prior[0]-1)*100 if prior and prior[0]>0 else None)

def classify_tcgcsv_product(name, ext_map):
    """Distinguish singles from sealed and miscellaneous TCGplayer products.

    TCGCSV includes sealed boxes, packs, accessories, and other products in the
    same category as singles. A name-based sealed check takes priority over card
    metadata because some sealed products contain rarity/card text fields.
    """
    n = re.sub(r'[^a-z0-9]+', ' ', str(name or '').lower()).strip()
    sealed_terms = (
        'booster box', 'booster pack', 'booster bundle', 'booster case', 'booster box case',
        'elite trainer box', 'build battle', 'build and battle', 'blister',
        'collector chest', 'collection box', 'premium collection', 'display box',
        'deck box', 'starter deck', 'theme deck', 'structure deck', 'mini tin', 'collector tin',
        'playmat', 'sleeves', 'binder', 'portfolio', 'dice', 'storage box',
        'collector chest case', 'elite trainer box case', 'pack art bundle', 'sealed product', 'gift box',
        'booster display', 'box set'
    )
    if re.search(r'\bcode card\b', n):
        return 'other'
    if any(re.search(r'\b'+re.escape(term)+r'\b', n) for term in sealed_terms):
        return 'sealed_product'
    number = ext_map.get('number') or ext_map.get('card number') or ext_map.get('collector number')
    rarity = ext_map.get('rarity')
    if number or rarity:
        return 'card'
    return 'other'

def download(url, dest, progress):
    req = urllib.request.Request(url, headers={'User-Agent':USER_AGENT})
    tmp = dest.with_suffix('.partial')
    with urllib.request.urlopen(req, timeout=90) as r, open(tmp, 'wb') as w:
        total = int(r.headers.get('Content-Length', 0)); count = 0; last_progress = 0
        emit_progress(progress, 0, total, 'Downloading '+Path(dest).name)
        while True:
            chunk = r.read(512 * 1024)
            if not chunk: break
            w.write(chunk); count += len(chunk)
            if count-last_progress >= 1024*1024 or (total and count >= total):
                last_progress=count
                emit_progress(progress, count, total, 'Downloading '+Path(dest).name)
            if count % (10 * 1024 * 1024) < len(chunk):
                progress('Downloaded '+f'{count/1048576:,.1f} MB'+ (f' / {total/1048576:,.1f} MB' if total else ''))
    tmp.replace(dest)
    emit_progress(progress, 1, 1, 'Download complete: '+Path(dest).name)

# --- Compact daily history: one row per printing per day, prices in cents; every scan reads this ---
# The raw prices table keeps every TCGCSV field as text-keyed rows (~300 bytes each); scanning 13M of them took
# minutes. daily keeps what the models use - market, cheapest listing, Card Kingdom buylist, Cardmarket (EUR) -
# as integers, about a tenth of the size, in (card, printing, day) order so a full scan needs no sort.
DAILY_VERSION = 1
CARD_KEY_BASE = 10**8  # card key = TCGCSV category x 10^8 + TCGplayer product id
_DAILY_UPSERT = {
    # TCGCSV is the primary daily market price; MTGJSON only fills days TCGCSV lacks (any import order gives the same table).
    'market':'INSERT INTO daily(card,printing,day,market) VALUES(?,?,?,?) ON CONFLICT(card,printing,day) DO UPDATE SET market=excluded.market',
    'market_fill':'INSERT INTO daily(card,printing,day,market) VALUES(?,?,?,?) ON CONFLICT(card,printing,day) DO UPDATE SET market=COALESCE(daily.market,excluded.market)',
    'low':'INSERT INTO daily(card,printing,day,low) VALUES(?,?,?,?) ON CONFLICT(card,printing,day) DO UPDATE SET low=excluded.low',
    'buylist':'INSERT INTO daily(card,printing,day,buylist) VALUES(?,?,?,?) ON CONFLICT(card,printing,day) DO UPDATE SET buylist=excluded.buylist',
    'eu':'INSERT INTO daily(card,printing,day,eu) VALUES(?,?,?,?) ON CONFLICT(card,printing,day) DO UPDATE SET eu=excluded.eu',
}
_DAILY_MIGRATION_LOCK = threading.Lock()

def card_key(cid):
    """'tcgcsv:3:502004' -> 300502004; None for ids that are not TCGCSV products."""
    parts=str(cid).split(':')
    if len(parts)!=3 or parts[0]!='tcgcsv' or not parts[1].isdigit() or not parts[2].isdigit(): return None
    return int(parts[1])*CARD_KEY_BASE+int(parts[2])

def card_id_from_key(key): return f'tcgcsv:{key//CARD_KEY_BASE}:{key%CARD_KEY_BASE}'

def daily_rows_from_prices(prices, printing_id):
    """{upsert kind: [(card, printing, day, cents)]} for the market and cheapest-listing rows among price tuples."""
    out={}
    for cid,source,price_type,_currency,price,stamp,_collected in prices:
        kind,_,subtype=str(price_type).partition('_')
        if kind=='market' and source=='tcgcsv_tcgplayer': k='market'
        elif kind=='market' and source=='mtgjson_tcgplayer': k='market_fill'
        elif kind=='low' and source=='tcgcsv_tcgplayer': k='low'
        else: continue
        key=card_key(cid); day=_day_ordinal(stamp)
        if key is None or not day or price is None or not 0<price<10000000: continue
        out.setdefault(k,[]).append((key,printing_id(subtype),day,int(round(price*100))))
    return out

class Store:
    def __init__(self, path=None):
        path=Path(path) if path else DB; path.parent.mkdir(parents=True, exist_ok=True)
        self.con = sqlite3.connect(path, check_same_thread=False)
        self.lock = threading.RLock()
        with self.lock:
            self.con.executescript('''
            PRAGMA journal_mode=WAL;
            PRAGMA synchronous=NORMAL;
            PRAGMA busy_timeout=30000;
            CREATE TABLE IF NOT EXISTS cards (
             id TEXT PRIMARY KEY, game TEXT NOT NULL, name TEXT NOT NULL, set_code TEXT,
             collector_number TEXT, rarity TEXT, finish TEXT, details TEXT,
             updated_at TEXT NOT NULL, item_type TEXT NOT NULL DEFAULT 'card');
            CREATE INDEX IF NOT EXISTS idx_cards_game_name ON cards(game,name);
            CREATE TABLE IF NOT EXISTS prices (
             id INTEGER PRIMARY KEY, card_id TEXT NOT NULL, source TEXT NOT NULL,
             price_type TEXT NOT NULL, currency TEXT NOT NULL DEFAULT 'USD',
             price REAL NOT NULL, source_time TEXT NOT NULL, collected_at TEXT NOT NULL,
             UNIQUE(card_id,source,price_type,source_time));
            CREATE INDEX IF NOT EXISTS idx_prices_card ON prices(card_id, source_time DESC);
            -- Duplicated the UNIQUE constraint's own index and slowed every price insert.
            DROP INDEX IF EXISTS idx_prices_card_source_type_time;
            CREATE TABLE IF NOT EXISTS tcgcsv_groups (
             category_id INTEGER NOT NULL, group_id TEXT NOT NULL, modified_on TEXT NOT NULL,
             product_count INTEGER NOT NULL, synced_at TEXT NOT NULL,
             PRIMARY KEY(category_id, group_id));
            CREATE TABLE IF NOT EXISTS jobs (
             id INTEGER PRIMARY KEY, started_at TEXT, ended_at TEXT, task TEXT, status TEXT,
             count INTEGER, message TEXT);
            CREATE TABLE IF NOT EXISTS watchlist(card_id TEXT PRIMARY KEY, added_at TEXT);
            CREATE TABLE IF NOT EXISTS signals (
             id INTEGER PRIMARY KEY, created_at TEXT, card_id TEXT, kind TEXT,
             description TEXT, status TEXT DEFAULT 'research');
            CREATE TABLE IF NOT EXISTS paper_trades (
             id INTEGER PRIMARY KEY, created_at TEXT, card_id TEXT, side TEXT,
             quantity INTEGER, price REAL, fee REAL, notes TEXT);
            CREATE TABLE IF NOT EXISTS settings(key TEXT PRIMARY KEY, value TEXT);
            CREATE TABLE IF NOT EXISTS set_info(
             game TEXT NOT NULL, code TEXT NOT NULL, name TEXT, released_on TEXT, set_type TEXT,
             source TEXT NOT NULL, updated_at TEXT, PRIMARY KEY(game,code,source));
            -- Watchlist and holdings: one row per printing; qty 0 = watched only.
            CREATE TABLE IF NOT EXISTS portfolio(
             card_id TEXT NOT NULL, price_type TEXT NOT NULL DEFAULT '', qty INTEGER NOT NULL DEFAULT 0,
             cost REAL, alert_above REAL, alert_below REAL, added_at TEXT, PRIMARY KEY(card_id,price_type));
            CREATE TABLE IF NOT EXISTS printings(id INTEGER PRIMARY KEY, name TEXT NOT NULL UNIQUE);
            CREATE TABLE IF NOT EXISTS pc_sets(game TEXT NOT NULL, slug TEXT PRIMARY KEY, release TEXT, fetched_at TEXT);
            CREATE TABLE IF NOT EXISTS pc_series(url TEXT PRIMARY KEY, game TEXT NOT NULL, slug TEXT NOT NULL, release TEXT,
             title TEXT, points TEXT NOT NULL, fetched_at TEXT);
            CREATE TABLE IF NOT EXISTS mtg_oracle(name TEXT PRIMARY KEY, legal TEXT, banned TEXT, edhrec INTEGER, updated_at TEXT);
            CREATE TABLE IF NOT EXISTS market_events(day TEXT NOT NULL, game TEXT NOT NULL, kind TEXT NOT NULL, subject TEXT NOT NULL,
             detail TEXT, PRIMARY KEY(day,game,kind,subject));
            CREATE TABLE IF NOT EXISTS trades(
             id INTEGER PRIMARY KEY, card_id TEXT NOT NULL, price_type TEXT NOT NULL DEFAULT '', side TEXT NOT NULL,
             qty INTEGER NOT NULL, price REAL NOT NULL, condition TEXT NOT NULL DEFAULT 'NM', fees REAL, shipping REAL,
             traded_on TEXT NOT NULL, market REAL, predicted_profit REAL, predicted_win REAL, note TEXT, created_at TEXT);
            CREATE TABLE IF NOT EXISTS daily(
             card INTEGER NOT NULL, printing INTEGER NOT NULL, day INTEGER NOT NULL,
             market INTEGER, low INTEGER, buylist INTEGER, eu INTEGER,
             PRIMARY KEY(card,printing,day)) WITHOUT ROWID;
            ''')
            # Earlier versions kept a card-level watchlist; move it into the portfolio once. Only write when there is
            # something to move: a needless write at startup fails while the daily background update is saving prices.
            if self.con.execute('SELECT 1 FROM watchlist LIMIT 1').fetchone():
                self.con.execute("INSERT OR IGNORE INTO portfolio(card_id,price_type,added_at) SELECT card_id,'',added_at FROM watchlist")
                self.con.execute('DELETE FROM watchlist')
            # Upgrade databases created by earlier single-file versions.
            columns = {row[1] for row in self.con.execute('PRAGMA table_info(cards)')}
            if 'item_type' not in columns:
                self.con.execute("ALTER TABLE cards ADD COLUMN item_type TEXT NOT NULL DEFAULT 'card'")
                # Correctly reclassify old TCGCSV rows imported before item_type existed.
                legacy=self.con.execute("SELECT id,name,details FROM cards WHERE details LIKE '%TCGCSV / TCGplayer cached product prices%'").fetchall()
                for cid,name,raw_details in legacy:
                    try:
                        detail=json.loads(raw_details or '{}')
                        ext_map={str(x.get('name','')).strip().lower():x.get('value')
                                 for x in detail.get('extended_data',[]) if isinstance(x,dict) and x.get('name') is not None}
                        kind=classify_tcgcsv_product(name,ext_map)
                    except (ValueError,TypeError,AttributeError):
                        kind='other'
                    self.con.execute('UPDATE cards SET item_type=? WHERE id=?',(kind,cid))
            # Pricing v2 moved shipping and the per-order fee out of the per-card cost; an untouched old default
            # (0.75 all-in) becomes the new supplies-only default so costs are not counted twice.
            version=self.con.execute("SELECT value FROM settings WHERE key='pricing_version'").fetchone()
            if not version or version[0]!=str(PRICING_VERSION):
                self.con.execute("UPDATE settings SET value=? WHERE key='pricing_cost' AND CAST(value AS REAL)=0.75",(str(DEFAULT_PRICING['cost']),))
                self.con.execute("INSERT INTO settings VALUES('pricing_version',?) ON CONFLICT(key) DO UPDATE SET value=excluded.value",(str(PRICING_VERSION),))
            self.con.commit()
            self.printing_ids={name:pid for pid,name in self.con.execute('SELECT id,name FROM printings')}
            if 'changes' not in {row[1] for row in self.con.execute('PRAGMA table_info(trades)')}:
                self.con.execute('ALTER TABLE trades ADD COLUMN changes INTEGER'); self.con.commit()  # liquidity when bought
    def q(self,sql,args=()):
        with self.lock: return self.con.execute(sql,args).fetchall()
    def iter_q(self,sql,args=(),fetch_size=4000):
        # Stream rows in bounded batches to avoid materializing large histories.
        with self.lock:
            cur=self.con.execute(sql,args)
            while True:
                batch=cur.fetchmany(fetch_size)
                if not batch: break
                for row in batch: yield row
    def execute(self,sql,args=()):
        with self.lock:
            try:
                x=self.con.execute(sql,args); self.con.commit(); return x.lastrowid
            except Exception:
                self.con.rollback()
                raise
    def executemany(self,sql,rows):
        with self.lock:
            try:
                self.con.executemany(sql,rows); self.con.commit()
            except Exception:
                self.con.rollback()
                raise
    def get_setting(self,k,default=''):
        r=self.q('SELECT value FROM settings WHERE key=?',(k,)); return r[0][0] if r else default
    def printing_id(self,name):
        """Small integer id for a printing name (Normal, Foil, Holofoil, ...); committed with the caller's write."""
        pid=self.printing_ids.get(name)
        if pid is None:
            with self.lock:
                self.con.execute('INSERT OR IGNORE INTO printings(name) VALUES(?)',(name,))
                pid=self.printing_ids[name]=self.con.execute('SELECT id FROM printings WHERE name=?',(name,)).fetchone()[0]
        return pid
    def _write_daily(self,rows_by_kind):
        for kind,rows in rows_by_kind.items():
            if rows: self.con.executemany(_DAILY_UPSERT[kind],rows)
    def upsert_daily(self,rows_by_kind):
        """Write {kind: [(card, printing, day, cents)]} into the compact daily history in one transaction."""
        with self.lock:
            try:
                self._write_daily(rows_by_kind); self.con.commit()
            except Exception:
                self.con.rollback()
                raise
    def setting(self,k,v):
        if self.get_setting(k,None)==str(v): return  # unchanged: no write, so opening the app never waits on the background update
        self.execute('INSERT INTO settings VALUES(?,?) ON CONFLICT(key) DO UPDATE SET value=excluded.value',(k,str(v)))
    def batch(self,rows, prices=(), groups=()):
        with self.lock:
            try:
                self.con.executemany('''INSERT INTO cards
                 (id,game,name,set_code,collector_number,rarity,finish,details,updated_at,item_type)
                 VALUES(?,?,?,?,?,?,?,?,?,?)
                 ON CONFLICT(id) DO UPDATE SET name=excluded.name, set_code=excluded.set_code,
                 collector_number=excluded.collector_number, rarity=excluded.rarity,
                 finish=excluded.finish, details=excluded.details, updated_at=excluded.updated_at,
                 item_type=excluded.item_type''',rows)
                if prices:
                    self.con.executemany('''INSERT OR IGNORE INTO prices
                    (card_id,source,price_type,currency,price,source_time,collected_at)
                    VALUES(?,?,?,?,?,?,?)''',prices)
                    self._write_daily(daily_rows_from_prices(prices,self.printing_id))
                if groups:
                    # Recorded in the same transaction as the catalog it describes.
                    self.con.executemany('''INSERT INTO tcgcsv_groups
                    (category_id,group_id,modified_on,product_count,synced_at) VALUES(?,?,?,?,?)
                    ON CONFLICT(category_id,group_id) DO UPDATE SET modified_on=excluded.modified_on,
                    product_count=excluded.product_count, synced_at=excluded.synced_at''',groups)
                self.con.commit()
            except Exception:
                self.con.rollback()
                raise
    def start_job(self,task): return self.execute('INSERT INTO jobs(started_at,task,status,count,message) VALUES(?,?,?,?,?)',(utc(),task,'running',0,''))
    def end_job(self,id,status,count,msg): self.execute('UPDATE jobs SET ended_at=?,status=?,count=?,message=? WHERE id=?',(utc(),status,count,str(msg)[:800],id))
    def close(self):
        with self.lock: self.con.close()

class ReadOnlyStore:
    """A separate SQLite connection for long read-only scans.

    Store serializes every query behind one lock, so a multi-minute ranking scan through it
    blocked GUI-thread queries (the 60-second scheduler tick froze the window). WAL mode lets
    this connection read while the shared one stays free.
    """
    def __init__(self):
        self.con=sqlite3.connect(DB,check_same_thread=False)
        self.con.execute('PRAGMA busy_timeout=10000'); self.con.execute('PRAGMA query_only=ON')
        # Larger page cache and memory-mapped reads for the multi-million-row ranking and forecast scans.
        self.con.execute('PRAGMA cache_size=-131072'); self.con.execute('PRAGMA mmap_size=1073741824')
    def q(self,sql,args=()): return self.con.execute(sql,args).fetchall()
    def iter_q(self,sql,args=(),fetch_size=4000):
        cur=self.con.execute(sql,args)
        while True:
            batch=cur.fetchmany(fetch_size)
            if not batch: break
            yield from batch
    def close(self): self.con.close()
    def __enter__(self): return self
    def __exit__(self,*_exc): self.close()

def pace_tcgcsv_request(clock=None, sleep=None):
    """Keep request starts at least TCGCSV_MIN_INTERVAL apart.

    The interval is measured from the previous request's start, so network latency
    counts toward it instead of being added on top of a fixed sleep.
    """
    global _tcgcsv_last_request
    clock=clock or time.monotonic; sleep=sleep or time.sleep
    with _tcgcsv_pace_lock:
        wait=_tcgcsv_last_request+TCGCSV_MIN_INTERVAL-clock()
        if wait>0: sleep(wait)
        _tcgcsv_last_request=clock()

def tcgcsv_fetch(url, accept, timeout, _redirects=3):
    """GET a TCGCSV resource over a reused keep-alive connection with gzip transfer.

    A fresh TLS handshake per request (urlopen) dominated sync time. Non-2xx responses
    raise urllib.error.HTTPError and transport failures raise URLError, so callers keep
    the same retry and 429 handling as before.
    """
    parts=urlsplit(url)
    if parts.scheme not in ('http','https'): raise ValueError('Unsupported URL scheme: '+url)
    key=(parts.scheme,parts.netloc)
    conns=getattr(_tcgcsv_http,'conns',None)
    if conns is None: conns=_tcgcsv_http.conns={}
    target=(parts.path or '/')+('?'+parts.query if parts.query else '')
    headers={'User-Agent':USER_AGENT,'Accept':accept,'Accept-Encoding':'gzip'}
    for attempt in range(2):
        conn=conns.get(key); reused=conn is not None
        if conn is None:
            factory=http.client.HTTPSConnection if parts.scheme=='https' else http.client.HTTPConnection
            conn=conns[key]=factory(parts.netloc,timeout=timeout)
        elif conn.sock is not None:
            conn.sock.settimeout(timeout)
        try:
            conn.request('GET',target,headers=headers)
            resp=conn.getresponse(); body=resp.read()
        except (http.client.HTTPException,OSError) as e:
            conn.close(); conns.pop(key,None)
            if reused and attempt==0 and isinstance(e,(ConnectionError,http.client.BadStatusLine)):
                continue  # the server closed an idle keep-alive connection; reconnect once
            raise urllib.error.URLError(e) from e
        if resp.will_close: conn.close(); conns.pop(key,None)
        break
    location=resp.getheader('Location') if resp.status in (301,302,303,307,308) else None
    if location and _redirects>0:
        return tcgcsv_fetch(urljoin(url,location),accept,timeout,_redirects-1)
    if not 200<=resp.status<300:
        raise urllib.error.HTTPError(url,resp.status,resp.reason,resp.headers,io.BytesIO(body))
    if (resp.getheader('Content-Encoding') or '').lower()=='gzip':
        try: body=gzip.decompress(body)
        except (OSError,EOFError) as e: raise urllib.error.URLError(f'corrupt gzip body: {e}') from e
    return body

def tcgcsv_text(url):
    """Fetch a small TCGCSV text resource with pacing and bounded transient retries."""
    for attempt in range(4):
        pace_tcgcsv_request()
        try:
            reserve_tcgcsv_request()
            return tcgcsv_fetch(url,'text/plain,*/*',30).decode('utf-8-sig').strip()
        except urllib.error.HTTPError as e:
            if e.code==429:
                mark_tcgcsv_throttled()
                raise RuntimeError('TCGCSV throttled this IP (HTTP 429). Stopping the sync; wait at least 10 minutes before retrying.') from e
            if e.code not in (408,500,502,503,504) or attempt==3: raise
            time.sleep(2**attempt)
        except (urllib.error.URLError,TimeoutError) as e:
            if attempt==3: raise RuntimeError(f'TCGCSV text request failed after 4 attempts for {url}: {e}') from e
            time.sleep(2**attempt)

def reserve_tcgcsv_request():
    """Persist a per-UTC-day request budget so repeated failed syncs cannot spam TCGCSV."""
    with _tcgcsv_budget_lock:
        ROOT.mkdir(parents=True,exist_ok=True)
        path=ROOT/'tcgcsv_request_budget.json'
        today=datetime.now(timezone.utc).date().isoformat()
        count=0; blocked_until=0.0
        if path.exists():
            try:
                saved=json.loads(path.read_text(encoding='utf-8'))
                if not isinstance(saved,dict): raise ValueError('expected a JSON object')
                if saved.get('day')==today:
                    count=int(saved.get('count',0)); blocked_until=float(saved.get('blocked_until_epoch',0) or 0)
                    if count<0 or not (0<=blocked_until<float('inf')):
                        raise ValueError('invalid request count or cooldown timestamp')
            except (OSError,ValueError,TypeError,AttributeError) as e:
                raise RuntimeError('TCGCSV request-budget file is unreadable; refusing requests to avoid exceeding source limits: '+str(e)) from e
        if blocked_until>time.time():
            remaining=int(blocked_until-time.time())
            raise RuntimeError(f'TCGCSV cooldown is active after throttling; wait about {max(1,(remaining+59)//60)} minute(s) before retrying.')
        if count>=TCGCSV_DAILY_REQUEST_BUDGET:
            raise RuntimeError(f'TCGCSV safety budget reached ({count:,} requests today UTC; cap {TCGCSV_DAILY_REQUEST_BUDGET:,}). Stop and wait for the UTC day to roll over.')
        payload={'day':today,'count':count+1,'blocked_until_epoch':blocked_until}
        tmp=path.with_suffix('.json.partial')
        tmp.write_text(json.dumps(payload),encoding='utf-8')
        tmp.replace(path)
        return count+1

def mark_tcgcsv_throttled(cooldown_seconds=600):
    """Persist a ten-minute cooldown after HTTP 429 so repeated GUI clicks don't retry."""
    with _tcgcsv_budget_lock:
        ROOT.mkdir(parents=True,exist_ok=True)
        path=ROOT/'tcgcsv_request_budget.json'
        today=datetime.now(timezone.utc).date().isoformat(); count=0
        if path.exists():
            try:
                saved=json.loads(path.read_text(encoding='utf-8'))
                if not isinstance(saved,dict): raise ValueError('expected a JSON object')
                if saved.get('day')==today:
                    count=int(saved.get('count',0))
                    if count<0: raise ValueError('invalid request count')
            except (OSError,ValueError,TypeError,AttributeError) as e:
                raise RuntimeError('Cannot persist TCGCSV cooldown because the request-budget file is unreadable: '+str(e)) from e
        payload={'day':today,'count':count,'blocked_until_epoch':time.time()+cooldown_seconds}
        tmp=path.with_suffix('.json.partial')
        tmp.write_text(json.dumps(payload),encoding='utf-8'); tmp.replace(path)

def tcgcsv_json(url, allow_not_found=False):
    """Fetch TCGCSV JSON with pacing, bounded transient retries, and explicit 404 handling.

    TCGCSV documents that empty product groups can return 404. Callers may opt to
    treat those specific product/price endpoints as empty; group-list failures stay fatal.
    HTTP 429 is never retried automatically because TCGCSV asks clients to wait 10 minutes.
    """
    for attempt in range(4):
        pace_tcgcsv_request()  # documented minimum pacing between requests
        try:
            reserve_tcgcsv_request()
            payload=json.loads(tcgcsv_fetch(url,'application/json',45))
            if not isinstance(payload,dict):
                raise RuntimeError(f'TCGCSV returned non-object JSON for {url}')
            return payload
        except urllib.error.HTTPError as e:
            if e.code == 429:
                mark_tcgcsv_throttled()
                raise RuntimeError('TCGCSV throttled this IP (HTTP 429). Stopping the sync; wait at least 10 minutes before retrying.') from e
            if e.code == 404 and allow_not_found:
                return {'success':True,'errors':[],'results':[]}
            if e.code not in (408,500,502,503,504) or attempt == 3:
                raise
            time.sleep(2 ** attempt)
        except (urllib.error.URLError, TimeoutError, json.JSONDecodeError) as e:
            if attempt == 3:
                raise RuntimeError(f'TCGCSV request failed after 4 attempts for {url}: {e}') from e
            time.sleep(2 ** attempt)

def tcgcsv_timestamp(raw):
    """Normalize TCGCSV last-updated marker for sortable historical observation times."""
    value=(raw or '').strip()
    for fmt in ('%m/%d/%Y, %I:%M:%S %p UTC','%Y-%m-%dT%H:%M:%S.%fZ','%Y-%m-%dT%H:%M:%SZ','%Y-%m-%d'):
        try:
            dt=datetime.strptime(value,fmt).replace(tzinfo=timezone.utc)
            return dt.isoformat(timespec='seconds')
        except ValueError:
            pass
    try:
        dt=datetime.fromisoformat(value.replace('Z','+00:00'))
        if dt.tzinfo is None: dt=dt.replace(tzinfo=timezone.utc)
        return dt.astimezone(timezone.utc).isoformat(timespec='seconds')
    except ValueError:
        # Preserve an unfamiliar marker rather than inventing an observation time.
        return value

def tcgcsv_results(payload, endpoint):
    if not isinstance(payload,dict) or not isinstance(payload.get('results'),list):
        raise RuntimeError(f'TCGCSV returned an unexpected response for {endpoint}')
    if payload.get('success') is False:
        raise RuntimeError(f'TCGCSV reported failure for {endpoint}: {payload.get("errors")}')
    return payload['results']

def tcgcsv_price_tuples(cid, item, source_time, collected_at):
    """Price rows for one TCGCSV price record (one product subtype)."""
    subtype=str(item.get('subTypeName') or 'Unspecified'); out=[]
    for field,label in TCGCSV_PRICE_FIELDS:
        val=numeric(item.get(field))
        if val is not None:
            out.append((cid,'tcgcsv_tcgplayer',f'{label}_{subtype}','USD',val,source_time,collected_at))
    return out

@contextmanager
def tcgcsv_sync_lock():
    """Cross-process lock shared by GUI and macOS background collector."""
    ROOT.mkdir(parents=True,exist_ok=True)
    path=ROOT/'tcgcsv_sync.lock'
    fd=None; acquired=False
    try:
        try:
            fd=os.open(path,os.O_CREAT|os.O_EXCL|os.O_WRONLY,0o600)
        except FileExistsError:
            try:
                age=time.time()-path.stat().st_mtime
                if age>6*60*60:
                    path.unlink()
                    fd=os.open(path,os.O_CREAT|os.O_EXCL|os.O_WRONLY,0o600)
                else:
                    raise RuntimeError('A TCGCSV sync already appears to be running. Wait for it to finish before starting another.')
            except FileNotFoundError:
                fd=os.open(path,os.O_CREAT|os.O_EXCL|os.O_WRONLY,0o600)
        acquired=True
        os.write(fd,f'pid={os.getpid()} started={utc()}\n'.encode('utf-8'))
        os.close(fd); fd=None
        yield
    finally:
        if fd is not None: os.close(fd)
        if acquired:
            try: path.unlink()
            except FileNotFoundError: pass

def fetch_tcgcsv_group(category_id, group, catalog_current=False, known_ids=frozenset()):
    """Network half of a group sync: returns (products, price_rows).

    When catalog_current is true the group's modifiedOn matches the stored catalog,
    so only prices are fetched and products is None. If a priced product is missing
    from known_ids the catalog is fetched anyway rather than storing orphan prices.
    """
    group_id=group.get('groupId')
    if group_id is None: return [],[]
    base=f'{TCGCSV_BASE}/{category_id}/{group_id}'
    products=None
    if not catalog_current:
        products=tcgcsv_results(tcgcsv_json(base+'/products',allow_not_found=True),base+'/products')
        if not products: return [],[]
    price_rows=tcgcsv_results(tcgcsv_json(base+'/prices',allow_not_found=True),base+'/prices')
    if products is None:
        prefix=f'tcgcsv:{category_id}:'
        if any(isinstance(pr,dict) and pr.get('productId') is not None and
               prefix+str(pr['productId']) not in known_ids for pr in price_rows):
            products=tcgcsv_results(tcgcsv_json(base+'/products',allow_not_found=True),base+'/products')
    return products,price_rows

def store_tcgcsv_group(store, report, category_id, game, group, products, price_rows, dataset_time):
    """Database half of a group sync. products=None means prices only (catalog unchanged)."""
    group_id=group.get('groupId')
    if group_id is None: return 0
    now=utc()
    modified=str(group.get('modifiedOn') or '')
    if products is None:
        prices=[]; priced=set()
        for item in price_rows:
            if isinstance(item,dict) and item.get('productId') is not None:
                cid=f'tcgcsv:{category_id}:{item["productId"]}'
                priced.add(cid); prices.extend(tcgcsv_price_tuples(cid,item,dataset_time,now))
        store.batch([],prices)
        return len(priced)
    if not products:
        report(f'{game}: group {group_id} has no products; skipped')
        if modified: store.batch([],(),[(category_id,str(group_id),modified,0,now)])
        return 0
    by_product={}
    for pr in price_rows:
        if isinstance(pr,dict) and pr.get('productId') is not None:
            by_product.setdefault(str(pr['productId']),[]).append(pr)
    cards=[]; prices=[]
    group_name=str(group.get('name') or group.get('abbreviation') or f'Group {group_id}')
    group_code=str(group.get('abbreviation') or group_id)
    for product in products:
        if not isinstance(product,dict) or product.get('productId') is None: continue
        product_id=str(product['productId']); cid=f'tcgcsv:{category_id}:{product_id}'
        ext=product.get('extendedData') or []
        ext_map={}
        if isinstance(ext,list):
            for item in ext:
                if isinstance(item,dict) and item.get('name') is not None:
                    ext_map[str(item['name']).strip().lower()]=item.get('value')
        number=str(ext_map.get('number') or ext_map.get('card number') or ext_map.get('collector number') or '')
        rarity=str(ext_map.get('rarity') or '')
        item_type=classify_tcgcsv_product(product.get('name') or product.get('cleanName'),ext_map)
        variants=by_product.get(product_id,[])
        finishes=sorted({str(x.get('subTypeName')) for x in variants if x.get('subTypeName')})
        details=json.dumps({
            'provider':'TCGCSV / TCGplayer cached product prices',
            'category_id':category_id,'group_id':group_id,'group_name':group_name,
            'product_id':product_id,'url':product.get('url'),'image_url':product.get('imageUrl'),
            'clean_name':product.get('cleanName'),'extended_data':ext,
            'price_variants':finishes,'item_type':item_type
        },ensure_ascii=False)
        cards.append((cid,game,str(product.get('name') or product.get('cleanName') or 'Unknown'),
                      group_code,number,rarity,','.join(finishes),details,now,item_type))
        # Store separate price types per subtype/printing. These are TCGCSV cached
        # market/listing metrics, not raw transaction-by-transaction sale records.
        for item in variants:
            prices.extend(tcgcsv_price_tuples(cid,item,dataset_time,now))
    store.batch(cards,prices,[(category_id,str(group_id),modified,len(cards),now)] if modified else ())
    return len(cards)

def ingest_tcgcsv(store, report, category_id, game, group, dataset_time):
    """Sync one TCGCSV group: product catalog plus daily market-price observations."""
    products,price_rows=fetch_tcgcsv_group(category_id,group)
    return store_tcgcsv_group(store,report,category_id,game,group,products,price_rows,dataset_time)

def _prefetch_in_order(items, fetch, depth=TCGCSV_PREFETCH_DEPTH):
    """Yield (item, fetch(item)) in order while one worker thread fetches ahead.

    Requests still run one at a time with the same pacing; only the database writes
    for one group now overlap the network requests for the next ones.
    """
    results=queue.Queue(maxsize=max(1,depth)); stop=threading.Event()
    def put(message):
        while not stop.is_set():
            try: results.put(message,timeout=0.25); return True
            except queue.Full: pass
        return False
    def worker():
        try:
            for item in items:
                if stop.is_set() or not put(('item',item,fetch(item))): return
            put(('end',None,None))
        except BaseException as exc:
            put(('error',None,exc))
    thread=threading.Thread(target=worker,name='tcgcsv-prefetch',daemon=True); thread.start()
    try:
        while True:
            kind,item,value=results.get()
            if kind=='end': return
            if kind=='error': raise value
            yield item,value
    finally:
        stop.set(); thread.join(timeout=5)

def _sync_tcgcsv_daily_locked(store, report):
    """Check the daily TCGCSV build marker, then sync Magic and Pokémon only if changed."""
    report('Checking TCGCSV last-updated marker')
    emit_progress(report,0,0,'Checking TCGCSV dataset marker')
    raw=tcgcsv_text(TCGCSV_LAST_UPDATED)
    if not raw: raise RuntimeError('TCGCSV last-updated.txt was empty')
    previous=store.get_setting('tcgcsv_dataset_marker','')
    categories=TCGCSV_CATEGORIES
    if previous == raw:
        # Databases from before the game list grew synced MTG and Pokémon only.
        try: synced=set(json.loads(store.get_setting('tcgcsv_categories','[1, 3]')))
        except ValueError: synced={1,3}
        categories=[(c,g) for c,g in TCGCSV_CATEGORIES if c not in synced]
        store.setting('tcgcsv_check_epoch',time.time())
        store.setting('tcgcsv_last_check',utc())
        if not categories:
            report('TCGCSV dataset is unchanged; no duplicate download or price snapshot created')
            emit_progress(report,1,1,'Dataset unchanged — no download needed')
            return 0
        report('Adding '+', '.join(g for _c,g in categories)+' from the current dataset')
    source_time=tcgcsv_timestamp(raw)
    total=0; counts={}
    for category_id,game in categories:
        report(f'Loading {game} group catalog (category {category_id})')
        emit_progress(report,0,0,f'Loading {game} group catalog')
        groups=tcgcsv_results(tcgcsv_json(f'{TCGCSV_BASE}/{category_id}/groups'),f'{game} groups')
        report(f'{game}: {len(groups):,} groups found; syncing products and daily prices')
        store_set_info(store,tcgcsv_group_set_rows(game,groups))  # set names and release dates for the calendar
        emit_progress(report,0,len(groups),f'Syncing {game} groups')
        known_ids={row[0] for row in store.q('SELECT id FROM cards WHERE id LIKE ?',(f'tcgcsv:{category_id}:%',))}
        saved={gid:(modified,count) for gid,modified,count in store.q(
            'SELECT group_id,modified_on,product_count FROM tcgcsv_groups WHERE category_id=?',(category_id,))}

        def fetch(group,category_id=category_id,known_ids=known_ids,saved=saved):
            modified=str(group.get('modifiedOn') or '')
            state=saved.get(str(group.get('groupId')))
            if not (modified and state and state[0]==modified):
                return fetch_tcgcsv_group(category_id,group)
            if state[1]==0: return [],[]  # unchanged empty group: no requests at all
            return fetch_tcgcsv_group(category_id,group,catalog_current=True,known_ids=known_ids)

        game_total=0; reused=0
        for idx,(group,(products,price_rows)) in enumerate(_prefetch_in_order(groups,fetch),1):
            if products is None: reused+=1
            game_total+=store_tcgcsv_group(store,report,category_id,game,group,products,price_rows,source_time)
            emit_progress(report,idx,len(groups),f'{game}: syncing groups')
            if idx%20==0 or idx==len(groups):
                report(f'{game}: groups {idx:,}/{len(groups):,}; products synced {game_total:,}')
        report(f'{game}: {reused:,} unchanged group catalogs reused; prices refreshed for every group')
        total+=game_total; counts[game]=game_total
    # Only mark the source marker successful after BOTH categories complete.
    if categories is TCGCSV_CATEGORIES: record_sync_counts(store,counts)
    # A database that synced before the record existed already has MTG and Pokémon.
    try: done=set(json.loads(store.get_setting('tcgcsv_categories','[1, 3]' if previous else '[]')))
    except ValueError: done=set()
    store.setting('tcgcsv_categories',json.dumps(sorted(done|{c for c,_g in categories})))
    store.setting('tcgcsv_dataset_marker',raw)
    if store.get_setting('daily_version','')==str(DAILY_VERSION): store.setting('daily_marker',raw)  # written by Store.batch
    store.setting('tcgcsv_dataset_time',source_time)
    store.setting('tcgcsv_success',utc())
    store.setting('tcgcsv_success_epoch',time.time())
    store.setting('tcgcsv_check_epoch',time.time())
    store.setting('tcgcsv_last_check',utc())
    return total

def sync_tcgcsv_daily(store, report):
    """Run a single TCGCSV sync, refusing concurrent GUI/LaunchAgent runs."""
    with tcgcsv_sync_lock():
        return _sync_tcgcsv_daily_locked(store,report)


def ingest_tcgcsv_archive_tree(store, extract_root, archive_day, report=lambda _msg: None):
    """Import one extracted TCGCSV daily archive for MTG/Pokémon into the compact daily history (market + cheapest listing)."""
    day = archive_day.isoformat() if hasattr(archive_day, 'isoformat') else str(archive_day)
    source_time = day + 'T20:00:00+00:00'
    valid_ids = {row[0] for row in store.q("SELECT id FROM cards WHERE id LIKE 'tcgcsv:%'")}
    if not valid_ids:
        raise RuntimeError("No TCGCSV catalog records are stored yet. Download today's prices once (Collectors tab) before backfilling history.")
    collected_at = utc(); pending = []; processed = 0; files_seen = 0
    root = Path(extract_root)
    for path in root.rglob('prices'):
        parts = path.relative_to(root).parts
        try: idx = parts.index(day)
        except ValueError: continue
        if len(parts) <= idx + 3: continue
        category = parts[idx + 1]
        if category not in {str(c) for c,_g in TCGCSV_CATEGORIES}: continue
        files_seen += 1
        try:
            with open(path, 'r', encoding='utf-8') as f: payload = json.load(f)
            rows = tcgcsv_results(payload, str(path))
        except (OSError, ValueError, TypeError) as exc:
            report(f'Skipping unreadable archive price file {path}: {exc}')
            continue
        for item in rows:
            if not isinstance(item, dict) or item.get('productId') is None: continue
            cid = f'tcgcsv:{category}:{item["productId"]}'
            if cid not in valid_ids: continue
            pending.extend(tcgcsv_price_tuples(cid, item, source_time, collected_at))
            if len(pending) >= 20000:
                store.upsert_daily(daily_rows_from_prices(pending,store.printing_id)); processed += len(pending); pending.clear()
    if pending:
        store.upsert_daily(daily_rows_from_prices(pending,store.printing_id)); processed += len(pending)
    if files_seen == 0:
        raise RuntimeError(f'No MTG/Pokémon price files were found in the extracted {day} archive; refusing to mark this date complete.')
    report(f'{day}: inspected {files_seen:,} MTG/Pokémon group price files; processed {processed:,} matching price observations')
    return processed


def find_7zip():
    """Locate a 7-Zip CLI on PATH, or in the default Windows install folders (not on PATH)."""
    found = shutil.which('7zz') or shutil.which('7z') or shutil.which('7za')
    if found or not sys.platform.startswith('win'): return found
    for base in (os.environ.get('ProgramFiles'), os.environ.get('ProgramFiles(x86)'), os.environ.get('ProgramW6432')):
        if base and (Path(base)/'7-Zip'/'7z.exe').is_file():
            return str(Path(base)/'7-Zip'/'7z.exe')
    return None


def backfill_tcgcsv_history(store, report, start_date, end_date):
    """Download each immutable daily archive once, extract supported categories, and ingest historical prices."""
    try:
        start = datetime.strptime(str(start_date), '%Y-%m-%d').date()
        end = datetime.strptime(str(end_date), '%Y-%m-%d').date()
    except ValueError as exc:
        raise ValueError('Dates must use YYYY-MM-DD format.') from exc
    if start < HISTORY_ARCHIVE_FIRST_DATE:
        raise ValueError(f'TCGCSV price archives begin on {HISTORY_ARCHIVE_FIRST_DATE.isoformat()}.')
    latest_allowed = datetime.now(timezone.utc).date() - timedelta(days=1)
    if end > latest_allowed:
        raise ValueError(f'Choose an end date on or before {latest_allowed.isoformat()} so the daily archive has time to publish.')
    if end < start: raise ValueError('End date must be on or after start date.')
    sevenzip = find_7zip()
    if not sevenzip:
        raise RuntimeError('Historical archives require the 7-Zip command-line tool. On Windows install 7-Zip from 7-zip.org (default folder); on macOS with Homebrew: brew install sevenzip. Then reopen the app and retry.')
    days=[]; current=start
    while current <= end:
        days.append(current); current += timedelta(days=1)
    completed_raw = store.get_setting('tcgcsv_archive_backfill_dates','[]')
    try: completed=set(json.loads(completed_raw))
    except (ValueError,TypeError): completed=set()
    total_inserted=0; missing=0; skipped=0; processed=0
    if not store.q("SELECT 1 FROM cards WHERE id LIKE 'tcgcsv:%' LIMIT 1") or not store.get_setting('tcgcsv_dataset_marker',''):
        raise RuntimeError("First download today's prices once (Collectors → Download today's prices now). The historical backfill needs the finished catalog to match archive product IDs to card names.")
    for idx, day in enumerate(days,1):
        day_text=day.isoformat()
        if day_text in completed:
            skipped += 1; report(f'History backfill {idx}/{len(days)}: {day_text} already imported; skipping immutable archive')
            emit_progress(report,idx,len(days),'Historical archive dates')
            continue
        report(f'History backfill {idx}/{len(days)}: downloading TCGCSV archive for {day_text}')
        emit_progress(report,idx-1,len(days),'Historical archive dates')
        with tempfile.TemporaryDirectory(prefix='cmt_tcgcsv_history_') as tmp:
            tmp_path=Path(tmp); archive=tmp_path/f'prices-{day_text}.ppmd.7z'; extract=tmp_path/'extract'; extract.mkdir()
            url=f'{HISTORY_ARCHIVE_BASE}/prices-{day_text}.ppmd.7z'
            try:
                download(url,archive,report)
            except urllib.error.HTTPError as exc:
                if exc.code == 404:
                    missing += 1; report(f'No archive published for {day_text} (HTTP 404); leaving date eligible for retry')
                    continue
                if exc.code == 403:
                    raise RuntimeError('TCGCSV is refusing archive downloads (HTTP 403): its price archive has been taken offline, '
                                       'so no backfill is possible until it returns. For MTG, use Collectors → Import last 90 days '
                                       'of MTG prices (MTGJSON).') from exc
                raise RuntimeError(f'Historical archive download failed for {day_text}: HTTP {exc.code}') from exc
            emit_progress(report,0,0,f'Extracting {day_text} archive with 7-Zip')
            result=subprocess.run([sevenzip,'x','-y',f'-o{extract}',str(archive)],capture_output=True,text=True,timeout=240)
            if result.returncode != 0:
                detail=(result.stderr or result.stdout or '').strip()[-1200:]
                raise RuntimeError(f'7-Zip could not extract {day_text} archive (exit {result.returncode}): {detail}')
            count=ingest_tcgcsv_archive_tree(store,extract,day,report)
            total_inserted += count; processed += 1
            completed.add(day_text)
            store.setting('tcgcsv_archive_backfill_dates',json.dumps(sorted(completed)))
        emit_progress(report,idx,len(days),'Historical archive dates')
    report(f'Historical backfill finished: {processed} dates imported, {skipped} already done, {missing} archive dates unavailable, {total_inserted:,} matching observations processed')
    return total_inserted


def _open_text(path):
    path=str(path)
    opener=lzma.open if path.endswith('.xz') else gzip.open if path.endswith('.gz') else open
    return opener(path,'rt',encoding='utf-8',newline='')

class _JsonStream:
    """Minimal incremental reader over a text stream for walking large JSON documents."""
    def __init__(self,f,chunk_size):
        self.f=f; self.chunk_size=chunk_size; self.buf=''; self.ix=0; self.decoder=json.JSONDecoder()
    def _more(self):
        extra=self.f.read(self.chunk_size)
        if not extra: return False
        self.buf=self.buf[self.ix:]+extra; self.ix=0
        return True
    def peek(self):
        while True:
            while self.ix<len(self.buf) and self.buf[self.ix] in ' \t\r\n': self.ix+=1
            if self.ix<len(self.buf): return self.buf[self.ix]
            if not self._more(): raise ValueError('Unexpected end of JSON document')
    def expect(self,ch):
        if self.peek()!=ch: raise ValueError(f'Expected {ch!r} in JSON document')
        self.ix+=1
    def skip_comma(self):
        if self.peek()==',': self.ix+=1
    def value(self):
        self.peek()
        while True:
            try:
                obj,end=self.decoder.raw_decode(self.buf,self.ix)
            except json.JSONDecodeError:
                if not self._more(): raise ValueError('Incomplete JSON value')
                continue
            if end>=len(self.buf) and self._more(): continue  # a number may continue in the next chunk
            self.ix=end
            return obj

def stream_json_object_member(f, member, chunk_size=1<<20):
    """Yield (key, value) for each entry of one member object of a top-level JSON object.

    MTGJSON's AllPrices is {"meta":{...},"data":{uuid:{...},...}} at ~1 GB uncompressed,
    so entries are decoded one card at a time instead of loading the document.
    """
    s=_JsonStream(f,chunk_size); s.expect('{')
    while s.peek()!='}':
        key=s.value(); s.expect(':')
        if key!=member:
            s.value()
        else:
            s.expect('{')
            while s.peek()!='}':
                entry=s.value(); s.expect(':')
                yield entry,s.value()
                s.skip_comma()
            return
        s.skip_comma()
    raise ValueError(f'JSON document has no "{member}" object')

def load_mtgjson_tcgplayer_ids(path):
    """Map MTGJSON uuid -> {finish: TCGplayer product id} from cardIdentifiers.csv (.xz/.gz allowed)."""
    ids={}
    with _open_text(path) as f:
        reader=csv.DictReader(f)
        missing={'uuid','tcgplayerProductId'}-set(reader.fieldnames or ())
        if missing: raise RuntimeError('MTGJSON cardIdentifiers.csv is missing columns: '+', '.join(sorted(missing)))
        for row in reader:
            product=(row.get('tcgplayerProductId') or '').strip()
            etched=(row.get('tcgplayerEtchedProductId') or '').strip()
            finishes={}
            if product: finishes['normal']=finishes['foil']=product
            if etched: finishes['etched']=etched
            if finishes and row.get('uuid'): ids[row['uuid']]=finishes
    return ids

def ingest_mtgjson_prices(store, prices_path, ids, report):
    """Import MTGJSON TCGplayer retail history for MTG cards already in the TCGCSV catalog.

    Rows use price types matching TCGCSV (market_Normal / market_Foil) under source
    'mtgjson_tcgplayer', so they extend the same daily series used for rankings; on days
    covered by both, the TCGCSV observation's later timestamp wins.
    Returns (price rows processed, cards matched).
    """
    valid={row[0] for row in store.q("SELECT id FROM cards WHERE id LIKE 'tcgcsv:1:%'")}
    collected_at=utc(); pending=[]; processed=0; matched=set(); seen=0
    with _open_text(prices_path) as f:
        for uuid,formats in stream_json_object_member(f,'data'):
            seen+=1
            finishes=ids.get(uuid)
            tcgplayer=((formats.get('paper') or {}).get('tcgplayer') or {}) if finishes and isinstance(formats,dict) else {}
            if tcgplayer.get('currency','USD')=='USD':
                for finish,series in (tcgplayer.get('retail') or {}).items():
                    product=finishes.get(finish); subtype=MTGJSON_FINISH_SUBTYPES.get(finish)
                    cid=f'tcgcsv:1:{product}'
                    if not product or not subtype or cid not in valid or not isinstance(series,dict): continue
                    for day,price in series.items():
                        val=numeric(price)
                        if val is None or _source_day(day) is None: continue
                        pending.append((cid,'mtgjson_tcgplayer',f'market_{subtype}','USD',val,f'{day}T12:00:00+00:00',collected_at))
                        matched.add(cid)
            if len(pending)>=20000:
                store.batch([],pending); processed+=len(pending); pending.clear()
            if seen%5000==0:
                emit_progress(report,0,0,f'MTGJSON: {seen:,} printings read; {len(matched):,} matched')
                if seen%25000==0: report(f'MTGJSON: {seen:,} printings read; {len(matched):,} cards matched to your catalog')
    if pending:
        store.batch([],pending); processed+=len(pending)
    return processed,len(matched)

def backfill_mtgjson_history(store, report):
    """Download MTGJSON identifiers + 90-day AllPrices once and import MTG TCGplayer history."""
    if not store.q("SELECT 1 FROM cards WHERE id LIKE 'tcgcsv:1:%' LIMIT 1"):
        raise RuntimeError("First download today's prices once (Collectors → Download today's prices now). MTGJSON history is matched to that catalog by TCGplayer product ID.")
    with tempfile.TemporaryDirectory(prefix='cmt_mtgjson_') as tmp:
        tmp=Path(tmp); ids_path=tmp/'cardIdentifiers.csv.xz'; prices_path=tmp/'AllPrices.json.xz'
        report('MTGJSON: downloading card identifiers (~11 MB)')
        download(f'{MTGJSON_BASE}/csv/cardIdentifiers.csv.xz',ids_path,report)
        ids=load_mtgjson_tcgplayer_ids(ids_path)
        report(f'MTGJSON: {len(ids):,} printings have TCGplayer product IDs')
        report('MTGJSON: downloading 90-day price history (~45 MB compressed)')
        download(f'{MTGJSON_BASE}/AllPrices.json.xz',prices_path,report)
        report('MTGJSON: importing TCGplayer price history (decompresses ~1 GB as it streams; this takes a few minutes)')
        rows,cards=ingest_mtgjson_prices(store,prices_path,ids,report)
        report('MTGJSON: adding 90 days of Card Kingdom buylist and Cardmarket prices')
        valid={card_key(cid) for (cid,) in store.q("SELECT id FROM cards WHERE id LIKE 'tcgcsv:1:%' AND item_type='card'")}
        with _open_text(prices_path) as f:
            batch=[]
            for item in stream_json_object_member(f,'data'):
                batch.append(item)
                if len(batch)>=5000: store.upsert_daily(mtgjson_vendor_rows(batch,ids,store.printing_id,valid)); batch.clear()
            if batch: store.upsert_daily(mtgjson_vendor_rows(batch,ids,store.printing_id,valid))
    store.setting('mtgjson_history_import',utc())
    report(f'MTGJSON import finished: {rows:,} daily price observations for {cards:,} MTG cards')
    return rows


def windowless_python():
    """pythonw.exe beside the running interpreter, so scheduled runs don't open a console."""
    exe=Path(sys.executable).resolve()
    candidate=exe.with_name('pythonw.exe')
    return candidate if candidate.is_file() else exe

def windows_task_xml(python, script, today=None, data=None):
    """Task Scheduler definition: daily runs, catch up after sleep/shutdown, no stored password.
    data: the data folder to sync into, passed as --data so the task does not depend on CMT_DATA being set."""
    today=today or datetime.now().date()
    triggers=''.join(
        f'<CalendarTrigger><StartBoundary>{today.isoformat()}T{at}:00</StartBoundary><Enabled>true</Enabled>'
        '<ScheduleByDay><DaysInterval>1</DaysInterval></ScheduleByDay></CalendarTrigger>' for at in WINDOWS_TASK_TIMES)
    arguments=subprocess.list2cmdline([str(script),'--sync']+(['--data',str(data)] if data else []))
    return f'''<?xml version="1.0" encoding="UTF-16"?>
<Task version="1.2" xmlns="http://schemas.microsoft.com/windows/2004/02/mit/task">
  <RegistrationInfo><Description>{xml_escape(APP)}: daily TCGCSV price sync (all supported games). Checks the build marker first; no purchases.</Description></RegistrationInfo>
  <Triggers>{triggers}</Triggers>
  <Principals><Principal id="Author"><LogonType>InteractiveToken</LogonType><RunLevel>LeastPrivilege</RunLevel></Principal></Principals>
  <Settings>
    <MultipleInstancesPolicy>IgnoreNew</MultipleInstancesPolicy>
    <DisallowStartIfOnBatteries>false</DisallowStartIfOnBatteries>
    <StopIfGoingOnBatteries>false</StopIfGoingOnBatteries>
    <StartWhenAvailable>true</StartWhenAvailable>
    <ExecutionTimeLimit>PT4H</ExecutionTimeLimit>
    <Enabled>true</Enabled>
  </Settings>
  <Actions Context="Author"><Exec><Command>{xml_escape(str(python))}</Command><Arguments>{xml_escape(arguments)}</Arguments><WorkingDirectory>{xml_escape(str(Path(script).parent))}</WorkingDirectory></Exec></Actions>
</Task>
'''

def install_windows_sync_task(python, script, task_name=WINDOWS_TASK_NAME, today=None, data=None):
    with tempfile.TemporaryDirectory(prefix='cmt_task_') as tmp:
        definition=Path(tmp)/'task.xml'
        definition.write_text(windows_task_xml(python,script,today,data),encoding='utf-16')
        result=subprocess.run(['schtasks','/Create','/TN',task_name,'/XML',str(definition),'/F'],capture_output=True,text=True,check=False)
    if result.returncode!=0:
        raise RuntimeError('Task Scheduler could not create the task: '+(result.stderr.strip() or result.stdout.strip()))

def windows_sync_task_installed(task_name=WINDOWS_TASK_NAME):
    """True/False when Task Scheduler answers, None when it cannot be asked (not Windows)."""
    if not sys.platform.startswith('win'): return None
    try:
        result=subprocess.run(['schtasks','/Query','/TN',task_name],capture_output=True,text=True,check=False,
                              creationflags=getattr(subprocess,'CREATE_NO_WINDOW',0),timeout=15)
    except (OSError,subprocess.SubprocessError): return None
    return result.returncode==0

def remove_windows_sync_task(task_name=WINDOWS_TASK_NAME):
    result=subprocess.run(['schtasks','/Delete','/TN',task_name,'/F'],capture_output=True,text=True,check=False)
    detail=(result.stderr+' '+result.stdout).strip()
    if result.returncode!=0 and 'cannot find' not in detail.lower():
        raise RuntimeError('Task Scheduler could not delete the task: '+detail)

def friendly_error(text):
    """A plain explanation for a failed download or job, followed by the technical detail."""
    t=str(text or ''); low=t.lower()
    if any(x in low for x in ('getaddrinfo','urlopen error','timed out','timeout','connection reset','connection refused',
                              'no route','network is unreachable','temporary failure in name resolution','remote end closed')):
        head="Couldn't reach the price source. Check your internet connection and try again later — your saved data is safe."
    elif 'http error 429' in low or 'too many requests' in low:
        head='The price site asked us to slow down. Nothing is wrong; try again in an hour.'
    elif any(f'http error {c}' in low for c in (500,502,503,504)):
        head='The price site is having problems right now. Try again later — your saved data is safe.'
    elif 'http error 403' in low or 'http error 404' in low:
        head='The price site refused or moved this download. The app keeps working with the data it already has.'
    elif 'database is locked' in low:
        head='The price database is busy — another copy of the app (or the background update) may be running. Wait a minute and try again.'
    elif 'no space left' in low or 'disk full' in low or 'errno 28' in low:
        head='Your disk is full. Free some space (or lower "Keep detailed daily price rows" in Settings) and try again.'
    elif 'permission' in low or 'access is denied' in low:
        head="Windows wouldn't let the app write a file. Close other copies of the app and make sure the data folder isn't read-only."
    else:
        return t
    return f'{head}\n\nDetails: {t}'

def csv_heading(name):
    """Readable spreadsheet heading for a machine column name: 'return_7d_pct' -> 'Return 7d %'."""
    if not re.fullmatch(r'[a-z0-9_]+',str(name)): return name
    words=re.sub(r'_pct$',' %',re.sub(r'_usd$',' $',str(name))).replace('_',' ')
    for short,full in (('ck','CK'),('eu','EU'),('id','ID'),('edhrec','EDHREC'),('nm','NM'),('lp','LP'),('mp','MP'),('qty','Qty'),('fx','FX')):
        words=re.sub(rf'\b{short}\b',full,words)
    return words[:1].upper()+words[1:]

def plural(n, word):
    """'1 day', '3 days'."""
    return f"{n:,} {word}{'' if n==1 else 's'}"

def parse_trade_date(text):
    """ISO date from 2026-10-29, 10/29/2026, 10/29/26 or 'today'; None when unreadable or in the future."""
    t=str(text or '').strip().lower()
    if t in ('','today'): return date.today().isoformat()
    for fmt in ('%Y-%m-%d','%m/%d/%Y','%m/%d/%y','%m-%d-%Y'):
        try: d=datetime.strptime(t,fmt).date()
        except ValueError: continue
        return d.isoformat() if d<=date.today() else None
    return None

# Worker-thread events handled by Terminal.handle_async_event (the rest are collector log/done/error).
ASYNC_EVENTS = ('kpis','progress','rank_progress','rankings_done','rankings_error','model_ready','model_error',
                'annotated','risk_free','risk_free_error','catalysts','set_names','backtest','facts','longterm','bg_note')

class Terminal(tk.Tk if tk else object):
    def __init__(self):
        super().__init__(); self.store=Store(); self.events=queue.Queue(); self.busy=False
        self.title('Card Market Terminal  |  MTG · Pokémon · One Piece · Riftbound'); self._fit_window()
        self.colors={'bg':'#0d1523','panel':'#182337','light':'#dbe7fa','muted':'#95aac7','accent':'#5ca9ff','amber':'#ffb000'}
        self.configure(bg=self.colors['bg']); self.theme(); self.make_ui()
        self.refresh(); self.after(200,self.drain); self.protocol('WM_DELETE_WINDOW',self.close)
    def theme(self):
        st=ttk.Style(self); st.theme_use('clam')
        st.configure('.',font=('Helvetica',11),background=self.colors['bg'],foreground=self.colors['light'])
        st.configure('TFrame',background=self.colors['bg']); st.configure('Panel.TFrame',background=self.colors['panel'])
        st.configure('TLabel',background=self.colors['bg'],foreground=self.colors['light']); st.configure('Small.TLabel',font=('Helvetica',10),foreground=self.colors['muted'])
        st.configure('TButton',padding=(13,8),background='#273c59',foreground='#f4f7fd')
        st.map('TButton',background=[('active','#365a86')]); st.configure('TNotebook',borderwidth=0)
        st.configure('TNotebook.Tab',padding=(12,8),background='#192a40',foreground='#dbe7fa')
        st.map('TNotebook.Tab',background=[('selected','#345d88')]); st.configure('Treeview',rowheight=26,background='#17253a',fieldbackground='#17253a',foreground='#e3eeff')
        st.configure('Treeview.Heading',background='#253b57',foreground='#e7f0ff',font=('Helvetica',10,'bold'))
        st.map('Treeview',background=[('selected','#3b648f')])
        st.configure('TEntry',fieldbackground='#eff5ff',foreground='#13223a')
        st.map('TCombobox',fieldbackground=[('readonly','#eff5ff')],foreground=[('readonly','#13223a')],
               selectbackground=[('readonly','#eff5ff')],selectforeground=[('readonly','#13223a')])
    def make_ui(self):
        top=ttk.Frame(self,padding=(18,10)); top.pack(fill='x')
        ttk.Label(top,text='CARD MARKET TERMINAL',font=('Helvetica',20,'bold'),foreground=self.colors['amber']).pack(side='left')
        cmd=ttk.Frame(top); cmd.pack(side='right')
        ttk.Label(cmd,text='COMMAND ›',font=('Consolas',11,'bold'),foreground=self.colors['amber']).pack(side='left',padx=(0,6))
        self.command=tk.StringVar()
        self.command_entry=ttk.Entry(cmd,textvariable=self.command,width=40,font=('Consolas',12))
        self.command_entry.pack(side='left'); self.command_entry.bind('<Return>',lambda _e:self.run_command())
        ttk.Button(cmd,text='Go',command=self.run_command).pack(side='left',padx=(6,0))
        ttk.Button(cmd,text='Glossary',command=self.show_glossary).pack(side='left',padx=(6,0))
        ttk.Label(cmd,text='HELP · Ctrl+K · click a column heading to explain it',style='Small.TLabel').pack(side='left',padx=(8,0))
        self.bind_all('<Control-k>',lambda _e:(self.command_entry.focus_set(),self.command_entry.select_range(0,'end')))
        self.nb=ttk.Notebook(self); self.nb.pack(fill='both',expand=True,padx=16,pady=(0,4))
        self.tabs={}
        for name in self.TAB_NAMES:
            fr=ttk.Frame(self.nb,padding=(13,8)); self.nb.add(fr,text=name); self.tabs[name]=fr
        self.ranking_data={'all':[],'fresh':[],'sharpe':[],'opportunities':[]}; self.row_index={}; self.rows_by_card={}
        self.pricing=stored_pricing(self.store); self.forecast_model=None; self.model_busy=False
        self._annotation_key=None; self._annotation_pending=None
        self.portfolio_rows=[]; self.catalysts=[]; self.set_name_map={}; self.set_stats={}
        self.today_tab(); self.overview(); self.history_tab(); self.portfolio_tab(); self.sharpe_opportunities_tab(); self.buy_list_tab()
        self.sets_tab(); self.backtest_tab(); self.collector_tab(); self.settings_tab()
        activity=ttk.Frame(self,padding=(18,0,18,2)); activity.pack(fill='x')
        self.activity_text=tk.StringVar(value='Activity: idle')
        ttk.Label(activity,textvariable=self.activity_text,style='Small.TLabel',width=38).pack(side='left',padx=(0,8))
        self.activity_progress=ttk.Progressbar(activity,mode='indeterminate',length=340,maximum=100)
        self.activity_progress.pack(side='left',fill='x',expand=True)
        self.status=tk.StringVar(value='Ready. Tip: click any row to read its full text here.')
        ttk.Label(self,textvariable=self.status,style='Small.TLabel',wraplength=1300,justify='left').pack(anchor='w',padx=20,pady=(0,8))
        self.load_catalysts(); self._load_set_names(); self._apply_advanced(); self.nb.select(self.tabs['Today'])
    def _fit_window(self):
        sw,sh=self.winfo_screenwidth(),self.winfo_screenheight()
        w,h=min(1440,sw-40),min(920,sh-80)
        self.geometry(f'{w}x{h}+{max(0,(sw-w)//2)}+{max(0,(sh-h)//3)}'); self.minsize(min(1000,w),min(640,h))
        if (sw<1480 or sh<1000) and sys.platform.startswith('win'):
            try: self.state('zoomed')  # small screens: use all of it
            except tk.TclError: pass

    def _auto_wrap(self):
        """Long explanatory labels re-wrap to the window width, so nothing runs off the edge on a smaller screen."""
        def fit(label):
            try:
                parent=label.master; width=parent.winfo_width()-label.winfo_x()-16
                if width>200 and abs(int(str(label.cget('wraplength') or 0))-width)>8: label.configure(wraplength=width)
            except (tk.TclError,ValueError): pass
        for widget in self._descendants(self):
            try: wrap=int(str(widget.cget('wraplength') or 0))
            except (tk.TclError,ValueError): continue
            if wrap>=900:  # a window's <Configure> also fires for every child, so only react to the window itself
                widget.master.bind('<Configure>',lambda e,l=widget:(e.widget is l.master) and fit(l),add='+')

    def section(self,parent,title,desc=''):
        ttk.Label(parent,text=title,font=('Helvetica',16,'bold')).pack(anchor='w',pady=(4,4))
        if desc: ttk.Label(parent,text=desc,style='Small.TLabel',wraplength=1000).pack(anchor='w',pady=(0,12))
    def gridview(self,parent,cols,height=13):
        frame=ttk.Frame(parent); frame.pack(fill='both',expand=True,pady=7)
        tree=ttk.Treeview(frame,columns=cols,show='headings',height=height)
        for col in cols:
            tree.heading(col,text=col,command=lambda c=col: self.explain(c)); tree.column(col,width=150 if len(cols)>4 else 210,anchor='w')
        for tag,color in (('up','#5fd38d'),('down','#ff7b7b'),('hot','#3ee07a'),('cold','#ff5c5c'),('warn','#ffb000')):
            tree.tag_configure(tag,foreground=color)
        vs=ttk.Scrollbar(frame,orient='vertical',command=tree.yview); hs=ttk.Scrollbar(frame,orient='horizontal',command=tree.xview)
        tree.configure(yscrollcommand=vs.set,xscrollcommand=hs.set)
        frame.rowconfigure(0,weight=1); frame.columnconfigure(0,weight=1)
        tree.grid(row=0,column=0,sticky='nsew'); vs.grid(row=0,column=1,sticky='ns'); hs.grid(row=1,column=0,sticky='ew')
        tree.bind('<<TreeviewSelect>>',lambda _e,t=tree:self._show_row_text(t),add='+')
        return tree
    def _show_row_text(self,tree):
        """Long cells are cut off in a table, so the selected row's longest text is shown in full in the status bar."""
        sel=tree.selection()
        if not sel or not hasattr(self,'status'): return
        cols=list(tree['columns']); values=[str(v) for v in tree.item(sel[0],'values')]
        named=[(c,v) for c,v in zip(cols,values) if c!='ID']
        longest=max(named,key=lambda cv:len(cv[1]),default=None)
        if longest and len(longest[1])>45:
            label=next((v for c,v in named if c in ('Card','Name','Strategy','Trade','Set')),'')
            self.status.set((f'{label} — ' if label and label!=longest[1] else '')+f'{longest[0]}: {longest[1]}')
    def overview(self):
        p=self.tabs['Overview']
        head=ttk.Frame(p); head.pack(fill='x')
        ttk.Label(head,text='Market monitor',font=('Helvetica',16,'bold')).pack(side='left')
        self.monitor_note=tk.StringVar(value='Waiting for rankings…')
        ttk.Label(head,textvariable=self.monitor_note,style='Small.TLabel').pack(side='left',padx=12)
        ttk.Button(head,text='Refresh',command=self.refresh).pack(side='right')
        ttk.Button(head,text='Daily brief (HTML)',command=self.open_daily_brief).pack(side='right',padx=8)
        tiles=ttk.Frame(p); tiles.pack(fill='x',pady=(6,2)); self.monitor_tiles={}
        bg,panel,muted,light=self.colors['bg'],self.colors['panel'],self.colors['muted'],self.colors['light']
        for row,game in enumerate(SUPPORTED_GAMES):
            tk.Label(tiles,text=game.upper(),bg=bg,fg=self.colors['amber'],font=('Helvetica',11,'bold'),width=9,anchor='w').grid(row=row,column=0,sticky='w')
            for col,key in enumerate(self.MONITOR_TILES,1):
                tiles.columnconfigure(col,weight=1,uniform='mon')
                cell=tk.Frame(tiles,bg=panel,padx=8,pady=3); cell.grid(row=row,column=col,sticky='nsew',padx=(0,5),pady=(0,5))
                name=tk.Label(cell,text=self.MONITOR_TILE_NAMES.get(key,key).upper(),bg=panel,fg=muted,font=('Helvetica',8),cursor='question_arrow')
                name.pack(anchor='w'); name.bind('<Button-1>',lambda _e,k=key:self.explain(k))
                var=tk.StringVar(value='—'); label=tk.Label(cell,textvariable=var,bg=panel,fg=light,font=('Helvetica',12,'bold'))
                label.pack(anchor='w'); self.monitor_tiles[(game,key)]=(var,label)
        mid=ttk.Frame(p); mid.pack(fill='both',expand=True)
        mid.columnconfigure(0,weight=3); mid.columnconfigure(1,weight=2); mid.rowconfigure(0,weight=1)
        chart_box=ttk.Frame(mid); chart_box.grid(row=0,column=0,sticky='nsew',padx=(0,8))
        bar=ttk.Frame(chart_box); bar.pack(fill='x')
        self.index_mode=tk.StringVar(value=self.INDEX_MODES[0]); self.index_range=tk.StringVar(value='90 days')
        for var,values,width in ((self.index_mode,list(self.INDEX_MODES),24),(self.index_range,['30 days','60 days','90 days'],9)):
            box=ttk.Combobox(bar,textvariable=var,values=values,state='readonly',width=width); box.pack(side='left',padx=(0,6))
            box.bind('<<ComboboxSelected>>',lambda _e:self.populate_overview())
        ttk.Label(bar,text='Average daily price change of cards worth $1+, starting at 100 (110 = up about 10%). Hover to read a day.',
                  style='Small.TLabel').pack(side='left',padx=6)
        self.index_chart=tk.Canvas(chart_box,height=190,bg='#0b1726',highlightthickness=1,highlightbackground='#253b57')
        self.index_chart.pack(fill='both',expand=True,pady=(4,0))
        self.index_chart.bind('<Configure>',lambda _e:self._draw_index_chart())
        self.index_chart.bind('<Motion>',self._index_hover)
        self.index_chart.bind('<Leave>',lambda _e:self.index_chart.delete('hover'))
        alerts=ttk.LabelFrame(mid,text=' ALERTS · SIGNALS · CATALYSTS ',padding=4); alerts.grid(row=0,column=1,sticky='nsew')
        self.alert_tree=self.gridview(alerts,('ID','Type','Item','Detail'),7)
        self.alert_tree.column('ID',width=0,minwidth=0,stretch=False)
        for col,width in (('Type',75),('Item',190),('Detail',330)):
            self.alert_tree.column(col,width=width,minwidth=60,stretch=(col=='Detail'))
        self.alert_tree.bind('<Double-1>',lambda _e:self._open_alert())
        bottom=ttk.Frame(p); bottom.pack(fill='both',expand=True,pady=(4,0))
        for i in range(3): bottom.columnconfigure(i,weight=1)
        bottom.rowconfigure(0,weight=1)
        self.gainers_tree=self._mini_table(bottom,0,' TOP GAINERS · 7 DAYS ($5+, 6+ trading days) ',('ID','Card','Price','7d %','Trading days'))
        self.losers_tree=self._mini_table(bottom,1,' TOP LOSERS · 7 DAYS ',('ID','Card','Price','7d %','Trading days'))
        self.blotter_tree=self._mini_table(bottom,2,' BEST BUYS NOW · after fees & shipping ',('ID','Card','Low','Cond','Exp. profit','Qty'))
        self.kpis=ttk.Label(p,text='',style='Small.TLabel'); self.kpis.pack(anchor='w',pady=(2,0))
    TAB_NAMES=('Today','Overview','Cards to Look For','Sharpe & Opportunities','Market History','Sets & Catalysts','Portfolio','Backtest & Trades','Collectors','Settings')
    COMMANDS=(('TODAY','what to buy and sell today, and the card checker (should I buy at this price? what should I sell for?)'),
              ('<card name>','open its chart; add FOIL for the foil printing (e.g. Sheoldred FOIL)'),
              ('MON','market monitor: indices, breadth, movers, best buys, alerts'),
              ('BUY','cards to look for (after fees, liquidity and forecast)'),
              ('RANK','steadiest risers and momentum rankings (advanced)'),
              ('SETS  or  CAL','set heatmap and release calendar'),
              ('SET <code>','cards to look for in one set, e.g. SET DSK'),
              ('CYCLE','release cycle: new-set curves, pre-sell and dip opportunities measured on your history'),
              ('PORT','portfolio & watchlist with sell signals'),
              ('BT  or  TRADES','how the advice did on past prices, and your own trade log'),
              ('HIST','market history'),
              ('SYNC',"download today's prices now"),
              ('BRIEF','open the daily brief (also written after each background sync)'),
              ('GLOSSARY  or  DEFINE <word>','what every column and action means, e.g. DEFINE max buy'),
              ('HELP','this list'))
    COMMAND_TABS={'MON':'Overview','TOP':'Overview','MOV':'Overview','IDX':'Overview','BUY':'Cards to Look For',
                  'LOOK':'Cards to Look For','RANK':'Sharpe & Opportunities','SHARPE':'Sharpe & Opportunities',
                  'SETS':'Sets & Catalysts','SECT':'Sets & Catalysts','CAL':'Sets & Catalysts','PORT':'Portfolio',
                  'W':'Portfolio','WATCH':'Portfolio','HIST':'Market History','GP':'Market History','COL':'Collectors',
                  'TODAY':'Today','DO':'Today','CHECK':'Today','BT':'Backtest & Trades','BACKTEST':'Backtest & Trades','TRADES':'Backtest & Trades','TRADE':'Backtest & Trades'}
    COMMAND_VIEWS={'CYCLE':'Release cycle','NEW':'Release cycle','PRESELL':'Release cycle','VARIANTS':'Variants'}
    def run_command(self,text=None):
        """Bloomberg-style command line: a function code, or a card name to chart."""
        raw=(self.command.get() if text is None else text).strip()
        if not raw: return
        word,_,arg=raw.upper().partition(' '); arg=arg.strip()
        if word in ('HELP','?'):
            messagebox.showinfo(APP,'Commands (type in the COMMAND box at the top, then press Enter):\n\n'+
                                '\n'.join(f'{code:<14} {desc}' for code,desc in self.COMMANDS))
        elif word=='SYNC' and not arg:
            if hasattr(self,'start_tcgcsv'): self.start_tcgcsv()
        elif word in ('GLOSSARY','DEFINE','WHAT'):
            self.show_glossary(arg)
        elif word=='BRIEF' and not arg:
            self.open_daily_brief()
        elif word=='SET' and arg:
            self.show_set_cards('All',arg)
        elif word in self.COMMAND_TABS and not arg:
            self.nb.add(self.tabs[self.COMMAND_TABS[word]]); self.nb.select(self.tabs[self.COMMAND_TABS[word]])  # add() restores a hidden tab
        elif word in self.COMMAND_VIEWS and not arg:
            self.set_group.set(self.COMMAND_VIEWS[word]); self.nb.select(self.tabs['Sets & Catalysts']); self.populate_sets()
        else:
            self.open_card_by_name(raw)
        self.command.set('')
    def open_card_by_name(self,query):
        q=query.strip().casefold()
        if q.endswith(' go'): q=q[:-3].strip()
        foil=q.endswith(' foil')
        if foil: q=q[:-5].strip()
        rows=self.ranking_data.get('fresh') or []
        hits=[r for r in rows if r['card_name'].casefold()==q] or [r for r in rows if q in r['card_name'].casefold()]
        names={r['card_name'] for r in hits}
        if hits and len(names)==1:
            want=lambda r: (r.get('printing') not in ('','Normal'))==foil
            best=max(hits,key=lambda r:(want(r),r.get('price_changes_30d') or 0,r.get('latest_price') or 0))
            self.history_series=best['price_type']; self.history_id.set(best['card_id'])
            self.nb.select(self.tabs['Market History']); self.load_history()
            self.status.set(f"{best['name']} · {best.get('set_code') or ''} — {len(hits)} matching printing(s); pick another in Market History search")
            return
        self.history_search.set(query); self.nb.select(self.tabs['Market History']); self.search_history_cards()
    MONITOR_TILES=('Index','1 day','7 days','30 days','Up / down 7d','At 30-day high','Significant Sharpe','Buy now')
    MONITOR_TILE_NAMES={'Index':'Market index','Up / down 7d':'Cards up / down 7 days','Significant Sharpe':'Steady risers','Buy now':'Under your max buy'}
    INDEX_MODES=('Every card counts equally','Pricier cards count more')
    def _mini_table(self,parent,col,title,cols):
        box=ttk.LabelFrame(parent,text=title,padding=4); box.grid(row=0,column=col,sticky='nsew',padx=(0 if col==0 else 6,0))
        tree=self.gridview(box,cols,7)
        tree.column('ID',width=0,minwidth=0,stretch=False); tree.column('Card',width=190,minwidth=120,stretch=True)
        for c in cols[2:]: tree.column(c,width=88 if c=='Trading days' else 66,minwidth=50,stretch=False,anchor='e')
        tree.bind('<Double-1>',lambda _e,t=tree:self.open_ranked_history(t))
        return tree
    def _put_tile(self,tiles,key,text,tone=None):
        var,label=tiles[key]; var.set(text)
        label.configure(fg={'up':'#5fd38d','down':'#ff7b7b'}.get(tone,self.colors['light']))
    def populate_overview(self):
        data=self.ranking_data; rows=data.get('fresh') or []
        if 'diagnostics' not in data: return
        pct=lambda v: '—' if v is None else f'{v:+.1f}%'
        tone=lambda v: None if v is None or abs(v)<0.05 else ('up' if v>0 else 'down')
        mode='ew' if self.index_mode.get()==self.INDEX_MODES[0] else 'pw'
        indices=data.get('indices') or {}; breadth=market_breadth(rows); annotated=self._annotations_current()
        for game in SUPPORTED_GAMES:
            s=index_summary(indices.get(game)); b=breadth.get(game,{}); put=lambda k,t,tn=None: self._put_tile(self.monitor_tiles,(game,k),t,tn)
            put('Index','—' if not s else f'{s[mode]:.1f}')
            for days,key in ((1,'1 day'),(7,'7 days'),(30,'30 days')):
                v=s[f'{mode}_{days}d'] if s else None; put(key,pct(v),tone(v))
            up,down=b.get('up_7d',0),b.get('down_7d',0)
            put('Up / down 7d',f'{up:,} / {down:,}' if b else '—','up' if up>down else 'down' if down>up else None)
            put('At 30-day high',f"{b.get('at_high',0):,}" if b else '—')
            put('Significant Sharpe',f"{b.get('significant',0):,}" if b else '—')
            put('Buy now',f"{b.get('buyable',0):,}" if b and annotated else '…' if b else '—')
        gainers,losers=market_movers(rows)
        for tree,items in ((self.gainers_tree,gainers),(self.losers_tree,losers)):
            self.clear(tree)
            for r in items:
                tree.insert('','end',values=(f"{r['card_id']}#{r['price_type']}",r['name'],money(r['latest_price']),pct(r['return_7d']),
                                             r.get('price_changes_30d')),tags=(tone(r['return_7d']) or '',))
        self.clear(self.blotter_tree)
        if annotated:
            for r in buy_list(rows,'Expected profit buying now ($/copy)',price_min=RANK_MIN_PRICE,min_changes=6,buyable_only=True,limit=25):
                self.blotter_tree.insert('','end',values=(f"{r['card_id']}#{r['price_type']}",r['name'],money(r.get('low_price')),
                    r.get('low_cond') or 'NM',money(r.get('exp_profit_low')),'—' if r.get('qty') is None else r['qty']),tags=('up',))
        dates=[r['latest_date'] for r in rows if r.get('latest_date')]
        latest=max(dates) if dates else None
        self.monitor_note.set(f"Prices as of {latest or '—'} · {len(rows):,} priced printings · "
                              f"{'buy/sell prices ready' if annotated else 'buy/sell prices pending forecast'}")
        self._draw_index_chart(); self.populate_alerts()
    def _draw_index_chart(self):
        canvas=self.index_chart; canvas.delete('all'); self._idx_hover=None
        width=max(300,canvas.winfo_width()); height=max(140,canvas.winfo_height())
        left,right,top,bottom=58,width-130,16,height-26
        indices=(self.ranking_data or {}).get('indices') or {}
        col=1 if self.index_mode.get()==self.INDEX_MODES[0] else 2
        span=int(self.index_range.get().split()[0])
        series={}
        for game,rows in indices.items():
            if not rows: continue
            start=(date.fromisoformat(rows[-1][0])-timedelta(days=span)).isoformat()
            pts=[(row[0],row[col]) for row in rows if row[0]>=start]
            if len(pts)>=2: series[game]=[(d,v/pts[0][1]*100) for d,v in pts]
        if not series:
            canvas.create_text(width/2,height/2,fill=self.colors['muted'],font=('Helvetica',11),
                               text='Market indices appear once two consecutive days of prices are ranked')
            return
        days=sorted({d for pts in series.values() for d,_ in pts}); pos={d:i for i,d in enumerate(days)}
        vals=[v for pts in series.values() for _,v in pts]; lo,hi=min(vals+[100.0]),max(vals+[100.0])
        pad=(hi-lo)*0.1 or 1.0; lo,hi=lo-pad,hi+pad
        x=lambda d: left+(right-left)*pos[d]/max(1,len(days)-1); y=lambda v: top+(bottom-top)*(hi-v)/(hi-lo)
        self._idx_hover={'days':days,'xs':[x(d) for d in days],'series':{g:dict(pts) for g,pts in series.items()},
                         'left':left,'right':right,'top':top,'bottom':bottom}
        muted='#95aac7'
        for k in range(5):
            value=hi-(hi-lo)*k/4; yy=y(value)
            canvas.create_line(left,yy,right,yy,fill='#22364f'); canvas.create_text(left-6,yy,anchor='e',fill=muted,text=f'{value:.1f}')
        canvas.create_line(left,y(100),right,y(100),fill='#3a5574',dash=(3,3))
        for i in sorted({round(k*(len(days)-1)/4) for k in range(5)}):
            canvas.create_text(x(days[i]),bottom+13,fill=muted,text=days[i][5:])
        colors={'MTG':self.colors['amber'],'Pokémon':'#5ca9ff'}; placed=[]
        for game,pts in sorted(series.items(),key=lambda kv:kv[1][-1][1]):
            color=colors.get(game,'#dbe7fa')
            canvas.create_line(*[c for d,v in pts for c in (x(d),y(v))],fill=color,width=2.2)
            label_y=y(pts[-1][1])
            if placed and abs(label_y-placed[-1])<15: label_y=placed[-1]-15
            placed.append(label_y)
            change=pts[-1][1]-100
            canvas.create_text(right+8,label_y,anchor='w',fill=color,font=('Helvetica',10,'bold'),
                               text=f'{game} {pts[-1][1]:.1f} ({change:+.1f}%)')
    def populate_alerts(self):
        if not hasattr(self,'alert_tree'): return
        self.clear(self.alert_tree); items=[]
        rows=self.ranking_data.get('fresh') or []
        dates=[r['latest_date'] for r in rows if r.get('latest_date')]
        if dates:
            age=(datetime.now(timezone.utc).date()-date.fromisoformat(max(dates))).days
            if age>=2: items.append(('','DATA','Daily prices',f'Latest prices are {age} days old — type SYNC','warn'))
        for warning in data_health(self.store): items.append(('','DATA','Data health',warning,'warn'))
        for pos in self.portfolio_rows:
            r=self.row_index.get((pos['card_id'],pos.get('row_type') or pos['price_type'])) or {}
            if pos['qty'] and (r.get('reprint') or r.get('legal_change')):
                items.append((pos['id'],'RISK',pos['name'],'; '.join(row_notes({'reprint':r.get('reprint'),'legal_change':r.get('legal_change')})),'down'))
        market=[]  # market-wide notices go after your own alerts; several of one kind become one line
        try:
            since=(date.today()-timedelta(days=14)).isoformat()
            events=self.store.q('SELECT day,game,kind,subject,detail FROM market_events WHERE day>=? ORDER BY day DESC LIMIT 200',(since,))
            by_kind={}
            for day,game,kind,subject,detail in events: by_kind.setdefault(kind,[]).append((day,subject,detail))
            for kind,evs in by_kind.items():
                if len(evs)<=2:
                    market+=[('',kind.upper(),subject,f'{detail} (detected {day})','warn') for day,subject,detail in evs]
                else:
                    market.append(('',kind.upper(),f"{len(evs)}{'+' if len(events)>=200 else ''} in the last 14 days",f'latest: {evs[0][1]} — {evs[0][2]} (detected {evs[0][0]})',''))
        except sqlite3.Error: pass
        presell=[o for o in release_opportunities(rows,self.pricing) if o['action']=='PRE-SELL']
        if presell: items.append(('','PRE-SELL','New sets',f"{len(presell):,} presale/launch printings where similar new cards fell sharply — type CYCLE",'warn'))
        arb=sum(1 for r in rows if not r.get('flags') and any(n.startswith('ARB') for n in buylist_signals(r,self.pricing)))
        if arb: items.append(('','CK BUYLIST','Card Kingdom buylist',f'{arb:,} cards are listed for less than Card Kingdom pays in cash — sort Cards to Look For by CK buylist','up'))
        for pos in self.portfolio_rows:
            if pos['alerts']: items.append((pos['id'],'ALERT',pos['name'],f"market {money(pos['market'])} hit {', '.join(pos['alerts'])}",'warn'))
        for pos in self.portfolio_rows:
            if pos['signal'] in ('SELL','TRIM') and pos['qty']: items.append((pos['id'],{'TRIM':'SELL SOME'}.get(pos['signal'],pos['signal']),pos['name'],pos['detail'],'down'))
        for c in self.catalysts:
            if -7<=c['days']<=21:
                when='today' if c['days']==0 else f"in {plural(c['days'],'day')}" if c['days']>0 else f"{plural(-c['days'],'day')} ago"
                stats=self.set_stats.get((c['game'],c['set_code']))
                move='' if not stats or stats.get('change_7d') is None else f" · set's cards {stats['change_7d']:+.1f}% this week"
                items.append((f"set:{c['game']}:{c['set_code']}",'RELEASE',f"{c['set_name']} ({c['game']})",f"{c['released_on']} ({when}){move}",
                              'up' if c['days']>=0 else ''))
        first=('DATA','ALERT','SELL','SELL SOME','RISK')  # your own cards and data problems first
        items=sorted(items,key=lambda it:first.index(it[1]) if it[1] in first else len(first))+market
        for iid,kind,item,detail,tag in items:
            self.alert_tree.insert('','end',values=(iid,kind,item,detail),tags=(tag,))
        if not items:
            self.alert_tree.insert('','end',values=('','—','No alerts','Set price alerts and positions in Portfolio; releases come from Sets & Catalysts'))
    def open_daily_brief(self):
        """Write the brief from what is on screen now and open it in the browser."""
        if 'diagnostics' not in self.ranking_data:
            messagebox.showinfo(APP,'Rankings are still loading; try again in a moment.'); return
        html=daily_brief_html(self.ranking_data,self.forecast_model,self.pricing,self.portfolio_rows,self.catalysts,self.set_name_map,
                              health=data_health(self.store))
        path=brief_path(); path.write_text(html,encoding='utf-8')
        self.status.set(f'Daily brief written to {path}')
        try:
            if sys.platform.startswith('win'): os.startfile(str(path))
            elif sys.platform=='darwin': subprocess.Popen(['open',str(path)])
            else: subprocess.Popen(['xdg-open',str(path)])
        except OSError as exc: messagebox.showinfo(APP,f'Brief saved to {path} ({exc})')
    @staticmethod
    def _descendants(widget):
        for child in widget.winfo_children():
            yield child; yield from Terminal._descendants(child)

    def explain(self,name):
        """Explain a column heading in the status bar and open the glossary at it."""
        hit=glossary_lookup(name)
        if hit: self.status.set(f'{hit[0]}: {hit[1]}')
        self.show_glossary(name)

    def show_glossary(self,query=''):
        win=getattr(self,'_glossary_win',None)
        if not (win and win.winfo_exists()):
            win=self._glossary_win=tk.Toplevel(self); win.title('Glossary'); win.configure(bg=self.colors['bg']); win.geometry('820x640')
            top=ttk.Frame(win,padding=10); top.pack(fill='x')
            ttk.Label(top,text='Search').pack(side='left',padx=(0,6))
            self._gloss_q=tk.StringVar(); entry=ttk.Entry(top,textvariable=self._gloss_q,width=40); entry.pack(side='left')
            self._gloss_q.trace_add('write',lambda *_a:self._fill_glossary())
            self._gloss_text=tk.Text(win,wrap='word',bg='#0b1726',fg='#dbe7fa',font=('Helvetica',11),padx=12,pady=8,relief='flat')
            self._gloss_text.pack(fill='both',expand=True,padx=10,pady=(0,10))
            self._gloss_text.tag_configure('term',foreground=self.colors['amber'],font=('Helvetica',12,'bold'))
            entry.focus_set()
        hit=glossary_lookup(query) if query else None
        self._gloss_q.set(hit[0] if hit else (query or '')); self._fill_glossary(); win.lift()

    def _fill_glossary(self):
        q=_gloss_key(self._gloss_q.get()); t=self._gloss_text; t.configure(state='normal'); t.delete('1.0','end')
        shown=0
        def rank(g):  # the term itself first, then its other names, then entries that only mention it
            term,aliases,meaning=g
            if not q: return (0,term.casefold())
            if _gloss_key(term)==q or q in {_gloss_key(x) for x in aliases}: return (0,term.casefold())
            if any(q in _gloss_key(n) for n in (term,*aliases)): return (1,term.casefold())
            return (2 if q in _gloss_key(meaning) else 3,term.casefold())
        for term,aliases,meaning in sorted(GLOSSARY,key=rank):
            if q and rank((term,aliases,meaning))[0]==3: continue
            t.insert('end',term,'term'); t.insert('end',(f"   (also: {', '.join(aliases)})" if aliases else '')+'\n'+meaning+'\n\n'); shown+=1
        if not shown: t.insert('end','Nothing matches; try a shorter word.')
        t.configure(state='disabled')

    def _crosshair_label(self,canvas,x,y,text,left,right):
        anchor='w' if x<(left+right)/2 else 'e'
        item=canvas.create_text(x+10 if anchor=='w' else x-10,y,anchor=anchor,fill='#ffffff',font=('Consolas',10,'bold'),text=text,tags='hover')
        x0,y0,x1,y1=canvas.bbox(item)
        canvas.tag_lower(canvas.create_rectangle(x0-5,y0-3,x1+5,y1+3,fill='#22364f',outline='#ffb000',tags='hover'),item)
    def _history_hover(self,event):
        canvas=self.history_chart; canvas.delete('hover'); h=getattr(self,'_hist_hover',None)
        if not h or not h['xs'] or not h['left']-4<=event.x<=h['right']+4: return
        i=bisect.bisect_left(h['xs'],event.x)
        if i>=len(h['xs']) or (i>0 and event.x-h['xs'][i-1]<h['xs'][i]-event.x): i=max(0,i-1)
        x,y=h['xs'][i],h['ys'][i]; day,price=h['points'][i]; first=h['points'][0][1]
        canvas.create_line(x,h['top'],x,h['bottom'],fill='#4d6a8c',dash=(2,2),tags='hover')
        canvas.create_oval(x-5,y-5,x+5,y+5,outline=self.colors['amber'],width=2,tags='hover')
        prev=h['points'][i-1][1] if i else None
        text=f"{day}  {money(price)}"+(f"  {(price/prev-1)*100:+.1f}% since the day before" if prev else '')+f"  {(price/first-1)*100:+.1f}% since {h['points'][0][0]}"
        self._crosshair_label(canvas,x,max(h['top']+10,y-22),text,h['left'],h['right'])
    def _index_hover(self,event):
        canvas=self.index_chart; canvas.delete('hover'); h=getattr(self,'_idx_hover',None)
        if not h or not h['xs'] or not h['left']-4<=event.x<=h['right']+4: return
        i=min(range(len(h['xs'])),key=lambda k:abs(h['xs'][k]-event.x)); day=h['days'][i]; x=h['xs'][i]
        canvas.create_line(x,h['top'],x,h['bottom'],fill='#4d6a8c',dash=(2,2),tags='hover')
        parts=[day]
        for game,values in h['series'].items():
            if day in values: parts.append(f'{game} {values[day]:.2f}')
        self._crosshair_label(canvas,x,h['top']+12,'  '.join(parts),h['left'],h['right'])
    def _open_alert(self):
        selected=self.alert_tree.selection()
        if not selected: return
        iid=str(self.alert_tree.item(selected[0],'values')[0])
        if iid.startswith('set:'):
            _,game,code=iid.split(':',2); self.show_set_cards(game,code)
        elif iid: self.open_ranked_history(self.alert_tree)
    def portfolio_tab(self):
        p=self.tabs['Portfolio']
        self.section(p,'Portfolio & watchlist','Printings you hold or watch (quantity 0 = watch only). Values are after your selling fee and per-card cost. '
                     'Signals compare a quick sale now (just under the cheapest listing) with the forecast at your horizon. Double-click a row to chart it.')
        bar=ttk.Frame(p); bar.pack(fill='x')
        ttk.Button(bar,text='Edit position & alerts…',command=self.edit_position).pack(side='left')
        ttk.Button(bar,text='Log a buy…',command=lambda:self.log_trade('BUY')).pack(side='left',padx=(8,0))
        ttk.Button(bar,text='Log a sale…',command=lambda:self.log_trade('SELL')).pack(side='left',padx=(8,0))
        ttk.Button(bar,text='Remove selected',command=self.remove_position).pack(side='left',padx=8)
        ttk.Button(bar,text='Export CSV',command=self.export_portfolio).pack(side='left')
        ttk.Button(bar,text='Refresh',command=self.load_portfolio).pack(side='left',padx=8)
        self.portfolio_summary=tk.StringVar(value='')
        ttk.Label(p,textvariable=self.portfolio_summary,font=('Helvetica',12,'bold')).pack(anchor='w',pady=(8,0))
        cols=('ID','Card','Game','Qty','Avg cost','Market','Low','7d %','30d %','Worth if sold','Profit if sold','Chance of rise','Signal','Alerts','Detail')
        self.portfolio_tree=self.gridview(p,cols,16)
        self.portfolio_tree.column('ID',width=0,minwidth=0,stretch=False)
        for col,width in (('Card',210),('Game',55),('Qty',45),('Avg cost',70),('Market',65),('Low',65),('7d %',55),('30d %',55),
                          ('Worth if sold',95),('Profit if sold',95),('Chance of rise',100),('Signal',80),('Alerts',90),('Detail',420)):
            self.portfolio_tree.column(col,width=width,minwidth=40,stretch=(col=='Detail'))
        self.portfolio_tree.bind('<Double-1>',lambda _e:self.open_ranked_history(self.portfolio_tree))
        self.portfolio_detail=tk.StringVar(value='Click a row to read its full advice here; double-click to chart it.')
        ttk.Label(p,textvariable=self.portfolio_detail,wraplength=1350,justify='left').pack(anchor='w')
        self.portfolio_tree.bind('<<TreeviewSelect>>',lambda _e:self._show_portfolio_detail())
    def _show_portfolio_detail(self):
        sel=self.portfolio_tree.selection()
        if not sel: return
        v=self.portfolio_tree.item(sel[0],'values')
        if v: self.portfolio_detail.set(f"{v[1]}: {v[12]} — {v[14] or 'watch only'}")
    def load_portfolio(self):
        if not hasattr(self,'portfolio_tree'): return
        self.clear(self.portfolio_tree)
        out=compute_positions(self.store,self.row_index,self.rows_by_card,self.forecast_model,self.pricing)
        self.portfolio_rows=out
        held=[r for r in out if r['qty']]
        cost=sum((r['cost'] or 0)*r['qty'] for r in held); value=sum(r['value'] or 0 for r in held)
        pct=lambda v: '—' if v is None else f'{v:+.1f}%'
        signed=lambda v: '—' if v is None else (money(v) if v>=0 else '−'+money(-v))
        for row in out:
            tag='warn' if row['alerts'] else 'down' if row['signal'] in ('SELL','TRIM') and row['qty'] else 'up' if (row['pnl'] or 0)>0 else ''
            limits=' / '.join(x for x in (f"≥{money(row['alert_above'])}" if row['alert_above'] else '',
                                          f"≤{money(row['alert_below'])}" if row['alert_below'] else '') if x)
            self.portfolio_tree.insert('','end',tags=(tag,),values=(row['id'],row['name'],row['game'],row['qty'] or 'watch',
                money(row['cost']),money(row['market']),money(row['low']),pct(row['return_7d']),pct(row['return_30d']),
                money(row['value']) if row['qty'] else '—',signed(row['pnl']),
                '—' if row['p_rise'] is None else f"{row['p_rise']*100:.0f}%",
                {'TRIM':'SELL SOME'}.get(row['signal'],row['signal']) if row['qty'] else '—',
                ('HIT '+', '.join(row['alerts'])) if row['alerts'] else limits or '—',row['detail'] if row['qty'] else ''))
        if not out:
            self.portfolio_summary.set('Your portfolio is empty.')
            self.portfolio_detail.set('To add a card: on Today, check it and click "I bought it…"; or select it in Cards to Look For and click '
                                      '"Add selected to portfolio"; or open its chart in Market History and click "Add to portfolio". '
                                      'Quantity 0 makes it a watchlist card, so you can set price alerts without owning it.')
            self.populate_alerts()
            if hasattr(self,'model_note'): self._start_annotation()
            return
        self.portfolio_summary.set(f"{len(out):,} printings · {sum(r['qty'] for r in held):,} copies held · cost {money(cost)} · "
                                   f"worth if sold now {money(value)} · profit if sold {signed(value-cost)} · "
                                   f"{sum(1 for r in held if r['signal'] in ('SELL','TRIM'))} to sell · "
                                   f"{sum(1 for r in out if r['alerts'])} alert(s) triggered")
        self.populate_alerts()
        if hasattr(self,'model_note'): self._start_annotation()  # suggested quantities depend on what you hold
    def add_to_portfolio(self,cid,price_type):
        if not cid: return
        self.store.execute('INSERT OR IGNORE INTO portfolio(card_id,price_type,qty,added_at) VALUES(?,?,0,?)',(cid,price_type or '',utc()))
        name=next((n for (n,) in self.store.q('SELECT name FROM cards WHERE id=?',(cid,))),cid)
        self.load_portfolio(); self.status.set(f'Added {name} {price_type.partition("_")[2] if price_type else ""} to Portfolio (set quantity, cost and alerts with Edit position)')
    def add_selected_to_portfolio(self,trees=None):
        for tree in trees or (self.sharpe_tree,self.opportunity_tree):
            selected=tree.selection()
            if selected:
                values=tree.item(selected[0],'values')
                if values:
                    cid,_,price_type=str(values[0]).partition('#'); self.add_to_portfolio(cid,price_type); return
        messagebox.showinfo(APP,'Select a card in the table first.')
    def add_history_to_portfolio(self):
        cid=self.history_id.get().strip()
        if not cid: messagebox.showinfo(APP,'Load a card first.'); return
        printing=self.history_printing.get()
        self.add_to_portfolio(cid,'market_'+printing if printing else '')
    def _selected_position(self):
        selected=self.portfolio_tree.selection()
        if not selected:
            messagebox.showinfo(APP,'Select a row in the portfolio first.'); return None
        iid=str(self.portfolio_tree.item(selected[0],'values')[0])
        return next((r for r in self.portfolio_rows if r['id']==iid),None)
    def edit_position(self):
        pos=self._selected_position()
        if not pos: return
        dlg=tk.Toplevel(self); dlg.title('Position & alerts'); dlg.configure(bg=self.colors['bg']); dlg.transient(self)
        frame=ttk.Frame(dlg,padding=16); frame.pack(fill='both',expand=True)
        ttk.Label(frame,text=pos['name'],font=('Helvetica',13,'bold')).grid(row=0,column=0,columnspan=2,sticky='w',pady=(0,10))
        fmt=lambda v: '' if v is None else f'{v:g}'
        fields=(('Quantity held (0 = watch only)','qty',str(pos['qty'] or 0)),('Average cost per copy $','cost',fmt(pos['cost'])),
                ('Alert when market ≥ $','above',fmt(pos['alert_above'])),('Alert when market ≤ $','below',fmt(pos['alert_below'])))
        values={}
        for i,(label,key,default) in enumerate(fields,1):
            ttk.Label(frame,text=label).grid(row=i,column=0,sticky='w',pady=3,padx=(0,10))
            values[key]=tk.StringVar(value=default); ttk.Entry(frame,textvariable=values[key],width=12).grid(row=i,column=1,sticky='w')
        def save():
            try:
                qty=int(values['qty'].get().strip() or 0)
                if qty<0: raise ValueError
                nums={k:parse_filter_value(values[k].get()) for k in ('cost','above','below')}
                if any(v is not None and v<0 for v in nums.values()): raise ValueError
            except ValueError:
                messagebox.showerror(APP,'Please fix: quantity must be a whole number (0 or more); prices must be dollar amounts such as 12.50, or blank.',parent=dlg); return
            if nums['above'] is not None and nums['below'] is not None and nums['above']<=nums['below']:
                messagebox.showerror(APP,'The "≥" alert should be higher than the "≤" alert (for example: alert at ≥ $30 to sell, ≤ $20 to buy more).',parent=dlg); return
            self.store.execute('UPDATE portfolio SET qty=?,cost=?,alert_above=?,alert_below=? WHERE card_id=? AND price_type=?',
                               (qty,nums['cost'],nums['above'],nums['below'],pos['card_id'],pos['price_type']))
            dlg.destroy(); self.load_portfolio()
        ttk.Label(frame,text='Alerts show on the Today list and in the daily brief: use ≥ for "time to sell", ≤ for "cheap enough to buy". Leave blank for none.',
                  style='Small.TLabel',wraplength=380,justify='left').grid(row=len(fields)+1,column=0,columnspan=2,sticky='w',pady=(8,0))
        buttons=ttk.Frame(frame); buttons.grid(row=len(fields)+2,column=0,columnspan=2,sticky='e',pady=(12,0))
        ttk.Button(buttons,text='Save',command=save).pack(side='right'); ttk.Button(buttons,text='Cancel',command=dlg.destroy).pack(side='right',padx=8)
        dlg.bind('<Return>',lambda _e:save()); dlg.grab_set()
    def remove_position(self):
        pos=self._selected_position()
        if pos and messagebox.askyesno(APP,f"Remove {pos['name']} from your portfolio? Its quantity, average cost and alerts are deleted "
                                           "(your logged trades stay in Backtest & Trades)."):
            self.store.execute('DELETE FROM portfolio WHERE card_id=? AND price_type=?',(pos['card_id'],pos['price_type'])); self.load_portfolio()
    def export_portfolio(self):
        if not self.portfolio_rows: messagebox.showinfo(APP,'The portfolio is empty.'); return
        self.save_csv(['card_id','printing','name','game','qty','avg_cost','market','lowest_listing','return_7d_pct','return_30d_pct',
                       'worth_if_sold','profit_if_sold','chance_rise','signal','alerts','detail'],
                      [(r['card_id'],r['price_type'],r['name'],r['game'],r['qty'],r['cost'],r['market'],r['low'],r['return_7d'],r['return_30d'],
                        r['value'],r['pnl'],r['p_rise'],{'TRIM':'SELL SOME'}.get(r['signal'],r['signal']),'; '.join(r['alerts']),r['detail'])
                       for r in self.portfolio_rows],'portfolio.csv')
    BT_COLORS=('#ffb000','#5ca9ff','#5fd38d','#ff7b7b')
    def backtest_tab(self):
        p=self.tabs['Backtest & Trades']
        self.section(p,'Strategy backtest & your trades',
            'A test of the app\'s advice on past prices: as if you had followed it every day, using only what was known on that day, '
            'buying one Near Mint copy each time and selling it at your horizon after every fee and both shipping costs. '
            '"Promised win" is what the app predicted; "Win rate" is what actually happened. Below, log your real buys and sales: '
            'the app shows your actual profit, compares it with what it predicted, and learns your real condition prices, fees and shipping.')
        bar=ttk.Frame(p); bar.pack(fill='x')
        ttk.Button(bar,text='Run backtest now',command=self.run_backtest).pack(side='left')
        self.backtest_note=tk.StringVar(value='The backtest runs with the daily precompute, or now with the button.')
        ttk.Label(bar,textvariable=self.backtest_note,style='Small.TLabel',wraplength=1200).pack(side='left',padx=10)
        self.backtest_plain=tk.StringVar(value='')
        ttk.Label(p,textvariable=self.backtest_plain,wraplength=1400,justify='left',font=('Helvetica',11,'bold')).pack(anchor='w',pady=(0,4))
        top=ttk.Frame(p); top.pack(fill='x')
        self.bt_tree=self.gridview(top,('Strategy','Trades','Win rate (90% range)','Promised win','Avg P/L per copy','ROI','Total P/L (1 each)','Worst drawdown'),4)
        for col,width in (('Strategy',300),('Trades',70),('Win rate (90% range)',140),('Promised win',95),('Avg P/L per copy',110),
                          ('ROI',70),('Total P/L (1 each)',120),('Worst drawdown',110)):
            self.bt_tree.column(col,width=width,minwidth=50,stretch=(col=='Strategy'))
        self.bt_chart=tk.Canvas(p,height=170,bg='#0b1726',highlightthickness=1,highlightbackground='#253b57')
        self.bt_chart.pack(fill='x',pady=(0,6)); self.bt_chart.bind('<Configure>',lambda _e:self._draw_backtest_chart())
        tbar=ttk.Frame(p); tbar.pack(fill='x')
        ttk.Label(tbar,text='Your trades',font=('Helvetica',12,'bold')).pack(side='left',padx=(0,12))
        ttk.Button(tbar,text='Log a buy…',command=lambda:self.log_trade('BUY')).pack(side='left')
        ttk.Button(tbar,text='Log a sale…',command=lambda:self.log_trade('SELL')).pack(side='left',padx=8)
        ttk.Button(tbar,text='Delete selected trade',command=self.delete_trade).pack(side='left')
        ttk.Button(tbar,text='Apply learned settings',command=self.apply_learned_settings).pack(side='left',padx=8)
        ttk.Button(tbar,text='Export trades CSV',command=self.export_trades).pack(side='left')
        self.trade_summary=tk.StringVar(value=''); self.trade_learned=tk.StringVar(value='')
        ttk.Label(p,textvariable=self.trade_summary,font=('Helvetica',11,'bold'),wraplength=1350).pack(anchor='w',pady=(4,0))
        ttk.Label(p,textvariable=self.trade_learned,style='Small.TLabel',wraplength=1350).pack(anchor='w')
        self.trade_tree=self.gridview(p,('ID','Date','Side','Card','Cond','Qty','Price','Fees','Shipping','Market then','Predicted profit','Actual profit','Note'),8)
        self.trade_tree.column('ID',width=0,minwidth=0,stretch=False)
        for col,width in (('Date',85),('Side',45),('Card',250),('Cond',45),('Qty',40),('Price',70),('Fees',60),('Shipping',65),
                          ('Market then',85),('Predicted profit',100),('Actual profit',95),('Note',200)):
            self.trade_tree.column(col,width=width,minwidth=40,stretch=(col=='Note'))
        self.backtest=None; self.backtest_busy=False; self.trade_rows=[]; self.learned={}
        self.load_trades()

    def today_tab(self):
        p=self.tabs['Today']
        ttk.Label(p,text='What to do today',font=('Helvetica',16,'bold')).pack(anchor='w')
        ttk.Label(p,text='Check any card before you buy or sell it, then work down the to-do list. Prices already include selling fees, '
                         'shipping both ways and supplies (set your own platform\'s fees in Settings). Estimates from past prices, not guarantees.',
                  style='Small.TLabel',wraplength=1350).pack(anchor='w',pady=(0,6))
        box=ttk.LabelFrame(p,text=' CHECK A CARD ',padding=10); box.pack(fill='x')
        row=ttk.Frame(box); row.pack(fill='x')
        self.today_game=tk.StringVar(value='All')
        ttk.Label(row,text='Game').pack(side='left',padx=(0,6))
        game_box=ttk.Combobox(row,textvariable=self.today_game,values=['All',*SUPPORTED_GAMES],state='readonly',width=11)
        game_box.pack(side='left',padx=(0,12))
        game_box.bind('<<ComboboxSelected>>',lambda _e:(self.populate_today(),self.check_name.get().strip() and self._check_search()))
        ttk.Label(row,text='Card name').pack(side='left',padx=(0,6))
        self.check_name=tk.StringVar(); name=ttk.Entry(row,textvariable=self.check_name,width=30,font=('Helvetica',12)); name.pack(side='left')
        name.bind('<Return>',lambda _e:self._check_search())
        ttk.Button(row,text='Find',command=self._check_search).pack(side='left',padx=(6,12))
        self.check_pick=tk.StringVar(); self.check_combo=ttk.Combobox(row,textvariable=self.check_pick,state='readonly',width=58)
        self.check_combo.pack(side='left',padx=(0,12)); self.check_combo.bind('<<ComboboxSelected>>',lambda _e:self._check_picked())
        row2=ttk.Frame(box); row2.pack(fill='x',pady=(8,0))
        ttk.Label(row2,text='Condition').pack(side='left',padx=(0,6))
        self.check_cond=tk.StringVar(value='NM')
        ttk.Combobox(row2,textvariable=self.check_cond,values=list(CONDITIONS),state='readonly',width=5).pack(side='left',padx=(0,16))
        ttk.Label(row2,text='Price $').pack(side='left',padx=(0,6))
        self.check_price=tk.StringVar(); price=ttk.Entry(row2,textvariable=self.check_price,width=10,font=('Helvetica',12)); price.pack(side='left',padx=(0,16))
        price.bind('<Return>',lambda _e:self.check_card('buy'))
        ttk.Button(row2,text='Should I BUY at this price?',command=lambda:self.check_card('buy')).pack(side='left',padx=(0,8))
        ttk.Button(row2,text='What should I SELL it for?',command=lambda:self.check_card('sell')).pack(side='left',padx=(0,8))
        row3=ttk.Frame(box); row3.pack(fill='x',pady=(6,0))
        ttk.Button(row3,text='Open chart',command=self._check_chart).pack(side='left',padx=(0,8))
        ttk.Button(row3,text='Long-term history',command=self._check_longterm).pack(side='left',padx=(0,8))
        ttk.Button(row3,text='I bought it…',command=lambda:self._check_log('BUY')).pack(side='left',padx=(0,8))
        ttk.Button(row3,text='I sold it…',command=lambda:self._check_log('SELL')).pack(side='left')
        ttk.Label(box,text='For selling, the price box is optional (what you paid). Logging a buy or sale updates your Portfolio and teaches the app your real prices.',
                  style='Small.TLabel').pack(anchor='w',pady=(4,0))
        self.check_headline=tk.StringVar(value='Type a card name and press Enter.')
        self.check_head_label=ttk.Label(box,textvariable=self.check_headline,font=('Helvetica',15,'bold'),wraplength=1350)
        self.check_head_label.pack(anchor='w',pady=(10,2))
        self.check_details=tk.StringVar(value='')
        ttk.Label(box,textvariable=self.check_details,font=('Helvetica',11),wraplength=1350,justify='left').pack(anchor='w')
        self.check_matches=[]
        self.first_run=ttk.LabelFrame(p,text=' GETTING STARTED ',padding=10)
        ttk.Label(self.first_run,text='No prices are stored on this computer yet. Download them once (about 10–20 minutes the first time; '
                                      'later days take a minute or two). Then turn on daily updates so the app keeps learning while it is closed. '
                                      'Buy ideas appear after about a month of daily prices; selling advice and the card checker work sooner.',
                  wraplength=1300,justify='left').pack(anchor='w')
        fr_row=ttk.Frame(self.first_run); fr_row.pack(anchor='w',pady=(8,0))
        ttk.Button(fr_row,text="1. Download today's prices",command=lambda:self.start_tcgcsv()).pack(side='left',padx=(0,8))
        if sys.platform.startswith('win'):
            ttk.Button(fr_row,text='2. Turn on daily updates',command=self.install_windows_task).pack(side='left',padx=(0,8))
        elif sys.platform=='darwin':
            ttk.Button(fr_row,text='2. Turn on daily updates',command=self.install_launch_agent).pack(side='left',padx=(0,8))
        ttk.Button(fr_row,text='3. Set my selling fees and shipping',command=lambda:self.nb.select(self.tabs['Settings'])).pack(side='left')
        self._first_run_anchor=ttk.Frame(p); self._first_run_anchor.pack(fill='x')
        self._update_first_run()
        head=ttk.Frame(p); head.pack(fill='x',pady=(10,0))
        ttk.Label(head,text="Today's to-do list",font=('Helvetica',14,'bold')).pack(side='left')
        self.today_note=tk.StringVar(value="Loading today's list — this takes a few seconds (up to a minute right after new prices arrive)…")
        ttk.Label(p,textvariable=self.today_note,style='Small.TLabel',wraplength=1350,justify='left').pack(anchor='w')
        self.today_tree=self.gridview(p,('ID','Do this','Card','Price','Qty','Why','Confidence'),14)
        self.today_tree.column('ID',width=0,minwidth=0,stretch=False)
        for col,width in (('Do this',165),('Card',300),('Price',80),('Qty',45),('Why',680),('Confidence',90)):
            self.today_tree.column(col,width=width,minwidth=40,stretch=(col=='Why'))
        self.today_tree.bind('<Double-1>',lambda _e:self._today_open())
        ttk.Label(p,text='Confidence: High = past results say this works out at least 80% of the time · Medium = 65–80% · '
                         'Low = less than that, or too little data to say. Double-click any row for the full check.',style='Small.TLabel').pack(anchor='w')

    def _update_first_run(self):
        if not hasattr(self,'first_run'): return
        try: empty=not self.store.q('SELECT 1 FROM daily LIMIT 1')
        except Exception: empty=False
        if empty and not self.first_run.winfo_ismapped(): self.first_run.pack(fill='x',pady=(10,0),before=self._first_run_anchor)
        elif not empty and self.first_run.winfo_manager(): self.first_run.pack_forget()

    def populate_today(self):
        self._update_first_run()
        if not hasattr(self,'today_tree') or not self._annotations_current(): return
        self.clear(self.today_tree)
        game=self.today_game.get()
        rows=[r for r in self.ranking_data.get('fresh') or [] if game=='All' or r.get('game')==game]
        positions=[p for p in self.portfolio_rows if game=='All' or p.get('game')==game]
        actions=todays_actions(rows,positions,self.pricing)
        tags={'SELL':'down','SELL SOME':'down','BUNDLE':'warn','SELL NOW':'down','PRE-SELL':'warn','CHECK':'warn','BUY NOW':'up','BUY → SELL TO CK':'up','TRADE-IN PRICE':'',
              'LONG-TERM BUY':'up'}
        for a in actions:
            self.today_tree.insert('','end',tags=(tags.get(a['action'],''),),values=(a['id'],a['action'],a['name'],money(a['price']),
                                   '—' if a['qty'] is None else a['qty'],a['why'],a['confidence']))
        dates=[r['latest_date'] for r in self.ranking_data.get('fresh') or [] if r.get('latest_date')]
        counts={}
        for a in actions: counts[a['action']]=counts.get(a['action'],0)+1
        young=[]
        for game in SUPPORTED_GAMES:
            days=[r.get('observations') or 0 for r in self.ranking_data.get('fresh') or [] if r.get('game')==game]
            if days and _median(days)<HISTORY_READY_DAYS: young.append(f'{game} {_median(days):.0f}')
        stale=''
        if dates:
            try:
                age=(date.today()-date.fromisoformat(str(max(dates))[:10])).days
                if age>=3: stale=f"⚠ PRICES ARE {age} DAYS OLD — type SYNC in the command box to update now, and check that daily updates are ON in Settings · "
            except ValueError: pass
        self.today_note.set(stale+f"prices as of {max(dates) if dates else '—'} · "+(' · '.join(f'{n} {k.lower()}' for k,n in counts.items()) or 'nothing to do today')+
                            ' · double-click a row to check it'+
                            (f" · history so far (days of {HISTORY_READY_DAYS} needed): "+', '.join(young)+' — buy ideas start once a game reaches it' if young else ''))

    def _today_open(self):
        sel=self.today_tree.selection()
        if not sel: return
        rid=str(self.today_tree.item(sel[0],'values')[0]); r=next((x for x in self.ranking_data.get('fresh') or [] if f"{x['card_id']}#{x['price_type']}"==rid),None)
        if not r: return
        self.check_matches=[r]; self.check_combo['values']=[self._check_label(r)]; self.check_pick.set(self._check_label(r)); self.check_name.set(r['card_name'])
        action=str(self.today_tree.item(sel[0],'values')[1])
        watch_only=action=='CHECK' and str(self.today_tree.item(sel[0],'values')[4])=='—'
        if action in ('SELL','SELL SOME','BUNDLE','SELL NOW','PRE-SELL','CHECK') and not watch_only:
            pos=next((x for x in self.portfolio_rows if x['id']==rid),None)
            self.check_price.set('' if not pos or pos.get('cost') is None else f"{pos['cost']:.2f}"); self.check_card('sell')
        else:
            self.check_price.set(f"{(r.get('low_price') if r.get('buyable') else r.get('max_buy')) or r['latest_price']:.2f}"); self.check_card('buy')

    @staticmethod
    def _check_label(r):
        return f"{r['name']} · {r.get('set_code') or ''} · {money(r['latest_price'])}"

    def _check_search(self):
        q=self.check_name.get().strip().casefold()
        if not q: return
        rows=self.ranking_data.get('fresh') or []
        game=self.today_game.get()
        hits=[r for r in rows if q in r['card_name'].casefold() and (game=='All' or r.get('game')==game)]
        hits.sort(key=lambda r:(r['card_name'].casefold()!=q,r.get('flags') and True or False,-(r.get('price_changes_30d') or 0),-(r['latest_price'] or 0)))
        self.check_matches=hits[:40]; self.check_combo['values']=[self._check_label(r) for r in self.check_matches]
        if not hits:
            known=self.store.q('SELECT name FROM cards WHERE name LIKE ? LIMIT 1',('%'+self.check_name.get().strip()+'%',))
            self.check_headline.set(f"{known[0][0]} is in the catalog but has no recent price to judge (it may rarely sell)." if known else
                                    'No card matches that name (try fewer words, or check the Game box).')
            self.check_details.set(''); return
        self.check_pick.set(self._check_label(hits[0])); self._check_picked()

    def _check_picked(self):
        r=self._check_row()
        if not r: return
        if not self.check_price.get().strip():
            self.check_price.set(f"{(r.get('low_price') or r['latest_price']):.2f}")
        self.check_headline.set(f"{r['name']} ({r.get('set_code') or ''}): market {money(r['latest_price'])}, cheapest listing {money(r.get('low_price'))}. "
                                "Enter a price, then choose BUY or SELL.")
        self.check_head_label.configure(foreground=self.colors['light']); self.check_details.set('')

    def _check_row(self):
        label=self.check_pick.get()
        return next((r for r in self.check_matches if self._check_label(r)==label),None)

    def _check_log(self,side):
        r=self._check_row()
        if not r: messagebox.showinfo(APP,'Find the card first (type its name and press Enter).'); return
        try: price=float(self.check_price.get().strip().replace('$','').replace(',',''))
        except ValueError: price=None
        self.log_trade(side,target=(r['card_id'],r['price_type'],r['name']),price=price,cond=self.check_cond.get())

    def _check_longterm(self):
        r=self._check_row()
        if not r: return
        if r.get('game') not in PC_GAME_PREFIX:
            self.check_details.set(self.check_details.get()+f"\n• No long-term history source covers {r.get('game')} yet; its history builds with your daily syncs."); return
        self.check_details.set(self.check_details.get()+'\n• Looking up long-term history on PriceCharting…')
        def worker():
            try: text=history_summary(pricecharting_history(self.store,r['card_id'])) or 'PriceCharting has no history for this card.'
            except Exception as exc: text=f'PriceCharting lookup failed: {exc}'
            self.events.put(('longterm',text))
        threading.Thread(target=worker,daemon=True).start()

    def _check_chart(self):
        r=self._check_row()
        if r:
            self.history_series=r['price_type']; self.history_id.set(r['card_id']); self.nb.select(self.tabs['Market History']); self.load_history()

    def check_card(self,mode):
        r=self._check_row()
        if not r:
            self._check_search(); r=self._check_row()
            if not r: return
        if not self.forecast_model:
            self.check_headline.set('The forecast is still loading; try again in a moment.'); return
        try: price=parse_filter_value(self.check_price.get())
        except ValueError: price=None
        if mode=='buy' and (price is None or price<=0):
            self.check_headline.set('Enter the price you would pay.'); return
        res=(decide_buy(r,self.forecast_model,self.pricing,self.check_cond.get(),price) if mode=='buy' else
             decide_sell(r,self.forecast_model,self.pricing,self.check_cond.get(),price))
        color={'YES':'#5fd38d','LIST HIGH':'#5fd38d','MAYBE':'#ffb000','SELL':'#ffb000','SELL NOW':'#ff7b7b','NO':'#ff7b7b',
               'NOT YET':'#ffb000'}.get(res['verdict'],self.colors['light'])
        self.check_head_label.configure(foreground=color); self.check_headline.set(res['headline'])
        self.check_details.set('\n'.join('• '+d for d in res['details']))

    def _load_card_facts(self):
        def worker():
            try:
                with ReadOnlyStore() as reader: self.events.put(('facts',mtg_card_facts(reader)))
            except Exception: pass
        threading.Thread(target=worker,daemon=True).start()

    def load_backtest_view(self):
        dates=[r['latest_date'] for r in self.ranking_data.get('fresh',[]) if r.get('latest_date')]
        self.backtest=load_backtest(max(dates) if dates else None,self.pricing); self.populate_backtest()

    def run_backtest(self):
        dates=[r['latest_date'] for r in self.ranking_data.get('fresh',[]) if r.get('latest_date')]
        if not dates: messagebox.showinfo(APP,'Rankings are still loading; try again in a moment.'); return
        if self.backtest_busy: return
        self.backtest_busy=True; pricing=dict(self.pricing); day=max(dates)
        self.backtest_plain.set(''); self.backtest_note.set('Replaying the buy rules on past prices…')
        def worker():
            try:
                ensure_daily_history(self.store)
                progress=lambda current,total,phase: self.events.put(('rank_progress',(current,total,phase)))
                with ReadOnlyStore() as reader: result=run_strategy_backtest(reader,pricing,day,progress)
                save_backtest(result); self.events.put(('backtest',result))
            except Exception as exc: self.events.put(('backtest',str(exc)))
        threading.Thread(target=worker,daemon=True).start()

    def populate_backtest(self):
        if not hasattr(self,'bt_tree'): return
        self.clear(self.bt_tree); bt=self.backtest
        if not bt:
            self.backtest_note.set('No backtest for today\'s data and your current assumptions yet. It is built by the daily precompute, '
                                   'or press Run backtest now (about a minute).'); self._draw_backtest_chart(); return
        pct=lambda v: '—' if v is None else f'{v*100:.0f}%'
        signed=lambda v: '—' if v is None else (money(v) if v>=0 else '−'+money(-v))
        for i,(name,r) in enumerate(bt['strategies'].items()):
            if not r:
                self.bt_tree.insert('','end',values=(name,0,'—','—','—','—','—','—')); continue
            ci=r.get('win_ci'); tag='up' if (r['roi'] or 0)>0 else 'down'
            self.bt_tree.insert('','end',tags=(tag,),values=(name,f"{r['trades']:,}",
                f"{pct(r['win_rate'])}"+(f" ({ci[0]*100:.0f}–{ci[1]*100:.0f})" if ci else ''),pct(r.get('pred_win')),
                signed(r['avg_pnl']),'—' if r['roi'] is None else f"{r['roi']*100:+.1f}%",signed(r['total_pnl']),signed(r['max_drawdown'])))
        span=bt.get('sell_days') or ['—','—']; pr=bt['pricing']
        self.backtest_note.set(f"{bt['horizon']}-day horizon, sales from {span[0]} to {span[1]}, built {bt['built_at'][:16].replace('T',' ')} UTC "
                               f"with {pr['fee_pct']:g}% + ${pr['fee_fixed']:.2f} fees, ${pr['ship_plain']:.2f}/${pr['ship_tracked']:.2f} shipping, "
                               f"${pr['ship_in']:.2f} inbound, {pr['win_pct']:g}% target win. Assumes each copy sells at the horizon market price "
                               "(a sale is not guaranteed) and is Near Mint. Win-rate ranges count overlapping windows once. "
                               "History is short (about 3 months for MTG; Pokémon starts with your daily syncs), so treat it as a sanity check."
                               +self._promise_text(bt))
        self.backtest_plain.set(self._backtest_plain(bt))
        self._draw_backtest_chart()

    @staticmethod
    def _backtest_plain(bt):
        st=bt.get('strategies') or {}
        mine=st.get('Buy-ins at Max buy · this model') or {}; base=st.get('Buy-ins at Max buy · no-skill forecast') or {}
        now=st.get('Buy now at cheapest listing · this model') or {}
        out=[]
        if mine.get('trades'):
            out.append(f"In plain words: paying no more than Max buy made money on {mine['win_rate']*100:.0f}% of past trades "
                       f"(about {money(mine['avg_pnl'])} per copy).")
            if base.get('avg_pnl') is not None and base['avg_pnl']>mine['avg_pnl']:
                out.append("The plain-average version did as well or better on this short history; the forecast is more cautious, "
                           "which should matter more when prices turn. Both are shown so you can judge.")
        if not now.get('trades'):
            out.append("Buy now at cheapest listing has no trades because no past listing was ever under Max buy on the test days — "
                       "the app would not have told you to buy at the listing price.")
        if (st.get('Buy every card at market · no model') or {}).get('roi',0)<0:
            out.append("Buying everything at market price lost money, which is why the app only buys under Max buy.")
        return ' '.join(out)

    @staticmethod
    def _promise_text(bt):
        mine=(bt.get('strategies') or {}).get('Buy-ins at Max buy · this model') or {}
        rows=mine.get('by_promise') or []
        if not rows: return ''
        return ('  Promised → realized chance of profit (if sold), by liquidity: '+
                ' · '.join(f'{r[0]}: {r[2]*100:.0f}% → {r[3]*100:.0f}% ({r[1]:,} trades'+(f', expected {money(r[4])} → realized {money(r[5])}/copy' if len(r)>4 else '')+')'
                           for r in rows)+'.')

    def _draw_backtest_chart(self):
        canvas=self.bt_chart; canvas.delete('all'); bt=self.backtest
        width=max(300,canvas.winfo_width()); height=max(120,canvas.winfo_height())
        left,right,top,bottom=80,width-20,40,height-24
        canvas.create_text(12,8,anchor='nw',fill='#dbe7fa',font=('Helvetica',10,'bold'),text='Cumulative P/L by sale date (one copy per signal)')
        series=[(name,r['curve']) for name,r in ((bt or {}).get('strategies') or {}).items() if r and r['curve'] and 'every card' not in name]
        if not series:
            canvas.create_text(width/2,height/2,fill='#95aac7',text='No backtest yet'); return
        days=sorted({d for _n,c in series for d,_v in c}); pos={d:i for i,d in enumerate(days)}
        vals=[v for _n,c in series for _d,v in c]+[0.0]; lo,hi=min(vals),max(vals)
        if hi-lo<1e-9: hi=lo+1
        x=lambda d: left+(right-left)*pos[d]/max(1,len(days)-1); y=lambda v: top+(bottom-top)*(hi-v)/(hi-lo)
        canvas.create_line(left,y(0),right,y(0),fill='#4d6a8c',dash=(3,3))
        for v in (lo,hi): canvas.create_text(left-6,y(v),anchor='e',fill='#95aac7',font=('Helvetica',9),text=money(v) if v>=0 else '−'+money(-v))
        for d in (days[0],days[-1]): canvas.create_text(x(d),bottom+12,fill='#95aac7',font=('Helvetica',9),text=d)
        for i,(name,curve) in enumerate(series):
            color=self.BT_COLORS[i%len(self.BT_COLORS)]
            coords=[c for d,v in curve for c in (x(d),y(v))]
            if len(coords)>=4: canvas.create_line(*coords,fill=color,width=2)
            canvas.create_text(left+10+300*i,24,anchor='nw',fill=color,font=('Helvetica',9),text=name)

    def load_trades(self):
        if not hasattr(self,'trade_tree'): return
        cols=('id','card_id','price_type','side','qty','price','condition','fees','shipping','traded_on','market','predicted_profit','predicted_win','note','changes')
        self.trade_rows=[dict(zip(cols,row)) for row in self.store.q(f"SELECT {','.join(cols)} FROM trades ORDER BY traded_on DESC,id DESC")]
        names=dict(self.store.q("SELECT id,name FROM cards WHERE id IN (SELECT card_id FROM trades)")) if self.trade_rows else {}
        ledger=trade_ledger(self.trade_rows); realized={}
        for sale in ledger['sales']: realized.setdefault((sale['card_id'],sale['price_type'],sale['traded_on']),[]).append(sale['pnl'])
        signed=lambda v: '—' if v is None else (money(v) if v>=0 else '−'+money(-v))
        self.clear(self.trade_tree)
        for t in self.trade_rows:
            pnl=sum(realized.get((t['card_id'],t['price_type'],t['traded_on']),[])) if t['side']=='SELL' else None
            pred=None if t['predicted_profit'] is None else t['predicted_profit']*t['qty']
            self.trade_tree.insert('','end',tags=('' if pnl is None else 'up' if pnl>0 else 'down',),values=(t['id'],t['traded_on'],t['side'],
                printing_label(names.get(t['card_id'],t['card_id']),t['price_type'] or RANK_PRICE_TYPE),t['condition'],t['qty'],money(t['price']),
                money(t['fees']),money(t['shipping']),money(t['market']),signed(pred),signed(pnl),t['note'] or ''))
        sales=ledger['sales']
        if sales:
            pnl=sum(x['pnl'] for x in sales); pred=sum(x['predicted'] for x in sales); wins=sum(1 for x in sales if x['pnl']>0)
            held=sum(x['days_held']*x['qty'] for x in sales)/sum(x['qty'] for x in sales)
            n=lambda k,word: f"{k:,} {word}{'' if k==1 else 's'}"
            still=sum(q for q,_c in ledger['open'].values())
            self.trade_summary.set(f"{n(len(self.trade_rows),'trade')} · {n(len(sales),'sale')} closed · profit on those sales {signed(pnl)} "
                                   f"(the app predicted {signed(pred)}) · {wins/len(sales)*100:.0f}% of sales made money · "
                                   f"held {held:.0f} days on average · {n(still,'copy') if still!=1 else '1 copy'} still unsold".replace('copys','copies'))
        else:
            self.trade_summary.set(f"{len(self.trade_rows):,} trades logged. Log buys and sales (Today, Portfolio or here) to see your actual profit "
                                   "and let the app learn your real condition prices, fees and shipping.")
        self.learned=learn_from_trades(self.trade_rows,self.pricing)
        labels=self.LEARNED_LABELS
        self.trade_learned.set('Learned from your trades (shrunk toward your current settings; Apply to use): '+
                               ' · '.join(f"{labels[k]} {v:g} ({n} trades; now {self.pricing[k]:g})" for k,(v,n) in self.learned.items())
                               if self.learned else 'Nothing learned yet: sales with a condition and recorded market price teach condition prices; '
                               'recorded fees and shipping teach costs.')

    def _trade_target(self,from_history=False):
        """(card_id, price_type, name) of the card to log: the Market History card, else the selected portfolio/trade row."""
        if not from_history:
            for tree in (getattr(self,'portfolio_tree',None),getattr(self,'trade_tree',None)):
                selected=tree.selection() if tree else ()
                if selected and tree is self.portfolio_tree:
                    pos=next((r for r in self.portfolio_rows if r['id']==str(tree.item(selected[0],'values')[0])),None)
                    if pos: return pos['card_id'],pos.get('row_type') or pos['price_type'],pos['name']
                if selected and tree is self.trade_tree:
                    t=next((r for r in self.trade_rows if str(r['id'])==str(tree.item(selected[0],'values')[0])),None)
                    if t: return t['card_id'],t['price_type'],t['card_id']
        cid=self.history_id.get().strip()
        if cid:
            printing=self.history_printing.get()
            return cid,('market_'+printing) if printing else RANK_PRICE_TYPE,self.history_title.get()
        return None

    def log_trade(self,side,from_history=False,target=None,price=None,cond=None):
        target=target or self._trade_target(from_history)
        if not target:
            messagebox.showinfo(APP,'Select a card in Portfolio (or open one in Market History) first.'); return
        cid,price_type,name=target; row=self.row_index.get((cid,price_type)) or {}
        market=row.get('latest_price'); p=self.pricing
        dlg=tk.Toplevel(self); dlg.title('Log a '+('buy' if side=='BUY' else 'sale')); dlg.configure(bg=self.colors['bg']); dlg.transient(self)
        frame=ttk.Frame(dlg,padding=16); frame.pack(fill='both',expand=True)
        ttk.Label(frame,text=f"{'BUY' if side=='BUY' else 'SELL'}  {row.get('name') or name}",font=('Helvetica',13,'bold')).grid(row=0,column=0,columnspan=2,sticky='w')
        ttk.Label(frame,text=f"Market now {money(market)}",style='Small.TLabel').grid(row=1,column=0,columnspan=2,sticky='w',pady=(0,8))
        default_price=price if price is not None else row.get('low_price') if side=='BUY' else row.get('target_sell') or market
        values={'qty':tk.StringVar(value='1'),'price':tk.StringVar(value='' if default_price is None else f'{default_price:.2f}'),
                'cond':tk.StringVar(value=cond or 'NM'),'fees':tk.StringVar(),'ship':tk.StringVar(),'date':tk.StringVar(value=date.today().isoformat()),
                'note':tk.StringVar()}
        def suggest(*_a):
            try: qty=int(values['qty'].get() or 1); price=float(values['price'].get())
            except ValueError: return
            if side=='SELL':
                values['fees'].set(f"{price*qty*p['fee_pct']/100+p['fee_fixed']:.2f}")
                values['ship'].set(f"{selling_costs(price,p)-p['fee_fixed']-p['cost']:.2f}")
            else: values['ship'].set(f"{p['ship_in']*qty:.2f}")
        fields=[('Quantity','qty'),('Price per copy $','price'),('Condition','cond')]
        fields+=[('Fees paid (total) $','fees'),('Shipping you paid (total) $','ship')] if side=='SELL' else [('Shipping you paid (total) $','ship')]
        fields+=[('Date (e.g. 10/29/2026)','date'),('Note','note')]
        for i,(label,key) in enumerate(fields,2):
            ttk.Label(frame,text=label).grid(row=i,column=0,sticky='w',pady=3,padx=(0,10))
            if key=='cond': ttk.Combobox(frame,textvariable=values[key],values=list(CONDITIONS),state='readonly',width=8).grid(row=i,column=1,sticky='w')
            else: ttk.Entry(frame,textvariable=values[key],width=24 if key=='note' else 12).grid(row=i,column=1,sticky='w')
        values['qty'].trace_add('write',suggest); values['price'].trace_add('write',suggest); suggest()
        def save():
            problems=[]
            try: qty=int(values['qty'].get().strip()); assert qty>0
            except (ValueError,AssertionError): problems.append('Quantity: a whole number of copies, 1 or more')
            try: price=float(values['price'].get().strip().replace('$','').replace(',','')); assert price>=0
            except (ValueError,AssertionError): problems.append('Price per copy: a dollar amount such as 12.50')
            try: fees=parse_filter_value(values['fees'].get()); ship=parse_filter_value(values['ship'].get())
            except ValueError: problems.append('Fees and shipping: dollar amounts such as 1.25, or leave them blank')
            day=parse_trade_date(values['date'].get())
            if not day: problems.append('Date: for example 2026-10-29 or 10/29/2026')
            if problems:
                messagebox.showerror(APP,'Please fix:\n\n'+'\n'.join('• '+x for x in problems),parent=dlg); return
            try:
                cond=values['cond'].get(); pred=self._predict_trade(row,price,cond,(ship or 0.0)/qty) if side=='BUY' else (None,None)
                record_trade(self.store,cid,price_type,side,qty,price,cond,fees,ship,day,market,pred[0],pred[1],values['note'].get().strip(),
                             row.get('price_changes_30d'))
            except ValueError as exc:
                messagebox.showerror(APP,'Could not log the trade: '+str(exc),parent=dlg); return
            dlg.destroy(); self.load_portfolio(); self.load_trades()
            self.status.set(f"Logged {side.lower()} of {qty} × {row.get('name') or name} at {money(price)}")
        buttons=ttk.Frame(frame); buttons.grid(row=len(fields)+2,column=0,columnspan=2,sticky='e',pady=(12,0))
        ttk.Button(buttons,text='Save',command=save).pack(side='right'); ttk.Button(buttons,text='Cancel',command=dlg.destroy).pack(side='right',padx=8)
        dlg.bind('<Return>',lambda _e:save()); dlg.grab_set()

    def _predict_trade(self,row,price,cond,ship_per_copy):
        """(expected profit per copy, win chance) the app predicts for buying this copy now; (None, None) without a forecast."""
        if not row or not self.forecast_model: return None,None
        fc=forecast_for(self.forecast_model,row.get('return_30d'),row.get('return_7d'),row.get('latest_price'),row.get('printing',''),
                        row.get('price_changes_30d'),row.get('return_sd_30d'),row.get('variant'),row.get('days_since_release'))
        if not fc: return None,None
        p=dict(self.pricing,ship_in=ship_per_copy,played_ratio=0.0)  # the condition is known, not inferred
        t=pricing_targets(row['latest_price']*condition_share(self.pricing,cond),price,fc,p,row.get('price_changes_30d'))
        return t['exp_sale_net_low']-(price+ship_per_copy),t['win_at_low']

    def delete_trade(self):
        selected=self.trade_tree.selection()
        if not selected: messagebox.showinfo(APP,'Select a trade first.'); return
        tid=self.trade_tree.item(selected[0],'values')[0]
        if messagebox.askyesno(APP,'Delete this trade from the log? The portfolio quantity is not changed; edit it in Portfolio if needed.'):
            self.store.execute('DELETE FROM trades WHERE id=?',(tid,)); self.load_trades()

    LEARNED_LABELS={'cond_LP':'LP ×','cond_MP':'MP ×','cond_HP':'HP ×','cond_DMG':'DMG ×','fee_pct':'fee %','ship_plain':'outgoing shipping $',
                    'ship_in':'inbound shipping $/card','sell_through':'copies sold per trading day'}
    def apply_learned_settings(self):
        if not self.learned: messagebox.showinfo(APP,'Nothing learned yet; log some sales first.'); return
        changes=[f"{self.LEARNED_LABELS.get(k,k)}: {self.pricing[k]:g} → {v:g}" for k,(v,_n) in self.learned.items()]
        if not messagebox.askyesno(APP,'Change these settings to what your own trades show?\n\n'+'\n'.join(changes)+
                                   '\n\nYou can change them back any time in Settings.'): return
        for key,(value,_n) in self.learned.items(): self.pricing_vars[key].set(f'{value:g}')
        self.apply_pricing(); self.load_trades()
        self.status.set('Applied settings learned from your trades: '+'; '.join(changes))

    def export_trades(self):
        if not self.trade_rows: messagebox.showinfo(APP,'No trades logged yet.'); return
        cols=list(self.trade_rows[0])
        self.save_csv(cols,[[t[c] for c in cols] for t in self.trade_rows],'trades.csv')
    SET_SORTS={'30-day change (one of each)':'change_30d','7-day change (one of each)':'change_7d','Share rising (7d)':'up_share',
               'Value (one of each)':'value','Buy-now count':'buyable','Median chance of rise':'median_rise','Printings':'printings'}
    def sets_tab(self):
        p=self.tabs['Sets & Catalysts']
        self.section(p,'Sets & catalysts','How each set\'s cards worth $1+ are moving, and what is being released soon. New sets and reprint announcements move older cards, '
                     'so check the calendar before buying. Double-click a set to see its cards to look for. Switch View to Release cycle to see how new cards usually move after release.')
        bar=ttk.Frame(p); bar.pack(fill='x')
        self.set_sort=tk.StringVar(value=next(iter(self.SET_SORTS))); self.set_game=tk.StringVar(value='All'); self.set_min=tk.StringVar(value='10')
        self.set_group=tk.StringVar(value='Sets')
        ttk.Label(bar,text='View',style='Small.TLabel').pack(side='left',padx=(0,4))
        box=ttk.Combobox(bar,textvariable=self.set_group,values=['Sets','Variants','Release cycle'],state='readonly',width=13); box.pack(side='left',padx=(0,12))
        box.bind('<<ComboboxSelected>>',lambda _e:self.populate_sets())
        ttk.Label(bar,text='Sort by',style='Small.TLabel').pack(side='left',padx=(0,4))
        box=ttk.Combobox(bar,textvariable=self.set_sort,values=list(self.SET_SORTS),state='readonly',width=24); box.pack(side='left',padx=(0,12))
        box.bind('<<ComboboxSelected>>',lambda _e:self.populate_sets())
        ttk.Label(bar,text='Game',style='Small.TLabel').pack(side='left',padx=(0,4))
        box=ttk.Combobox(bar,textvariable=self.set_game,values=['All',*SUPPORTED_GAMES],state='readonly',width=11); box.pack(side='left',padx=(0,12))
        box.bind('<<ComboboxSelected>>',lambda _e:self.populate_sets())
        ttk.Label(bar,text='Min printings',style='Small.TLabel').pack(side='left',padx=(0,4))
        entry=ttk.Entry(bar,textvariable=self.set_min,width=5); entry.pack(side='left',padx=(0,12)); entry.bind('<Return>',lambda _e:self.populate_sets())
        ttk.Button(bar,text='Export sets CSV',command=self.export_sets).pack(side='left',padx=(0,8))
        ttk.Button(bar,text='Refresh release calendar',command=lambda:self.refresh_catalysts_async(True)).pack(side='left')
        # Two views share the tab: sets/variants with the release calendar, or the release cycle.
        self.sets_view=ttk.Frame(p); self.sets_view.pack(fill='both',expand=True)
        self.cycle_view=ttk.Frame(p)
        v=self.sets_view
        self.sets_tree=self.gridview(v,('Key','Game','Set','Name','Printings','7d %','30d %','Rising 7d','Value (1 each)',
                                        'Liquidity','Chance of rise','Buy now'),11)
        self.sets_tree.column('Key',width=0,minwidth=0,stretch=False)
        for col,width in (('Game',60),('Set',70),('Name',280),('Printings',70),('7d %',70),('30d %',70),('Rising 7d',75),
                          ('Value (1 each)',100),('Liquidity',70),('Chance of rise',95),('Buy now',70)):
            self.sets_tree.column(col,width=width,minwidth=50,stretch=(col=='Name'))
        self.sets_tree.bind('<Double-1>',lambda _e:self._open_set(self.sets_tree))
        ttk.Label(v,text='Release calendar (last 30 days → next 120 days)',font=('Helvetica',12,'bold')).pack(anchor='w',pady=(4,0))
        self.calendar_note=tk.StringVar(value='')
        ttk.Label(v,textvariable=self.calendar_note,style='Small.TLabel').pack(anchor='w')
        self.calendar_tree=self.gridview(v,('Key','Date','When','Game','Set','Name','Type','Set 7d %','Source'),7)
        self.calendar_tree.column('Key',width=0,minwidth=0,stretch=False)
        for col,width in (('Date',90),('When',90),('Game',70),('Set',70),('Name',300),('Type',110),('Set 7d %',80),('Source',80)):
            self.calendar_tree.column(col,width=width,minwidth=50,stretch=(col=='Name'))
        self.calendar_tree.bind('<Double-1>',lambda _e:self._open_set(self.calendar_tree))
        c=self.cycle_view
        head=ttk.Frame(c); head.pack(fill='x')
        ttk.Label(head,text='Release cycle: how new cards move after release, and what trading it earned',font=('Helvetica',12,'bold')).pack(side='left')
        self.curve_mode=tk.StringVar(value='Daily (first 90 days)')
        box=ttk.Combobox(head,textvariable=self.curve_mode,values=['Daily (first 90 days)','Monthly (2 years)'],state='readonly',width=20)
        box.pack(side='left',padx=12); box.bind('<<ComboboxSelected>>',lambda _e:self._draw_release_curves())
        self.curve_note=tk.StringVar(value='')
        ttk.Label(c,textvariable=self.curve_note,style='Small.TLabel',wraplength=1350).pack(anchor='w')
        top=ttk.Frame(c); top.pack(fill='x',pady=(2,4))
        top.columnconfigure(0,weight=2); top.columnconfigure(1,weight=3)
        self.curve_chart=tk.Canvas(top,height=250,bg='#0b1726',highlightthickness=1,highlightbackground='#253b57')
        self.curve_chart.grid(row=0,column=0,sticky='nsew',padx=(0,6)); self.curve_chart.bind('<Configure>',lambda _e:self._draw_release_curves())
        stats=ttk.LabelFrame(top,text=' RELEASE TRADES ON YOUR HISTORY, AFTER ALL COSTS ',padding=4); stats.grid(row=0,column=1,sticky='nsew')
        self.cycle_stats=self.gridview(stats,('Cards','Trade','Median','$ per copy','Better/profitable','Printings'),7)
        for col,width in (('Cards',130),('Trade',330),('Median',70),('$ per copy',80),('Better/profitable',115),('Printings',70)):
            self.cycle_stats.column(col,width=width,minwidth=40,stretch=(col=='Trade'))
        box=ttk.LabelFrame(c,text=' NEW-SET OPPORTUNITIES (presale and first 90 days) ',padding=4); box.pack(fill='both',expand=True)
        self.cycle_tree=self.gridview(box,('ID','Action','Card','Set','Age','Market','Typical move','Note'),10)
        self.cycle_tree.column('ID',width=0,minwidth=0,stretch=False)
        for col,width in (('Action',90),('Card',260),('Set',55),('Age',85),('Market',75),('Typical move',100),('Note',560)):
            self.cycle_tree.column(col,width=width,minwidth=40,stretch=(col=='Note'))
        self.cycle_tree.bind('<Double-1>',lambda _e:self.open_ranked_history(self.cycle_tree))
        self.set_rows=[]
    def populate_sets(self):
        if not hasattr(self,'sets_tree'): return
        cycle=self.set_group.get()=='Release cycle'
        (self.sets_view.pack_forget if cycle else self.cycle_view.pack_forget)()
        (self.cycle_view if cycle else self.sets_view).pack(fill='both',expand=True)
        if cycle: self._draw_release_curves(); return
        if 'diagnostics' not in self.ranking_data: return
        summary=set_summary(self.ranking_data.get('fresh') or [],self.set_name_map)
        self.set_stats={(s['game'],s['set_code']):s for s in summary}
        variants=self.set_group.get()=='Variants'
        if variants: summary=variant_summary(self.ranking_data.get('fresh') or [])
        self.sets_tree.heading('Set',text='Variant' if variants else 'Set'); self.sets_tree.column('Set',width=230 if variants else 70)
        try: min_n=int(parse_filter_value(self.set_min.get()) or 0)
        except ValueError: min_n=0
        key=self.SET_SORTS[self.set_sort.get()]; game=self.set_game.get()
        rows=[s for s in summary if s['printings']>=min_n and (game=='All' or s['game']==game)]
        rows.sort(key=lambda s:(s[key] is None,-(s[key] or 0),s['set_name']))
        self.set_rows=rows; self.clear(self.sets_tree)
        pct=lambda v: '—' if v is None else f'{v:+.1f}%'
        for s in rows:
            m=s['change_7d']; tag='' if m is None else 'hot' if m>=3 else 'up' if m>0.5 else 'cold' if m<=-3 else 'down' if m<-0.5 else ''
            self.sets_tree.insert('','end',tags=(tag,),values=(f"{'variant' if variants else 'set'}:{s['game']}:{s['set_code']}",s['game'],s['set_code'],s['set_name'],s['printings'],
                pct(s['change_7d']),pct(s['change_30d']),'—' if s['up_share'] is None else f"{s['up_share']*100:.0f}%",money(s['value']),
                '—' if s['median_liquidity'] is None else f"{s['median_liquidity']:.0f}/30",
                '—' if s['median_rise'] is None else f"{s['median_rise']*100:.0f}%",s['buyable'] if self._annotations_current() else '…'))
        self.populate_calendar()
    CURVE_COLORS=('#ffb000','#5ca9ff','#5fd38d','#c39bd3')
    CYCLE_PHASES={(-14,0):'last 2 weeks before release',(0,14):'first 2 weeks',(14,42):'weeks 2–6',(42,90):'weeks 6–13'}
    def _draw_release_curves(self):
        if getattr(self,'curve_mode',None) is not None and self.curve_mode.get()=='Monthly (2 years)': return self._draw_monthly_curves()
        canvas=self.curve_chart; canvas.delete('all'); curves=load_release_curves()
        width=max(300,canvas.winfo_width()); height=max(120,canvas.winfo_height())
        left,right,top,bottom=60,width-20,30,height-24; lo_d,hi_d=RELEASE_CURVE_RANGE
        if not curves:
            canvas.create_text(width/2,height/2,fill='#95aac7',text='No set in your history has been released long enough to measure yet'); self.curve_note.set(''); return
        vals=[v for c in curves.values() for _d,m,q1,q3,_n in c['curve'] for v in (q1,q3)]+[0.0]
        lo,hi=max(-0.8,min(vals)),min(1.5,max(vals))
        if hi-lo<1e-6: hi=lo+0.1
        x=lambda d: left+(right-left)*(d-lo_d)/(hi_d-lo_d); y=lambda v: top+(bottom-top)*(hi-max(lo,min(hi,v)))/(hi-lo)
        canvas.create_line(left,y(0),right,y(0),fill='#4d6a8c',dash=(3,3)); canvas.create_line(x(0),top,x(0),bottom,fill='#ffb000',dash=(3,3))
        canvas.create_text(x(0)+4,top-8,anchor='w',fill='#ffb000',font=('Helvetica',9),text='release day')
        for d in (-30,0,14,42,90): canvas.create_text(x(d),bottom+12,fill='#95aac7',font=('Helvetica',9),text=f'{d:+d}d' if d else '0')
        for v in (lo,0.0,hi): canvas.create_text(left-6,y(v),anchor='e',fill='#95aac7',font=('Helvetica',9),text=f'{v*100:+.0f}%')
        notes=[]
        for i,(label,c) in enumerate(sorted(curves.items())):
            color=self.CURVE_COLORS[i%len(self.CURVE_COLORS)]; pts=c['curve']
            if len(pts)>=2:
                band=[(x(d),y(q3)) for d,_m,_q1,q3,_n in pts]+[(x(d),y(q1)) for d,_m,q1,_q3,_n in reversed(pts)]
                canvas.create_polygon(*[v for xy in band for v in xy],fill='',outline=color,dash=(1,3))
                canvas.create_line(*[v for d,m,_q1,_q3,_n in pts for v in (x(d),y(m))],fill=color,width=2)
            canvas.create_text(right-4,top+4+14*i,anchor='ne',fill=color,font=('Helvetica',9),text=f"{label} ({c['cards']:,} printings, {len(c['sets'])} sets)")
            moves=[(a,b,curve_change(pts,a,b)) for a,b in ((-14,0),(0,14),(14,42),(42,90))]
            notes.append(f"{label}: "+', '.join(f"{self.CYCLE_PHASES[(a,b)]} {m:+.0f}%" for a,b,m in moves if m is not None))
        self.clear(self.cycle_stats)
        for label,c in sorted(curves.items()):
            for t in c.get('trades') or ():
                d=t['median_dollars']
                self.cycle_stats.insert('','end',tags=('up' if t['median']>0 else 'down',),values=(label,t['name'],f"{t['median']*100:+.0f}%",
                    money(d) if d>=0 else '−'+money(-d),f"{t['win']*100:.0f}%",f"{t['n']:,}"))
        self.curve_note.set('Typical price change of new cards: '+' · '.join(notes)+
                            '. Solid line = typical card; dotted outline = where the middle half of cards landed. '
                            'Pre-sell rows compare selling early with selling on day 14.')
        self.populate_cycle()

    def _draw_monthly_curves(self):
        canvas=self.curve_chart; canvas.delete('all'); load_release_curves(); curves=load_monthly_curves()
        width=max(300,canvas.winfo_width()); height=max(120,canvas.winfo_height())
        left,right,top,bottom=60,width-20,30,height-24; lo_m,hi_m=LONGRUN_MONTHS
        if not curves:
            canvas.create_text(width/2,height/2,fill='#95aac7',text='The long-run sample builds weekly with the background sync'); return
        vals=[v for c in curves.values() for _m,mm,q1,q3,_n in c['curve'] for v in (q1,q3)]+[0.0]
        lo,hi=max(-0.8,min(vals)),min(2.0,max(vals))
        x=lambda m: left+(right-left)*(m-lo_m)/(hi_m-lo_m); y=lambda v: top+(bottom-top)*(hi-max(lo,min(hi,v)))/(hi-lo)
        canvas.create_line(left,y(0),right,y(0),fill='#4d6a8c',dash=(3,3)); canvas.create_line(x(0),top,x(0),bottom,fill='#ffb000',dash=(3,3))
        for m in (0,3,6,12,18,24): canvas.create_text(x(m),bottom+12,fill='#95aac7',font=('Helvetica',9),text=f'{m}m')
        for v in (lo,0.0,hi): canvas.create_text(left-6,y(v),anchor='e',fill='#95aac7',font=('Helvetica',9),text=f'{v*100:+.0f}%')
        notes=[]
        for i,(game,c) in enumerate(sorted(curves.items())):
            color=self.CURVE_COLORS[i%len(self.CURVE_COLORS)]; pts=c['curve']
            if len(pts)>=2: canvas.create_line(*[v for m,mm,_a,_b,_n in pts for v in (x(m),y(mm))],fill=color,width=2)
            canvas.create_text(right-4,top+4+14*i,anchor='ne',fill=color,font=('Helvetica',9),
                               text=f"{game} ({c['cards']} chase cards, {len(c['sets'])} sets)"+(' — too few sets to act on yet' if len(c['sets'])<LONGRUN_MIN_SETS else ''))
            d={m:mm for m,mm,_a,_b,_n in pts}
            notes.append(f"{game}: "+', '.join(f'month {m} {d[m]*100:+.0f}%' for m in (3,6,12,24) if m in d))
        self.curve_note.set('Monthly prices of each set\'s chase cards (chosen by their release-month price) vs the release month, from PriceCharting. '+
                            ' · '.join(notes)+'.')

    def populate_cycle(self):
        if not hasattr(self,'cycle_tree'): return
        self.clear(self.cycle_tree)
        opps=release_opportunities(self.ranking_data.get('fresh') or [],self.pricing)
        for o in opps[:300]:
            r=o['row']; age=r['days_since_release']
            self.cycle_tree.insert('','end',tags=({'PRE-SELL':'warn','BUY THE DIP':'up','WAIT':'down','LONG-TERM BUY':'up'}.get(o['action'],''),),
                values=(f"{r['card_id']}#{r['price_type']}",o['action'],r['name'],r.get('set_code') or '',
                        f'{-age} days before' if age<0 else f'day {age}',money(r['latest_price']),f"{o['move']:+.0f}% by day {o['by_day']}",o['note']))
        if not opps: self.cycle_tree.insert('','end',values=('','—','No new-set opportunities','','','','','Needs a set in presale or under 90 days old and a measured release curve'))

    def populate_calendar(self):
        if not hasattr(self,'calendar_tree'): return
        self.clear(self.calendar_tree)
        for c in self.catalysts:
            stats=self.set_stats.get((c['game'],c['set_code']))
            when='today' if c['days']==0 else f"in {plural(c['days'],'day')}" if c['days']>0 else f"{plural(-c['days'],'day')} ago"
            move='—' if not stats or stats.get('change_7d') is None else f"{stats['change_7d']:+.1f}%"
            self.calendar_tree.insert('','end',tags=('up' if c['days']>=0 else '',),values=(f"set:{c['game']}:{c['set_code']}",c['released_on'],when,
                c['game'],c['set_code'],c['set_name'],c['set_type'].replace('_',' '),move,c['source']))
        fetched=self.store.get_setting('catalysts_epoch','')
        stamp=datetime.fromtimestamp(float(fetched)).strftime('%Y-%m-%d %H:%M') if fetched else 'never'
        self.calendar_note.set(f"{len(self.catalysts):,} releases · calendar refreshed {stamp} (also refreshed by each daily sync)")
        if hasattr(self,'curve_chart'): self._draw_release_curves()
    def _open_set(self,tree):
        selected=tree.selection()
        if not selected: return
        iid=str(tree.item(selected[0],'values')[0])
        if iid.startswith('set:'):
            _,game,code=iid.split(':',2); self.show_set_cards(game,code)
        elif iid.startswith('variant:'):
            _,game,variant=iid.split(':',2); self.buy_inputs['variant'].set('' if variant=='Regular' else variant); self.show_set_cards(game,'')
    def show_set_cards(self,game,code):
        self.buy_inputs['set'].set(code); self.buy_game.set(game if game in SUPPORTED_GAMES else 'All')
        self.buy_inputs['min'].set('1'); self.buy_inputs['liq'].set('')
        self.nb.select(self.tabs['Cards to Look For']); self.populate_buy_list()
    def export_sets(self):
        if not self.set_rows: messagebox.showinfo(APP,'No sets to export yet.'); return
        self.save_csv(['game','set_code','set_name','printings','basket_change_7d_pct','basket_change_30d_pct','share_rising_7d',
                       'value_one_of_each','median_trading_days_30d','median_chance_rise','buy_now_count'],
                      [(s['game'],s['set_code'],s['set_name'],s['printings'],s['change_7d'],s['change_30d'],s['up_share'],s['value'],
                        s['median_liquidity'],s['median_rise'],s['buyable']) for s in self.set_rows],'sets.csv')
    def load_catalysts(self):
        try: self.catalysts=catalyst_calendar(self.store)
        except sqlite3.Error: self.catalysts=[]
        self.populate_calendar(); self.populate_alerts()
    def _load_set_names(self):
        def worker():
            try:
                with ReadOnlyStore() as reader: self.events.put(('set_names',set_names(reader)))
            except Exception: pass
        threading.Thread(target=worker,daemon=True).start()
    def refresh_catalysts_async(self,include_tcgcsv=True):
        self.status.set('Refreshing the release calendar (Scryfall + TCGCSV set lists)…')
        def worker():
            try:
                notes=[]; count=refresh_catalysts(self.store,notes.append,include_tcgcsv)
                self.events.put(('catalysts',(count,notes)))
            except Exception as exc: self.events.put(('catalysts',(0,[str(exc)])))
        threading.Thread(target=worker,daemon=True).start()
    def _index_rows(self,data):
        self.row_index={(r['card_id'],r['price_type']):r for r in data.get('fresh') or []}
        by_card={}
        for r in data.get('fresh') or []: by_card.setdefault(r['card_id'],[]).append(r)
        self.rows_by_card=by_card
    def refresh_views(self):
        """Repaint everything derived from the rankings, forecast and portfolio."""
        self.populate_overview(); self.populate_sets(); self.load_portfolio(); self.populate_today()
    HISTORY_TILE_NAMES={'P(Sharpe>0)':'Trend is real (chance)','30-day Sharpe':'Gain vs swings (Sharpe)','Market ÷ low':'Market vs cheapest',
                        'Win % at low':'Chance of profit at low','30-day drawdown':'Drop from 30-day high'}
    HISTORY_STATS=(('Market','Low listing','7-day','30-day','P(Sharpe>0)','30-day high','30-day drawdown'),
                   ('30-day Sharpe','30-day volatility','Market ÷ low','Liquidity','Chance it sells','Suggested qty','Ranking'),
                   ('Forecast median','80% range','Chance of rise','Win % at low','Max buy NM/LP/MP','Break-even sell','List at (target)'))

    def history_tab(self):
        p=self.tabs['Market History']
        bar=ttk.Frame(p); bar.pack(fill='x',pady=(0,6))
        ttk.Label(bar,text='Market history',font=('Helvetica',16,'bold')).pack(side='left',padx=(0,16))
        self.history_search=tk.StringVar(); self.history_game=tk.StringVar(value='All')
        entry=ttk.Entry(bar,textvariable=self.history_search,width=32); entry.pack(side='left',padx=(0,8))
        entry.bind('<Return>',lambda _e:self.search_history_cards())
        ttk.Combobox(bar,textvariable=self.history_game,values=['All',*SUPPORTED_GAMES],state='readonly',width=11).pack(side='left',padx=(0,8))
        ttk.Button(bar,text='Find cards',command=self.search_history_cards).pack(side='left',padx=(0,8))
        ttk.Label(bar,text='Daily TCGplayer market estimates, not individual sales',style='Small.TLabel').pack(side='right')
        # Search results appear only while picking a card, then collapse so the chart has the space.
        self.history_results_frame=ttk.Frame(p)
        self.history_results=self.gridview(self.history_results_frame,('ID','Game','Card','Set','Type'),4)
        self.history_results.column('ID',width=0,minwidth=0,stretch=False)
        self.history_results.bind('<Double-1>',lambda _e:self.load_selected_history())
        self.history_results.bind('<Return>',lambda _e:self.load_selected_history())
        self.history_id=tk.StringVar(value='')
        self.history_header=ttk.Frame(p); self.history_header.pack(fill='x',pady=(2,4))
        self.history_title=tk.StringVar(value='No card selected'); self.history_series=None
        title_row=ttk.Frame(self.history_header); title_row.pack(fill='x')
        ttk.Label(title_row,textvariable=self.history_title,font=('Helvetica',14,'bold')).pack(side='left')
        self.history_printing=tk.StringVar()
        self.history_printing_box=ttk.Combobox(title_row,textvariable=self.history_printing,state='readonly',width=18)
        self.history_printing_box.bind('<<ComboboxSelected>>',lambda _e:self._history_printing_chosen())
        self.history_printing_box.pack(side='right')
        ttk.Label(title_row,text='Printing',style='Small.TLabel').pack(side='right',padx=(0,6))
        ttk.Button(title_row,text='Add to portfolio',command=self.add_history_to_portfolio).pack(side='right',padx=(0,12))
        ttk.Button(title_row,text='Log a buy…',command=lambda:self.log_trade('BUY',from_history=True)).pack(side='right',padx=(0,8))
        self.history_status=tk.StringVar(value='Search above, or double-click a card in Today, Cards to Look For or Portfolio.')
        ttk.Label(self.history_header,textvariable=self.history_status,style='Small.TLabel',wraplength=1100).pack(anchor='w')
        stats=ttk.Frame(p); stats.pack(fill='x',pady=(0,6)); self.history_stats={}
        for row,keys in enumerate(self.HISTORY_STATS):
            for col,key in enumerate(keys):
                stats.columnconfigure(col,weight=1,uniform='stat')
                cell=tk.Frame(stats,bg=self.colors['panel'],padx=10,pady=5)
                cell.grid(row=row,column=col,sticky='nsew',padx=(0,6),pady=(0,6))
                name=tk.Label(cell,text=self.HISTORY_TILE_NAMES.get(key,key).upper(),bg=self.colors['panel'],fg=self.colors['muted'],
                              font=('Helvetica',8),cursor='question_arrow')
                name.pack(anchor='w'); name.bind('<Button-1>',lambda _e,k=key:self.explain(k))
                var=tk.StringVar(value='—')
                value=tk.Label(cell,textvariable=var,bg=self.colors['panel'],fg=self.colors['light'],font=('Helvetica',13,'bold'),
                               wraplength=180,justify='left')
                value.pack(anchor='w'); self.history_stats[key]=(var,value)
        # Trade calculator (formerly the Opportunity Lab tab), prefilled from the loaded printing.
        calc=ttk.LabelFrame(p,text=' TRADE CALCULATOR ',padding=(10,4)); calc.pack(fill='x',pady=(0,6))
        self.calc_vars={k:tk.StringVar() for k in ('buy','sell','qty')}
        for label,key,width in (('Buy price $','buy',8),('Sell price $','sell',8),('Quantity','qty',5)):
            ttk.Label(calc,text=label,style='Small.TLabel').pack(side='left',padx=(0,4))
            entry=ttk.Entry(calc,textvariable=self.calc_vars[key],width=width); entry.pack(side='left',padx=(0,12))
            entry.bind('<Return>',lambda _e:self.calculate_trade())
        ttk.Button(calc,text='Calculate',command=self.calculate_trade).pack(side='left',padx=(0,12))
        self.calc_result=tk.StringVar(value='Load a card; buy/sell/quantity are prefilled from its lowest listing, target sell and max qty.')
        ttk.Label(calc,textvariable=self.calc_result,font=('Helvetica',11,'bold'),wraplength=560,justify='left').pack(side='left')
        self.history_trade_context=None
        # Price table and export pinned to the bottom so the chart takes whatever height remains.
        bottom=ttk.Frame(p); bottom.pack(side='bottom',fill='x')
        self.pricetree=self.gridview(bottom,('Source time','Price','Currency','Source','Kind','Collected at'),4)
        self.pricetree.master.pack_configure(fill='x',expand=False)
        ttk.Button(bottom,text='Export card history (CSV)',command=self.export_history).pack(anchor='w')
        self.history_chart=tk.Canvas(p,height=260,bg='#0b1726',highlightthickness=1,highlightbackground='#253b57')
        self.history_chart.pack(fill='both',expand=True,pady=(0,6))
        self.history_chart_points=[]; self.history_chart_meta={}
        self.history_chart.bind('<Configure>',lambda _e:self._draw_history_chart(self.history_chart_points))
        self.history_chart.bind('<Motion>',self._history_hover)
        self.history_chart.bind('<Leave>',lambda _e:self.history_chart.delete('hover'))
        self._draw_history_chart([])

    def search_history_cards(self):
        needle=self.history_search.get().strip(); game=self.history_game.get(); self.clear(self.history_results)
        sql="SELECT id,game,name,set_code,item_type FROM cards WHERE game IN ('MTG','Pokémon','One Piece','Riftbound')"; args=[]
        if needle:
            sql+=' AND (name LIKE ? OR id LIKE ?)'; args.extend(['%'+needle+'%']*2)
        if game!='All': sql+=' AND game=?'; args.append(game)
        sql+=' ORDER BY name LIMIT 200'
        rows=self.store.q(sql,tuple(args))
        for row in rows: self.history_results.insert('','end',values=row)
        self.history_results_frame.pack(fill='x',before=self.history_header)
        self.history_status.set(f'Found {len(rows):,} matching records. Double-click one (or select it and press Enter) to load it.')

    def load_selected_history(self):
        selected=self.history_results.selection()
        if not selected:
            messagebox.showinfo(APP,'Search for a card and select a result first.'); return
        values=self.history_results.item(selected[0],'values')
        if values:
            self.history_series=None; self.history_id.set(values[0]); self.load_history()

    def _draw_history_chart(self, points):
        self.history_chart_points=list(points)
        meta=getattr(self,'history_chart_meta',None) or {}
        canvas=self.history_chart; canvas.delete('all'); self._hist_hover=None
        width=max(300,canvas.winfo_width()); height=max(160,canvas.winfo_height())
        left,right,top,bottom=72,width-170,40,height-34
        muted,grid,line,low_color='#95aac7','#22364f','#5ca9ff','#e0a458'
        canvas.create_text(14,12,anchor='nw',fill='#dbe7fa',font=('Helvetica',12,'bold'),text=meta.get('title') or 'Market price')
        points=[(str(d)[:10],float(v)) for d,v in points if v is not None and float(v)>0]
        if not points:
            message='No saved market history for this card yet' if self.history_id.get() else 'Search for a card above to chart its price'
            canvas.create_text(width/2,height/2,fill=muted,font=('Helvetica',12),text=message)
            return
        low=meta.get('low'); fc=meta.get('forecast'); ahead=fc['horizon'] if fc else 0; labels=[]
        vals=[v for _,v in points]+([low] if low else [])+([fc['q10_price'],fc['q90_price']] if fc else [])
        lo,hi=min(vals),max(vals)
        pad=(hi-lo)*0.08 or hi*0.05 or 1.0
        lo,hi=max(0.0,lo-pad),hi+pad
        y=lambda v: top+(bottom-top)*(hi-v)/(hi-lo)
        n=len(points); x=lambda i: left+(right-left)*(i/max(1,n-1+ahead))
        for k in range(6):
            value=hi-(hi-lo)*k/5; yy=y(value)
            canvas.create_line(left,yy,right,yy,fill=grid)
            canvas.create_text(left-8,yy,anchor='e',fill=muted,text=f'${value:,.2f}')
        for i in sorted({round(k*(n-1)/5) for k in range(6)}):
            canvas.create_line(x(i),bottom,x(i),bottom+4,fill=muted)
            canvas.create_text(x(i),bottom+16,fill=muted,text=points[i][0])
        coords=[c for i,(_,v) in enumerate(points) for c in (x(i),y(v))]
        self._hist_hover={'xs':[x(i) for i in range(n)],'ys':[y(v) for _,v in points],'points':points,
                          'left':left,'right':right,'top':top,'bottom':bottom}
        if n>=2:
            canvas.create_polygon(*coords,x(n-1),bottom,x(0),bottom,fill='#13304f',outline='')
            canvas.create_line(*coords,fill=line,width=2.5)
        index={d:i for i,(d,_v) in enumerate(points)}
        # 30-day moving average, Card Kingdom buylist (the price a dealer pays: your floor) and the set's release day.
        if n>=30:
            run=sum(v for _d,v in points[:30]); ma=[(29,run/30)]
            for i in range(30,n): run+=points[i][1]-points[i-30][1]; ma.append((i,run/30))
            if len(ma)>=2: canvas.create_line(*[c for i,v in ma for c in (x(i),y(min(hi,max(lo,v))))],fill='#c39bd3',dash=(4,3),width=1.5)
            labels.append((y(min(hi,max(lo,ma[-1][1]))),f'30d avg {money(ma[-1][1])}','#c39bd3',('Helvetica',10)))
        bl=[(index[d],v) for d,v in meta.get('buylist') or () if d in index]
        if len(bl)>=2:
            canvas.create_line(*[c for i,v in bl for c in (x(i),y(min(hi,max(lo,v))))],fill='#5fd38d',dash=(2,2),width=1.5)
            labels.append((y(min(hi,max(lo,bl[-1][1]))),f'CK buylist {money(bl[-1][1])}','#5fd38d',('Helvetica',10)))
        release=meta.get('release')
        if release and release in index:
            canvas.create_line(x(index[release]),top,x(index[release]),bottom,fill='#ffb000',dash=(3,3))
            canvas.create_text(x(index[release])+4,bottom-12,anchor='w',fill='#ffb000',font=('Helvetica',9),text='set release')
        last_x,last_y=x(n-1),y(points[-1][1])
        labels.insert(0,(last_y,f'market {money(points[-1][1])}','#dbe7fa',('Helvetica',11,'bold')))
        if fc:
            # Forecast fan: 80% (10th–90th) and 50% (25th–75th percentile) ranges at the horizon, median dashed.
            end_x=x(n-1+ahead)
            canvas.create_line(last_x,top,last_x,bottom,fill='#2c4767',dash=(2,3))
            canvas.create_polygon(last_x,last_y,end_x,y(fc['q90_price']),end_x,y(fc['q10_price']),fill='#1b2e44',outline='')
            canvas.create_polygon(last_x,last_y,end_x,y(fc['q75_price']),end_x,y(fc['q25_price']),fill='#29476a',outline='')
            canvas.create_line(last_x,last_y,end_x,y(fc['median_price']),fill='#9fd0ff',dash=(5,3),width=2)
            canvas.create_text(last_x+8,top+2,anchor='nw',fill=muted,
                               text=f'next {ahead} days: 80% range {money(fc["q10_price"])}–{money(fc["q90_price"])}, 50% {money(fc["q25_price"])}–{money(fc["q75_price"])}')
            canvas.create_line(end_x,bottom,end_x,bottom+4,fill=muted)
            canvas.create_text(end_x,bottom+16,fill=muted,text=f'+{ahead}d')
            labels.append((y(fc['median_price']),f'{ahead}d median {money(fc["median_price"])}','#9fd0ff',('Helvetica',10)))
            labels.append((y(fc['q90_price']),f'80% high {money(fc["q90_price"])}','#7f9cc0',('Helvetica',9)))
            labels.append((y(fc['q75_price']),f'50% high {money(fc["q75_price"])}','#a9c4e4',('Helvetica',9)))
            labels.append((y(fc['q25_price']),f'50% low {money(fc["q25_price"])}','#a9c4e4',('Helvetica',9)))
            labels.append((y(fc['q10_price']),f'80% low {money(fc["q10_price"])}','#7f9cc0',('Helvetica',9)))
        canvas.create_oval(last_x-5,last_y-5,last_x+5,last_y+5,fill=line,outline='#dbe7fa')
        if low:
            low_y=y(low)
            canvas.create_line(left,low_y,right,low_y,fill=low_color,dash=(6,4),width=1.5)
            labels.append((low_y,f'lowest listing {money(low)}',low_color,('Helvetica',10)))
        placed=[]  # nudge right-margin labels apart so they never overlap
        for label_y,text,color,font in sorted(labels):
            if placed and label_y-placed[-1]<16: label_y=placed[-1]+16
            placed.append(label_y)
            canvas.create_text(right+12,label_y,anchor='w',fill=color,font=font,text=text)

    def _show_history_stats(self, metrics=None, points=(), low=None, pricing=None):
        def put(key,text,tone=None):
            var,label=self.history_stats[key]; var.set(text)
            label.configure(fg={'up':'#5fd38d','down':'#ff7b7b'}.get(tone,self.colors['light']))
        if not metrics or not metrics.get('observations'):
            for keys in self.HISTORY_STATS:
                for key in keys: put(key,'—')
            return
        pct=lambda v: '—' if v is None else f'{v:+.1f}%'
        tone=lambda v: None if v is None or abs(v)<0.05 else ('up' if v>0 else 'down')
        latest=metrics['latest_price']
        window_start=(datetime.fromisoformat(metrics['latest_date'])-timedelta(days=29)).date().isoformat()
        ratio=latest/low if low else None
        flags=spike_flags({**metrics,'low_price':low if latest>=RANK_MIN_PRICE else None})
        t=pricing or {}
        cond=t.get('low_cond') if low else None
        put('Market',money(latest)); put('Low listing',money(low)+(f' (≈{cond})' if cond and cond!='NM' else ''),'down' if cond and cond!='NM' else None)
        put('7-day',pct(metrics['return_7d']),tone(metrics['return_7d']))
        put('30-day',pct(metrics['return_30d']),tone(metrics['return_30d']))
        psr=metrics.get('psr')
        put('P(Sharpe>0)','—' if psr is None else f'{min(psr,0.999)*100:.1f}%','up' if psr is not None and psr>=0.95 else None)
        put('30-day high',money(max(v for d,v in points if d>=window_start)))
        changes=metrics.get('price_changes_30d'); liq=liquidity_label(changes)
        put('Liquidity','—' if changes is None else f'{liq} ({changes}/30 days)',
            'up' if liq=='High' else 'down' if liq in ('Low','Very low') else None)
        prob=lambda v: '—' if v is None else f'{v*100:.0f}%'
        put('Chance it sells',prob(t.get('p_sold')))
        qty=(0,'excluded') if flags else self._suggested_qty(t,low,latest) if t else None
        put('Suggested qty','—' if qty is None else f'{qty[0]} ({QTY_LIMIT_WORDS.get(qty[1],qty[1])})','down' if qty and qty[0]==0 else None)
        h=self.pricing['horizon']
        put('Forecast median','—' if not t else f"{money(t['median_price'])} in {h} days")
        put('80% range','—' if not t else f"{money(t['q10_price'])} – {money(t['q90_price'])}")
        ci=lambda v,band: prob(v) if v is None or not band else f'{prob(v)} ({band[0]*100:.0f}–{band[1]*100:.0f})'
        put('Chance of rise',ci(t.get('p_rise'),t.get('p_rise_ci')))
        win=t.get('win_at_low')
        put('Win % at low',ci(win,t.get('win_low_ci')),None if win is None else 'up' if win*100>=self.pricing['win_pct'] else 'down')
        by=t.get('max_buy_cond') or {}
        buy_ok=low and by.get(cond or 'NM') and low<=by[cond or 'NM']
        put('Max buy NM/LP/MP','—' if not t else ' / '.join(f'{by[c]:.2f}' if by.get(c) else '—' for c in ('NM','LP','MP'))
            if t.get('max_buy') else 'none qualifies','up' if buy_ok else 'down' if t else None)
        put('Break-even sell',money(t.get('min_sell')) if t else '—')
        self.history_target_sell=t.get('target_sell') if t else None
        put('List at (target)','—' if not t else f"{money(t['target_sell'])} ({t['target_fill']*100:.0f}% chance within {h} days)" if t['target_ev']>0
            else f"none profitable at {money(low or latest)}",None if not t else 'up' if t['target_ev']>0 else 'down')
        put('30-day drawdown',pct(metrics['drawdown_30d']),tone(metrics['drawdown_30d']))
        put('30-day Sharpe','—' if metrics['sharpe_30d'] is None else f"{metrics['sharpe_30d']:.2f}")
        put('30-day volatility','—' if metrics['volatility_30d'] is None else f"{metrics['volatility_30d']*100:.0f}% /yr")
        put('Market ÷ low','—' if ratio is None else f'{ratio:.2f}×','down' if ratio and (ratio>=SPIKE_MARKET_TO_LOW or ratio<SPIKE_LOW_TO_MARKET) else None)
        if flags: put('Ranking','Excluded','down')
        elif metrics['sharpe_30d'] is not None or metrics['opportunity_score'] is not None: put('Ranking','Eligible','up')
        else: put('Ranking','Needs history')
        self.history_flags=flags

    def _suggested_qty(self,t,low,market):
        """(copies, limit) for the loaded printing, sized like the buy list against what the portfolio holds."""
        cond=t.get('low_cond') or 'NM'; by=t.get('max_buy_cond') or {}
        buyable=low and by.get(cond) and low<=by[cond]
        buy,value=(low,market*condition_share(self.pricing,cond)) if buyable else (t.get('max_buy'),market)
        if not buy: return None
        exposure=portfolio_exposure(self.portfolio_rows); cid=self.history_id.get().strip()
        row=self.row_index.get((cid,'market_'+self.history_printing.get())) or {}
        return suggested_quantity(t,buy,value,self.pricing,exposure['cards'].get((cid,'market_'+self.history_printing.get()),0.0),
                                  exposure['sets'].get((row.get('game'),row.get('set_code')),0.0),exposure['total'])

    def _prefill_trade(self, metrics, low, pricing):
        market=metrics.get('latest_price') if metrics else None
        self.history_trade_context={'metrics':metrics,'pricing':pricing} if market else None
        if not market:
            for var in self.calc_vars.values(): var.set('')
            self.calc_result.set('No market price for this printing yet.'); return
        self.calc_vars['buy'].set(f'{(low or market):.2f}')
        self.calc_vars['sell'].set(f"{(pricing['target_sell'] if pricing else market):.2f}")
        qty=self._suggested_qty(pricing,low,market) if pricing else None
        self.calc_vars['qty'].set(str(max(1,qty[0] if qty else (pricing or {}).get('max_qty') or 1)))
        self.calculate_trade()

    def calculate_trade(self):
        """Net P/L after the assumed fees and per-card costs, plus the forecast chance of profit at that buy price."""
        try:
            buy=float(self.calc_vars['buy'].get().replace('$','')); sell=float(self.calc_vars['sell'].get().replace('$',''))
            qty=int(self.calc_vars['qty'].get())
            p=self.pricing
            profit,roi=calculate_net_profit(buy,sell,p['fee_pct'],(selling_costs(sell,p)+p['ship_in'])*qty,qty)
        except ValueError as exc:
            self.calc_result.set('Enter a buy price, sell price and whole-number quantity'+(f' ({exc})' if str(exc) and 'could not convert' not in str(exc) else '')+'.')
            return
        text=f'Net P/L {money(profit) if profit>=0 else "−"+money(-profit)}  ·  ROI ' + ('n/a' if roi is None else f'{roi:+.1f}%')
        ctx=self.history_trade_context
        keep=1-self.pricing['fee_pct']/100.0
        if keep>0:
            break_even=(buy+self.pricing['ship_in']+selling_costs(sell,self.pricing))/keep
            market=ctx['metrics'].get('latest_price') if ctx else None
            text+=f'  ·  break-even sell {money(break_even)}'+(f' ({(break_even/market-1)*100:+.1f}% vs market)' if market else '')
        if ctx:
            m=ctx['metrics']
            at_buy=self._row_pricing({**m,'printing':self.history_printing.get(),'low_price':buy})
            if at_buy and at_buy['win_at_low'] is not None:
                text+=f"  ·  forecast chance of profit at ${buy:.2f}: {at_buy['win_at_low']*100:.0f}% ({self.pricing['horizon']}d, after fees and shipping)"
            max_qty=(ctx['pricing'] or {}).get('max_qty')
            if max_qty is not None and qty>max(1,max_qty):
                text+=f'  ·  caution: ~{max_qty} sellable in {self.pricing["horizon"]}d at current liquidity'
        self.calc_result.set(text)

    def sharpe_opportunities_tab(self):
        p=self.tabs['Sharpe & Opportunities']
        self.section(p,'Best risk-adjusted history and potential opportunities',
            'In plain words: cards whose price has climbed steadily (not just spiked) over the last 30 days. This is the past, not advice — '
            'use Today or Cards to Look For to decide what to buy. Details for finance users: each printing is ranked from daily TCGplayer market prices. Sharpe needs 28 of 30 days observed, subtracts the T-bill rate and is '
            'autocorrelation-adjusted (Newey–West). P(SR>0) is the Probabilistic Sharpe Ratio; "significant" controls the false-discovery rate across all printings. '
            'Listing spikes and cards under $1 are excluded unless shown. Rankings describe the past; use Win @ low and Max buy to trade.')
        bar=ttk.Frame(p); bar.pack(fill='x',pady=(0,5))
        self.rank_refresh_button=ttk.Button(bar,text='Recalculate rankings',command=lambda:self.refresh_rankings(force=True))
        self.rank_refresh_button.pack(side='left',padx=(0,8))
        ttk.Button(bar,text='Add selected to portfolio',command=self.add_selected_to_portfolio).pack(side='left',padx=(0,8))
        ttk.Button(bar,text='Export rankings CSV',command=self.export_rankings).pack(side='left')
        self.show_excluded=tk.BooleanVar(value=False)
        ttk.Checkbutton(bar,text=f'Show excluded (listing spikes, under ${RANK_MIN_PRICE:,.0f})',variable=self.show_excluded,
                        command=lambda: 'diagnostics' in self.ranking_data and self.populate_rankings(self.ranking_data)).pack(side='left',padx=(12,0))
        self.ranking_note=tk.StringVar(value='Waiting for market data…')
        ttk.Label(p,textvariable=self.ranking_note,style='Small.TLabel',wraplength=1050).pack(anchor='w',pady=(2,4))
        rank_progress_row=ttk.Frame(p); rank_progress_row.pack(fill='x',pady=(0,6))
        self.rank_progress_text=tk.StringVar(value='Rankings have not been calculated yet')
        ttk.Label(rank_progress_row,textvariable=self.rank_progress_text,style='Small.TLabel',width=42).pack(side='left',padx=(0,8))
        self.rank_progress=ttk.Progressbar(rank_progress_row,mode='indeterminate',length=300,maximum=100)
        self.rank_progress.pack(side='left',fill='x',expand=True)
        self._build_rank_filters(p)
        self.rankings_busy=False
        panels=ttk.Frame(p); panels.pack(fill='both',expand=True)
        left=ttk.LabelFrame(panels,text=' BEST 30-DAY SHARPE RATIOS ',padding=7)
        right=ttk.LabelFrame(panels,text=' POTENTIAL OPPORTUNITIES / HISTORY BUILDING ',padding=7)
        self.sharpe_empty_text=tk.StringVar(value='No valid Sharpe ratios yet. Requires at least 28 of the last 30 days observed and at least 20 consecutive daily returns.')
        self.sharpe_empty_label=ttk.Label(left,textvariable=self.sharpe_empty_text,style='Small.TLabel',wraplength=430)
        self.sharpe_empty_label.pack(anchor='w',fill='x',pady=(0,5))
        # Stacked full-width: each table carries a dozen columns once pricing and liquidity are shown.
        left.pack(side='top',fill='both',expand=True,pady=(0,4))
        right.pack(side='top',fill='both',expand=True)
        self.sharpe_tree=self.gridview(left,('ID','Card','Game','Price','Low','Sharpe','P(SR>0)','30d %','Liquidity','Win @ low','Max buy','Max qty','Excluded'),6)
        self.sharpe_tree.column('ID',width=0,minwidth=0,stretch=False)
        for col,width in [('Card',260),('Game',60),('Price',80),('Low',80),('Sharpe',70),('P(SR>0)',75),('30d %',80),('Liquidity',100),('Win @ low',80),
                          ('Max buy',80),('Max qty',70),('Excluded',150)]:
            self.sharpe_tree.column(col,width=width,minwidth=width,stretch=(col=='Card'))
        self.opportunity_tree=self.gridview(right,('ID','Card','Game','Price','Low','Score','7d %','30d %','Liquidity','Win @ low','Max buy','Max qty','State'),6)
        self.opportunity_tree.column('ID',width=0,minwidth=0,stretch=False)
        for col,width in [('Card',260),('Game',60),('Price',80),('Low',80),('Score',60),('7d %',80),('30d %',80),('Liquidity',100),
                          ('Win @ low',80),('Max buy',80),('Max qty',70),('State',150)]:
            self.opportunity_tree.column(col,width=width,minwidth=width,stretch=(col=='Card'))
        self.sharpe_tree.bind('<Double-1>',lambda _e:self.open_ranked_history(self.sharpe_tree))
        self.opportunity_tree.bind('<Double-1>',lambda _e:self.open_ranked_history(self.opportunity_tree))
        self.ranking_data={'all':[],'fresh':[],'sharpe':[],'opportunities':[]}

    def buy_list_tab(self):
        p=self.tabs['Cards to Look For']
        self.section(p,'Cards to look for',
            'Cards that should make money after every fee and shipping cost, using your numbers in Settings. '
            'Max buy is the most to pay (Near Mint · Lightly Played · Moderately Played): pay that or less and the card should profit. '
            'BUY NOW means a listing is already under it; otherwise use it as your offer for trade-ins and collections. '
            'Qty is how many copies to get, and the word in brackets says what limited it. Click a row to read the advice; '
            'double-click to chart it; click a column heading to explain it. Estimates from past prices, not guarantees.')
        bar=ttk.Frame(p); bar.pack(fill='x',pady=(0,6))
        self.buy_sort=tk.StringVar(value=next(iter(BUY_LIST_SORTS)))
        ttk.Label(bar,text='Sort by',style='Small.TLabel').pack(side='left',padx=(0,4))
        sort=ttk.Combobox(bar,textvariable=self.buy_sort,values=list(BUY_LIST_SORTS),state='readonly',width=40)
        sort.pack(side='left',padx=(0,12)); sort.bind('<<ComboboxSelected>>',lambda _e:self.populate_buy_list())
        self.buy_game=tk.StringVar(value='All')
        ttk.Label(bar,text='Game',style='Small.TLabel').pack(side='left',padx=(0,4))
        game=ttk.Combobox(bar,textvariable=self.buy_game,values=['All',*SUPPORTED_GAMES],state='readonly',width=11)
        game.pack(side='left',padx=(0,12)); game.bind('<<ComboboxSelected>>',lambda _e:self.populate_buy_list())
        self.buy_inputs={}
        bar2=ttk.Frame(p); bar2.pack(fill='x',pady=(0,6)); bar3=ttk.Frame(p); bar3.pack(fill='x',pady=(0,6))
        for label,key,default,where in (('Min price $','min','1',bar),('Max price $','max','',bar),('Min trading days /30','liq','6',bar),
                                        ('Set code','set','',bar2),('Variant','variant','',bar2)):
            ttk.Label(where,text=label,style='Small.TLabel').pack(side='left',padx=(0,4))
            self.buy_inputs[key]=tk.StringVar(value=default)
            entry=ttk.Entry(where,textvariable=self.buy_inputs[key],width=7); entry.pack(side='left',padx=(0,12))
            entry.bind('<Return>',lambda _e:self.populate_buy_list())
        self.buy_now_only=tk.BooleanVar(value=False)
        ttk.Checkbutton(bar2,text='Buy now only',variable=self.buy_now_only,command=self.populate_buy_list).pack(side='left',padx=(0,12))
        self.hide_reprints=tk.BooleanVar(value=True)
        ttk.Checkbutton(bar2,text='Hide announced reprints & new sets under 6 weeks',variable=self.hide_reprints,command=self.populate_buy_list).pack(side='left',padx=(0,12))
        ttk.Button(bar3,text='Update list',command=self.populate_buy_list).pack(side='left',padx=(0,8))
        ttk.Button(bar3,text='Export list (CSV)',command=self.export_buy_list).pack(side='left')
        ttk.Button(bar3,text='Add selected to portfolio',command=lambda:self.add_selected_to_portfolio((self.buy_tree,))).pack(side='left',padx=(8,0))
        ttk.Button(bar3,text='Copy TCGplayer Mass Entry',command=self.copy_mass_entry).pack(side='left',padx=(8,0))
        self.buy_note=tk.StringVar(value='Waiting for rankings and the forecast model…')
        ttk.Label(p,textvariable=self.buy_note,style='Small.TLabel',wraplength=1500).pack(anchor='w',pady=(0,4))
        cols=('ID','Card','Game','Market','Low','Low ≈','Max buy NM · LP · MP','Exp. profit','Win','Sells','Liquidity','Qty','Target sell',
              'Range 80%','Vol /yr','CK buylist','Formats','EDHREC','Recommendation')
        self.buy_tree=self.gridview(p,cols,20)
        self.buy_tree.column('ID',width=0,minwidth=0,stretch=False)
        for col,width in [('Card',230),('Game',55),('Market',70),('Low',70),('Low ≈',45),('Max buy NM · LP · MP',265),('Exp. profit',110),
                          ('Win',55),('Sells',50),('Liquidity',85),('Qty',110),('Target sell',110),('Range 80%',120),('Vol /yr',60),
                          ('CK buylist',75),('Formats',120),
                          ('EDHREC',60),('Recommendation',520)]:
            self.buy_tree.column(col,width=width,minwidth=width,stretch=(col=='Recommendation'))
        self.buy_tree.bind('<Double-1>',lambda _e:self.open_ranked_history(self.buy_tree))
        self.buy_detail=tk.StringVar(value='')
        ttk.Label(p,textvariable=self.buy_detail,wraplength=1350,justify='left').pack(anchor='w')
        self.buy_tree.bind('<<TreeviewSelect>>',lambda _e:self._show_buy_detail())
        self.buy_rows=[]

    def _buy_list_rows(self):
        if not self._annotations_current(): return None
        try:
            pmin=parse_filter_value(self.buy_inputs['min'].get()); pmax=parse_filter_value(self.buy_inputs['max'].get())
            liq=parse_filter_value(self.buy_inputs['liq'].get())
        except ValueError:
            self.buy_note.set('Price and trading-day limits must be numbers (or blank).'); return []
        return buy_list(self.ranking_data['fresh'],self.buy_sort.get(),self.buy_game.get(),pmin,pmax,
                        None if liq is None else int(liq),self.buy_now_only.get(),set_code=self.buy_inputs['set'].get().strip() or None,
                        hide_reprints=self.hide_reprints.get(),variant=self.buy_inputs['variant'].get().strip() or None)

    def _show_buy_detail(self):
        sel=self.buy_tree.selection()
        if not sel: return
        v=self.buy_tree.item(sel[0],'values')
        if v: self.buy_detail.set(f"{v[1]}: {v[-1]} · expected profit {v[7]} per copy")

    def populate_buy_list(self):
        self.clear(self.buy_tree)
        rows=self._buy_list_rows()
        if rows is None:
            self.buy_note.set('Waiting for rankings, the forecast model and buy/sell prices…'); return
        self.buy_rows=rows; h=self.pricing['horizon']
        signed=lambda v: '—' if v is None else (money(v) if v>=0 else '−'+money(-v))
        pct=lambda v: '—' if v is None else f'{v*100:.0f}%'
        for r in rows:
            profit=r['exp_profit_low'] if r.get('buyable') else r.get('exp_profit_max_buy')
            changes=r.get('price_changes_30d')
            self.buy_tree.insert('','end',values=(f"{r['card_id']}#{r['price_type']}",r['name'],r['game'],money(r['latest_price']),
                money(r.get('low_price')),r.get('low_cond') or '—',max_buy_text(r),f"{signed(profit)} {'now' if r.get('buyable') else 'at max'}",
                pct(r.get('win')),pct(r.get('p_sold')),'—' if changes is None else f'{changes} {liquidity_label(changes)}',
                '—' if r.get('qty') is None else f"{r['qty']} ({QTY_LIMIT_WORDS.get(r.get('qty_limit'),r.get('qty_limit'))})",
                '—' if r.get('target_sell') is None else f"{money(r['target_sell'])} ({(r.get('target_fill') or 0)*100:.0f}%)",
                '—' if r.get('q10_price') is None else f"{money(r['q10_price'])}–{money(r['q90_price'])}",
                '—' if r.get('volatility_30d') is None else f"{r['volatility_30d']*100:.0f}%",
                money(r.get('buylist')),r.get('formats') or ('—' if r['game']=='MTG' else ''),r.get('edhrec') or '—',
                buy_recommendation(r,h,self.pricing,self.cardmarket_on())),tags=('warn',) if r.get('reprint') or r.get('legal_change') else ())
        now=sum(1 for r in rows if r.get('buyable')); p=self.pricing
        self.buy_note.set(f"{len(rows):,} printings shown ({now:,} buy now, {len(rows)-now:,} buy-in targets; top 300). "
                          f"Assumptions: {p['fee_pct']:g}% + ${p['fee_fixed']:.2f} selling fee, shipping ${p['ship_plain']:.2f} "
                          f"(${p['ship_tracked']:.2f} tracked from ${p['ship_threshold']:g}), ${p['ship_in']:.2f} inbound, ${p['cost']:.2f} supplies, "
                          f"{p['win_pct']:g}% target win, {h}-day horizon, ≥ {money(p['min_profit'])} and ≥ {p['min_roi']:g}% expected profit per copy, {p['sell_through']:g} copies sold per trading day; "
                          f"capital {money(p['capital'])}, ≤ {money(p['max_card'])} per card, ≤ {p['max_set_pct']:g}% per set. "
                          "Double-click a card for its chart.")
        if not rows:
            game=self.buy_game.get(); fresh=[r for r in self.ranking_data.get('fresh') or () if game=='All' or r.get('game')==game]
            days=max((r.get('observations') or 0 for r in fresh),default=0)
            if fresh and days<HISTORY_READY_DAYS:
                self.buy_note.set(f"No {game} cards yet: the app needs about {HISTORY_READY_DAYS} days of prices before it suggests buys, and it has {days} so far. "
                                  "The daily update adds one day at a time; use the card checker on the Today tab meanwhile.")
            else:
                self.buy_note.set('No cards match these filters. Try a lower Min price or Min trading days, clear Set code and Variant, or untick Buy now only.')

    def copy_mass_entry(self):
        rows=[r for r in self.buy_rows if r.get('qty')]
        if not rows: messagebox.showinfo(APP,'No rows with a suggested quantity; loosen the limits or wait for prices.'); return
        self.clipboard_clear(); self.clipboard_append(mass_entry_text(rows))
        self.status.set(f'Copied {len(rows):,} lines for TCGplayer Mass Entry (quantity, name, [set]); check each match and condition before buying')

    def cardmarket_on(self): return self.store.get_setting('cardmarket_module','0')=='1'

    def export_buy_list(self):
        if not self.buy_rows:
            messagebox.showinfo(APP,'The list is empty; wait for prices to finish or loosen the limits.'); return
        h=self.pricing['horizon']
        by=lambda r,c: (r.get('max_buy_cond') or {}).get(c)
        self.save_csv(['card_id','printing','game','set','name','market','lowest_listing','lowest_listing_likely_condition',
                       'max_buy_nm','max_buy_lp','max_buy_mp','max_buy_hp','buy_now','exp_profit_buying_now',
                       'exp_profit_at_max_buy','win_at_low','chance_sells','chance_rises','price_change_days_30d','sellable_qty',
                       'suggested_qty','qty_limited_by','target_sell','quick_sale','break_even_sell','recommendation'],
                      [(r['card_id'],r['printing'],r['game'],r.get('set_code'),r['name'],r['latest_price'],r.get('low_price'),r.get('low_cond'),
                        by(r,'NM'),by(r,'LP'),by(r,'MP'),by(r,'HP'),r.get('buyable'),
                        r.get('exp_profit_low'),r.get('exp_profit_max_buy'),r.get('win'),r.get('p_sold'),r.get('p_rise'),
                        r.get('price_changes_30d'),r.get('max_qty'),r.get('qty'),r.get('qty_limit'),r.get('target_sell'),r.get('quick_sell'),
                        r.get('min_sell'),buy_recommendation(r,h,self.pricing,self.cardmarket_on())) for r in self.buy_rows],'cards_to_look_for.csv')

    def _build_rank_filters(self,parent):
        box=ttk.LabelFrame(parent,text=' FILTERS ',padding=(10,4)); box.pack(fill='x',pady=(0,6))
        specs=[('price_min','Min price',0.0,100.0,price_to_slider(RANK_MIN_PRICE)),
               ('price_max','Max price',0.0,100.0,100.0),
               ('sharpe_min','Min Sharpe',SHARPE_SLIDER_MIN,SHARPE_SLIDER_MAX,SHARPE_SLIDER_MIN),
               ('sharpe_max','Max Sharpe',SHARPE_SLIDER_MIN,SHARPE_SLIDER_MAX,SHARPE_SLIDER_MAX),
               ('liq_min','Min liquidity (trading days /30)',0.0,29.0,0.0),
               ('rise_min','Min chance of rise',0.0,100.0,0.0),
               ('win_min','Min Win @ low',0.0,100.0,0.0)]
        self.rank_filter_vars={}; self.rank_filter_text={}; self._rank_filter_job=None
        self.buyable_only=tk.BooleanVar(value=False)
        for i,(key,label,lo,hi,default) in enumerate(specs):
            row,col=divmod(i,5)
            box.columnconfigure(col,weight=1)
            self.rank_filter_vars[key]=tk.DoubleVar(value=default)
            self.rank_filter_text[key]=tk.StringVar()
            cell=ttk.Frame(box); cell.grid(row=row,column=col,sticky='we',padx=(0,18),pady=(0,2))
            head=ttk.Frame(cell); head.pack(fill='x')
            ttk.Label(head,text=label,style='Small.TLabel').pack(side='left')
            entry=ttk.Entry(head,textvariable=self.rank_filter_text[key],width=8,justify='right')
            entry.pack(side='right')
            entry.bind('<Return>',lambda _e,k=key:self._rank_filter_typed(k))
            entry.bind('<FocusOut>',lambda _e,k=key:self._rank_filter_typed(k))
            ttk.Scale(cell,from_=lo,to=hi,orient='horizontal',variable=self.rank_filter_vars[key],
                      command=lambda _v,k=key:self._rank_filter_moved(k)).pack(fill='x')
        ttk.Checkbutton(box,text='Only buyable now (listing ≤ Max buy)',variable=self.buyable_only,
                        command=lambda:self._rank_filter_moved('buyable')).grid(row=1,column=2,columnspan=2,sticky='w')
        self.significant_only=tk.BooleanVar(value=False)
        ttk.Checkbutton(box,text=f'Only significant Sharpe (FDR ≤ {SIGNIFICANCE_FDR:.0%})',variable=self.significant_only,
                        command=lambda:self._rank_filter_moved('significant')).grid(row=1,column=4,sticky='w')
        self._update_rank_filter_labels()

    def rank_filter_bounds(self):
        """Arguments for filter_ranked_rows; a slider at its end means unbounded."""
        v={k:var.get() for k,var in self.rank_filter_vars.items()}
        liq=int(round(v['liq_min'])); rise=round(v['rise_min']); win=round(v['win_min'])
        return (None if v['price_min']<=0.01 else slider_to_price(v['price_min']),
                None if v['price_max']>=99.99 else slider_to_price(v['price_max']),
                None if v['sharpe_min']<=SHARPE_SLIDER_MIN+0.01 else v['sharpe_min'],
                None if v['sharpe_max']>=SHARPE_SLIDER_MAX-0.01 else v['sharpe_max'],
                None if liq<=0 else liq,
                None if rise<=0 else rise/100.0,
                None if win<=0 else win/100.0,
                self.buyable_only.get(),self.significant_only.get())

    def _update_rank_filter_labels(self):
        pmin,pmax,smin,smax,liq,rise,win,_buyable,_significant=self.rank_filter_bounds()
        self.rank_filter_text['rise_min'].set('any' if rise is None else f'{rise*100:.0f}%')
        self.rank_filter_text['win_min'].set('any' if win is None else f'{win*100:.0f}%')
        self.rank_filter_text['price_min'].set('any' if pmin is None else money(pmin))
        self.rank_filter_text['price_max'].set('no max' if pmax is None else money(pmax))
        self.rank_filter_text['sharpe_min'].set('any' if smin is None else f'{smin:.1f}')
        self.rank_filter_text['sharpe_max'].set('no max' if smax is None else f'{smax:.1f}')
        self.rank_filter_text['liq_min'].set('any' if liq is None else f'{liq} ({liquidity_label(liq)})')

    def _rank_filter_moved(self,key):
        # Keep each min at or below its max by pushing the other slider.
        for lo,hi in (('price_min','price_max'),('sharpe_min','sharpe_max')):
            a,b=self.rank_filter_vars[lo],self.rank_filter_vars[hi]
            if a.get()>b.get(): (b if key==lo else a).set((a if key==lo else b).get())
        self._update_rank_filter_labels()
        if self._rank_filter_job: self.after_cancel(self._rank_filter_job)
        self._rank_filter_job=self.after(150,self._apply_rank_filters)

    def _rank_filter_typed(self,key):
        """Typed limit (e.g. 1.44, $25, any, no max) -> move the matching slider."""
        text=self.rank_filter_text[key].get()
        if key=='liq_min': text=text.split('(')[0]  # accept the displayed "15 (High)" form
        try: value=parse_filter_value(text)
        except ValueError:
            self._update_rank_filter_labels(); return
        if key=='liq_min':
            pos=0.0 if value is None else min(29.0,max(0.0,round(value)))
        elif key in ('rise_min','win_min'):
            pos=0.0 if value is None else min(100.0,max(0.0,value))
        elif key.startswith('price'):
            pos=(0.0 if key=='price_min' else 100.0) if value is None else min(100.0,max(0.0,price_to_slider(max(value,PRICE_SLIDER_MIN))))
        else:
            pos=(SHARPE_SLIDER_MIN if key=='sharpe_min' else SHARPE_SLIDER_MAX) if value is None else min(SHARPE_SLIDER_MAX,max(SHARPE_SLIDER_MIN,value))
        var=self.rank_filter_vars[key]
        if abs(var.get()-pos)<1e-9:
            self._update_rank_filter_labels(); return
        var.set(pos); self._rank_filter_moved(key)

    def _apply_rank_filters(self):
        self._rank_filter_job=None
        if 'diagnostics' in self.ranking_data: self.populate_rankings(self.ranking_data)

    def _visible_rankings(self,data):
        show_excluded=self.show_excluded.get()
        sharpe_rows=data.get('sharpe_all',data['sharpe']) if show_excluded else data['sharpe']
        opportunity_rows=data.get('opportunities_all',data['opportunities']) if show_excluded else data['opportunities']
        bounds=self.rank_filter_bounds()
        return filter_ranked_rows(sharpe_rows,*bounds),filter_ranked_rows(opportunity_rows,*bounds)

    def _build_pricing_controls(self,parent):
        box=ttk.LabelFrame(parent,text=' YOUR COSTS, TARGETS & LIMITS (press Apply after changing) ',padding=(10,4)); box.pack(fill='x',pady=(0,6))
        self.pricing_vars={k:tk.StringVar(value=self.store.get_setting('pricing_'+k,str(v))) for k,v in DEFAULT_PRICING.items()}
        row=ttk.Frame(box); row.pack(fill='x')
        ttk.Button(row,text='Apply',command=self.apply_pricing).pack(side='left',padx=(0,8))
        ttk.Button(row,text='How these are calculated…',command=self.show_model_report).pack(side='left',padx=(0,12))
        ttk.Label(row,text='Horizon (days)',style='Small.TLabel').pack(side='left',padx=(0,4))
        horizon=ttk.Combobox(row,textvariable=self.pricing_vars['horizon'],values=[str(h) for h in FORECAST_HORIZONS],state='readonly',width=4)
        horizon.pack(side='left',padx=(0,12)); horizon.bind('<<ComboboxSelected>>',lambda _e:self.apply_pricing())
        ttk.Button(row,text='Fetch T-bill rate',command=self.fetch_risk_free).pack(side='left')
        # Grouped by topic, a few per line, so the panel fits a laptop screen.
        for title,fields in (('Selling costs',(('Selling fee %','fee_pct',6),('Per-order fee $','fee_fixed',5),('Supplies per card $','cost',6))),
                             ('Shipping',(('Plain shipping $','ship_plain',5),('Tracked shipping $','ship_tracked',5),('Tracked from sale $','ship_threshold',6),
                                          ('Buyer pays shipping $','ship_charge',5),('…on orders under $','free_ship_from',5))),
                             ('Buying',(('Inbound shipping per card bought $','ship_in',5),('Min profit per copy $','min_profit',5),('Min return %','min_roi',5),
                                        ('Target win %','win_pct',5))),
                             ('Money limits',(('Capital $','capital',8),('Max per card $','max_card',7),('Max per set %','max_set_pct',5),
                                              ('Kelly fraction','kelly',5),('Risk-free rate %','risk_free',6))),
                             ('Condition & sales pace',(('LP ×','cond_LP',5),('MP ×','cond_MP',5),('HP ×','cond_HP',5),('DMG ×','cond_DMG',5),
                                                        ('Low counts as NM if ≥ × market','played_ratio',5),('Copies sold per trading day','sell_through',5)))):
            extra=ttk.Frame(box); extra.pack(fill='x',pady=(4,0))
            ttk.Label(extra,text=title,width=20,font=('Helvetica',9,'bold')).pack(side='left')
            for label,key,width in fields:
                ttk.Label(extra,text=label,style='Small.TLabel').pack(side='left',padx=(0,4))
                entry=ttk.Entry(extra,textvariable=self.pricing_vars[key],width=width); entry.pack(side='left',padx=(0,12))
                entry.bind('<Return>',lambda _e:self.apply_pricing())
        for label in [w for w in self._descendants(box) if isinstance(w,ttk.Label) and glossary_lookup(w.cget('text'))]:
            hit=glossary_lookup(label.cget('text'))
            label.bind('<Enter>',lambda _e,h=hit:self.status.set(f'{h[0]}: {h[1]}'))
            label.bind('<Button-1>',lambda _e,t=label.cget('text'):self.explain(t)); label.configure(cursor='question_arrow')
        ttk.Label(box,text='Point at any setting to see what it means in the status bar (click it for the glossary).',style='Small.TLabel').pack(anchor='w',pady=(3,0))
        self.model_note=tk.StringVar(value='Forecast model: builds after the rankings finish.')
        ttk.Label(box,textvariable=self.model_note,style='Small.TLabel',wraplength=1500).pack(anchor='w',pady=(3,0))
        self.pricing=self._read_pricing(show_errors=False) or self.pricing

    def _start_annotation(self):
        """Work out the trade arithmetic for every printing (filters + buy list) in the background."""
        data=self.ranking_data; model=self.forecast_model
        if not model or 'diagnostics' not in data: return
        exposure=portfolio_exposure(self.portfolio_rows)
        key=(id(data),id(model),tuple(sorted(self.pricing.items())),
             tuple(sorted(exposure['cards'].items())),round(exposure['total'],2))
        if key in (self._annotation_key,self._annotation_pending): return
        self._annotation_pending=key; rows=list(data['fresh']); pricing=dict(self.pricing)
        self.rank_progress_text.set('Working out buy/sell prices for every printing (about half a minute after new prices; instant after that)…')
        disk_key=pricing_cache_key(data,model,pricing,exposure,rows)
        def worker():
            try:
                results=load_pricing_cache(disk_key,len(rows))
                if results is None:
                    results=annotate_with_pricing(rows,model,pricing,exposure); save_pricing_cache(disk_key,results)
                self.events.put(('annotated',(key,results)))
            except Exception as exc: self.events.put(('model_error','pricing step: '+str(exc)))
        threading.Thread(target=worker,daemon=True).start()

    def _annotations_current(self):
        return self._annotation_key is not None and self._annotation_key[0]==id(self.ranking_data)

    PRICING_RULES=(('fee_pct','Selling fee %',lambda x:0<=x<100,'0 to 99'),('cost','Supplies per card $',lambda x:x>=0,'0 or more'),
                   ('win_pct','Target win %',lambda x:1<=x<=99,'1 to 99'),('sell_through','Copies sold per trading day',lambda x:0<x<=20,'above 0, up to 20'),
                   ('risk_free','Risk-free rate %',lambda x:-5<=x<=30,'−5 to 30'),('fee_fixed','Per-order fee $',lambda x:x>=0,'0 or more'),
                   ('ship_plain','Plain shipping $',lambda x:x>=0,'0 or more'),('ship_tracked','Tracked shipping $',lambda x:x>=0,'0 or more'),
                   ('ship_threshold','Tracked from sale $',lambda x:x>0,'above 0'),('ship_charge','Buyer pays shipping $',lambda x:x>=0,'0 or more'),
                   ('free_ship_from','…on orders under $',lambda x:x>=0,'0 or more'),('ship_in','Inbound shipping per card bought $',lambda x:x>=0,'0 or more'),
                   ('capital','Capital $',lambda x:x>0,'above 0'),('max_card','Max per card $',lambda x:x>0,'above 0'),
                   ('max_set_pct','Max per set %',lambda x:0<x<=100,'above 0, up to 100'),('kelly','Kelly fraction',lambda x:0<x<=1,'above 0, up to 1 (0.25 is typical)'),
                   ('min_profit','Min profit per copy $',lambda x:x>=0,'0 or more'),('min_roi','Min return %',lambda x:0<=x<=500,'0 to 500'),
                   ('cond_LP','LP ×',lambda x:0<x<=1,'above 0, up to 1'),('cond_MP','MP ×',lambda x:0<x<=1,'above 0, up to 1'),
                   ('cond_HP','HP ×',lambda x:0<x<=1,'above 0, up to 1'),('cond_DMG','DMG ×',lambda x:0<x<=1,'above 0, up to 1'),
                   ('played_ratio','Low counts as NM if ≥ × market',lambda x:0<x<=1,'above 0, up to 1'))
    def _read_pricing(self,show_errors=True):
        labels={k:label for k,label,_ok,_hint in self.PRICING_RULES}; labels['horizon']='Horizon (days)'; problems=[]; v={}
        for k in DEFAULT_PRICING:
            raw=self.pricing_vars[k].get().strip().replace('$','').replace('%','').replace(',','')
            try: v[k]=float(raw)
            except ValueError: problems.append(f"{labels.get(k,k)}: '{raw}' is not a number")
        if not problems:
            v['horizon']=int(v['horizon'])
            if v['horizon'] not in FORECAST_HORIZONS: problems.append('Horizon (days): choose 7, 14 or 30')
            problems+=[f"{label}: must be {hint} (now {v[k]:g})" for k,label,ok,hint in self.PRICING_RULES if k in v and not ok(v[k])]
        if not problems: return v
        if show_errors:
            messagebox.showerror(APP,'Please fix these settings, then press Apply:\n\n'+'\n'.join('• '+x for x in problems))
        return None

    def apply_pricing(self):
        values=self._read_pricing()
        if not values: return
        old=self.pricing; self.pricing=values
        for key,value in values.items(): self.store.setting('pricing_'+key,value)
        if values['horizon']!=old['horizon']:
            self.forecast_model=None; self._ensure_forecast_model()
        if values['risk_free']!=old['risk_free']:
            self.refresh_rankings()  # Sharpe ratios depend on the risk-free rate
        self._repaint_forecasts()

    def _repaint_forecasts(self):
        if hasattr(self,'trade_tree'): self.load_trades(); self.load_backtest_view()
        if 'diagnostics' in self.ranking_data: self.populate_rankings(self.ranking_data)
        if self.history_id.get(): self.load_history()
        self._start_annotation()

    def fetch_risk_free(self):
        def worker():
            try: self.events.put(('risk_free',fetch_risk_free_rate()))
            except Exception as exc: self.events.put(('risk_free_error',str(exc)))
        self.status.set('Fetching the 3-month Treasury bill rate from FRED…')
        threading.Thread(target=worker,daemon=True).start()

    def _ensure_forecast_model(self):
        """Load today's cached model for the chosen horizon, or build it in the background."""
        dates=[r['latest_date'] for r in self.ranking_data.get('fresh',[]) if r.get('latest_date')]
        if not dates or self.model_busy: return
        data_date=max(dates); horizon=self.pricing['horizon']; model=self.forecast_model
        if model and model['horizon']==horizon and model['data_date']==data_date: return
        self.model_busy=True
        self.model_note.set(f'Forecast model: preparing the {horizon}-day model (first build after new data takes a few minutes)…')
        def worker():
            try:
                built=load_forecast_model(horizon,data_date)
                if built is None:
                    # All horizons in one pass, so switching horizon later is instant.
                    progress=lambda current,total,phase: self.events.put(('rank_progress',(current,total,phase)))
                    ensure_daily_history(self.store,lambda msg: progress(0,0,msg))
                    with ReadOnlyStore() as reader:
                        models=build_forecast_models(reader,FORECAST_HORIZONS,data_date,progress)
                    for model in models.values(): save_forecast_model(model)
                    built=models[horizon]
                self.events.put(('model_ready',built))
            except Exception as exc:
                self.events.put(('model_error',str(exc)))
        threading.Thread(target=worker,daemon=True).start()

    def _model_summary(self,model):
        bt=model.get('backtest')
        head=f"Forecast: {model['horizon']}-day estimates learned from {model['samples']:,} past price moves up to {model['data_date']}"
        if not bt:
            return head+' · not enough history yet to test this horizon on cases it has not seen.'
        skill=bt.get('brier_skill'); recent=bt.get('recent_half')
        plain=(f"{abs(skill)*100:.1f}% {'more' if skill>0 else 'less'} accurate than a plain average" if skill is not None else
               ('more accurate than a plain average' if bt['brier_model']<bt['brier_baseline'] else 'NOT better than a plain average'))
        text=(f"{head} · tested on {bt['test_samples']:,} recent cases it had not seen: {plain} "
              f"(Brier {bt['brier_model']:.4f} vs {bt['brier_baseline']:.4f}; lower is better)")
        if recent:
            text+=(f" · calibration {'ON' if bt.get('calibrated') else 'off'}: newest cases {recent['raw']:.4f} raw → "
                   f"{recent['calibrated']:.4f} calibrated")
        return text+'. Estimates, not guarantees.'

    def show_model_report(self):
        p=self.pricing; lines=[]
        model=self.forecast_model
        lines.append(self._model_summary(model) if model else 'Forecast model not ready yet (it builds after the rankings finish).')
        bt=model.get('backtest') if model else None
        if bt:
            lines+=['','Calibration on held-out cases before recalibration (predicted chance of a price rise vs what happened):']
            lines+=[f'  predicted {lo*100:.0f}–{hi*100:.0f}%: {n:,} cases, predicted {pm*100:.0f}%, actual {act*100:.0f}%'
                    for lo,hi,n,pm,act in bt['calibration']]
            if bt.get('calibrated'):
                lines.append('  Recalibration (isotonic, fitted on the older half of the test window and checked on the newer half) is applied to every probability and price range shown.')
        lines+=['','How the numbers are derived:',
                f"• Forecast: what past printings with a similar 30-day and 7-day trend, price tier, finish, liquidity, volatility variant (Borderless, Serial Numbered, Special Illustration Rare, ...) and, for cards under 90 days old, release phase did over the next {p['horizon']} days.",
                f"  Thin groups are shrunk toward broader ones ({FORECAST_PRIOR} pseudo-observations), which keeps small groups from looking overconfident.",
                '  Ranges like 58% (51–65) are ~90% intervals using the effective sample size (overlapping windows counted once). They cover sampling noise only, not market-wide shocks.',
                '• Liquidity: days in the last 30 on which the market price changed (it changes when copies sell). TCGCSV has no sales counts, so this is a proxy.',
                f"• Chance it sells: 1 − e^(−trading days × {p['horizon']}/30 × {p['sell_through']:g} copies per trading day) (Poisson sales).",
                f"• Costs per sale: {p['fee_pct']:g}% + ${p['fee_fixed']:.2f} per order, outgoing shipping ${p['ship_plain']:.2f} (${p['ship_tracked']:.2f} tracked "
                f"for sales of ${p['ship_threshold']:g}+; buyers pay ${p['ship_charge']:.2f} on orders under ${p['free_ship_from']:g}), ${p['cost']:.2f} supplies; "
                f"${p['ship_in']:.2f} inbound shipping per card bought.",
                f"• Win @ low: chance it sells × chance the forecast sale, after those costs, beats buying at the cheapest listing.",
                f"• Condition: TCGCSV's cheapest listing covers every condition. A listing under {p['played_ratio']:g}× market is assumed played and valued",
                f"  as the condition its discount matches (LP {p['cond_LP']:g}×, MP {p['cond_MP']:g}×, HP {p['cond_HP']:g}×, DMG {p['cond_DMG']:g}× of Near Mint). Confirm condition before buying.",
                f"• Max buy: the highest buy price per condition that keeps Win % at {p['win_pct']:g}%. It sits below market because a resale gives up fees and costs;",
                '  treat it as your buylist price (trade-ins, collections, underpriced listings). Blank = no price reaches the target.',
                '• Sellable qty: the most copies with at least an even chance of all selling within the horizon (Poisson median).',
                f"• Suggested qty: the smallest of {p['kelly']:g}× the Kelly stake on {money(p['capital'])} capital, your {money(p['max_card'])} per-card and "
                f"{p['max_set_pct']:g}% per-set limits (minus what you hold), the remaining budget and the sellable qty.",
                '• Break-even sell: what a sale must fetch to cover buying at the cheapest listing plus every cost.',
                '• Target sell (list at): the asking price with the highest expected profit = chance the market reaches it within the horizon',
                '  (calibrated forecast × chance it trades) × profit after costs at that price. Higher asks earn more per sale but sell less often.',
                '  Quick sale: just under the cheapest Near Mint listing.',
                f"• Sharpe: 30-day daily log returns minus the {p['risk_free']:g}% T-bill rate, annualized with a Newey–West long-run variance",
                f'  ({SHARPE_NW_LAGS} lags), because TCGplayer market prices are smoothed averages whose returns are autocorrelated; naive √365 scaling overstates them.',
                '• P(SR>0): Probabilistic Sharpe Ratio — chance the true Sharpe is above zero given sample length, skew and fat tails.',
                f'  With ~200,000 printings tested, some look great by luck; ✓ marks those still significant after a Benjamini–Hochberg false-discovery-rate cut of {SIGNIFICANCE_FDR:.0%}.',
                '  Sharpe still ignores fees: a smooth riser can lose money after the selling fee. Use Win @ low and Max buy for trade decisions.',
                '• Market indices: chained daily cross-section of one-day moves of $1+ printings; equal-weighted (each move capped at ±25%) or price-weighted (one copy of each).',
                '• Portfolio signals: SELL when a quick sale now nets more after costs than the forecast mean at the horizon; TRIM when you hold more than is expected to sell.',
                '','These are statistical estimates from about three months of cached TCGplayer prices, not guarantees or financial advice.']
        messagebox.showinfo(APP,'\n'.join(lines))

    def _row_pricing(self,r):
        fc=forecast_for(self.forecast_model,r.get('return_30d'),r.get('return_7d'),r.get('latest_price'),r.get('printing',''),
                        r.get('price_changes_30d'),r.get('return_sd_30d'),r.get('variant'),r.get('days_since_release'))
        if not fc: return None
        return pricing_targets(r['latest_price'],r.get('low_price'),fc,self.pricing,r.get('price_changes_30d'))

    def _pricing_cells(self,r):
        """(Liquidity, Win %, Max buy, Max qty) display cells for a ranking row."""
        changes=r.get('price_changes_30d')
        liq='—' if changes is None else f'{changes} {liquidity_label(changes)}'
        t=self._row_pricing(r)
        if not t: return liq,'—','—','—'
        win=t['win_at_low'] if t['win_at_low'] is not None else t['win_at_market']
        return liq,f'{win*100:.0f}%',money(t['max_buy']) if t['max_buy'] else 'none','—' if t['max_qty'] is None else str(t['max_qty'])

    def _fmt_psr(self,r):
        psr=r.get('psr')
        return '—' if psr is None else f"{min(psr,0.999)*100:.1f}%"+(' ✓' if self._significant(r) else '')
    def _significant(self,r):
        return r.get('fdr_q') is not None and r['fdr_q']<=SIGNIFICANCE_FDR and (r.get('sharpe_30d') or 0)>0
    def _fmt_pct(self,value):
        return '—' if value is None else f'{value:+.1f}%'

    def refresh_rankings(self, force=False):
        """Show rankings: unchanged data keeps what is shown, saved results load in seconds,
        and only new data (or force, the Refresh button) triggers the multi-minute recalculation."""
        if not hasattr(self,'ranking_note') or self.rankings_busy: return
        risk_free=self.pricing['risk_free']/100.0
        signature=rankings_signature(self.store,risk_free)
        if not force and self.ranking_data.get('signature')==signature: return
        self.rankings_busy=True
        self.rank_refresh_button.configure(state='disabled')
        self.ranking_note.set('Loading saved rankings…' if not force else 'Calculating rankings from recent daily price observations…')
        self.rank_progress.stop(); self.rank_progress.configure(mode='indeterminate'); self.rank_progress.start(12)
        self.rank_progress_text.set('Loading saved rankings…' if not force else 'Starting ranking calculation…')
        def worker():
            try:
                ensure_daily_history(self.store,lambda msg: self.events.put(('rank_progress',(0,0,msg))))
                data=None if force else load_rankings(signature)
                if data is None:
                    self.events.put(('rank_progress',(0,0,'Data changed since the last calculation; recalculating…')))
                    progress=lambda current,total,phase: self.events.put(('rank_progress',(current,total,phase)))
                    try:
                        data,_models=compute_market_views(self.store,risk_free,progress); data['saved_at']=utc()
                    except OSError:  # could not save: still usable this session, recalculated next launch
                        with ReadOnlyStore() as reader:
                            data=build_market_rankings(reader,progress=progress,risk_free=risk_free)
                data['signature']=signature
                self.events.put(('rankings_done',data))
            except Exception as exc:
                self.events.put(('rankings_error',str(exc)))
        threading.Thread(target=worker,daemon=True).start()

    def populate_rankings(self,data):
        self.ranking_data=data
        self.clear(self.sharpe_tree); self.clear(self.opportunity_tree)
        show_excluded=self.show_excluded.get()
        sharpe_rows,opportunity_rows=self._visible_rankings(data)
        for r in sharpe_rows[:100]:
            self.sharpe_tree.insert('','end',values=(f"{r['card_id']}#{r['price_type']}",r['name'],r['game'],money(r['latest_price']),
                money(r.get('low_price')),f"{r['sharpe_30d']:.2f}",self._fmt_psr(r),self._fmt_pct(r['return_30d']),*self._pricing_cells(r),
                ', '.join(r.get('flags') or [])),tags=('up' if self._significant(r) else '',))
        # When no score is supportable yet, show real cards being tracked instead of
        # leaving both tables blank. These rows are explicitly marked Needs history.
        visible_opportunities=opportunity_rows[:100]
        fallback_mode=not data['opportunities'] and bool(data['fresh'])
        if fallback_mode:
            tracked=[r for r in data['fresh'] if show_excluded or not r.get('flags')]
            visible_opportunities=sorted(tracked,key=lambda r:(-r['observations'],r['name'].casefold()))[:30]
        for r in visible_opportunities:
            scored=r['opportunity_score'] is not None
            state=('30d Sharpe' if r['sharpe_30d'] is not None else 'Provisional') if scored else 'Needs history'
            if r.get('flags'): state=', '.join(r['flags'])
            self.opportunity_tree.insert('','end',values=(f"{r['card_id']}#{r['price_type']}",r['name'],r['game'],money(r['latest_price']),
                money(r.get('low_price')),f"{r['opportunity_score']:.0f}" if scored else '—',self._fmt_pct(r['return_7d']),self._fmt_pct(r['return_30d']),
                *self._pricing_cells(r),state))
        fresh=len(data['fresh']); sharp=len(data['sharpe']); opp=len(data['opportunities'])
        excluded=len(data.get('excluded',[]))
        if sharpe_rows:
            self.sharpe_empty_label.pack_forget()
        else:
            self.sharpe_empty_text.set('No cards match the current filters.' if sharp else
                'No valid Sharpe ratios yet. Requires at least 28 of the last 30 days observed and at least 20 consecutive daily returns.')
            self.sharpe_empty_label.pack(anchor='w',fill='x',pady=(0,5))
        diag=data.get('diagnostics',{})
        if fresh and not sharp and not opp:
            note=(f'{fresh:,} currently priced singles found. The right table lists cards being tracked, not ranked buys. '
                  'Scores stay blank until at least 8 daily observations and a usable return window; 30-day Sharpe needs '
                  'at least 28 of the last 30 days observed plus 20 consecutive daily returns. No values are invented.')
        elif not fresh:
            latest=diag.get('latest_market_source_time') or 'none'
            if not diag.get('market_prices'):
                note=(f"No TCGCSV market-price rows are stored yet ({diag.get('total_cards',0):,} catalog records; "
                      f"{diag.get('total_prices',0):,} total price rows). Finish a successful sync and check whether the source returned prices.")
            elif not diag.get('recent_market_prices'):
                note=(f"Found {diag.get('market_prices',0):,} TCGCSV market-price rows, but none in the recent 35-day window. "
                      f'Latest stored source timestamp: {latest}. Check the sync log and source timestamps.')
            else:
                note=(f"Found {diag.get('recent_market_prices',0):,} recent TCGCSV market-price rows, but none matched cards "
                      f"classified as singles. Catalog item types: {diag.get('item_types',{})}. This points to a classification/data-link issue.")
        else:
            note=(f'{fresh:,} current priced singles | {len(sharpe_rows):,} Sharpe and {len(opportunity_rows):,} opportunity rows match the filters. '
                  'Cached market prices are estimates, not verified sale prices; score is not a buy signal.')
        if excluded and not show_excluded:
            note+=(f' {excluded:,} cards excluded as likely artifacts: under ${RANK_MIN_PRICE:,.0f}, market price '
                   f'{SPIKE_MARKET_TO_LOW:g}× or more above the cheapest listing or under {SPIKE_LOW_TO_MARKET:.0%} of it, '
                   f'or a 30-day rise of {SPIKE_MIN_RETURN_30D:g}%+ mostly from one day.')
        bounds=self.rank_filter_bounds()
        sig=sum(1 for r in data.get('sharpe',[]) if self._significant(r))
        if sig: note+=f' {sig:,} positive Sharpes are statistically significant (FDR ≤ {SIGNIFICANCE_FDR:.0%}, ✓).'
        if (bounds[5] is not None or bounds[6] is not None or bounds[7]) and not self._annotations_current():
            note+=' Chance-of-rise, Win and buyable-now filters apply once buy/sell prices are worked out (shortly after the forecast loads).'
        self.ranking_note.set(note)

    def open_ranked_history(self,tree):
        selected=tree.selection()
        if not selected: return
        values=tree.item(selected[0],'values')
        if not values: return
        # Ranking rows are keyed "card_id#price_type" so the chosen printing is the one charted.
        cid,_,price_type=str(values[0]).partition('#')
        self.history_series=price_type or None
        self.history_id.set(cid); self.nb.select(self.tabs['Market History']); self.load_history()


    def export_rankings(self):
        if 'diagnostics' not in self.ranking_data:
            messagebox.showinfo(APP,'Rankings have not been calculated yet.'); return
        rows=[]
        for label,visible in zip(('Sharpe','Opportunity'),self._visible_rankings(self.ranking_data)):
            for r in visible[:1000]:
                t=self._row_pricing(r) or {}
                rows.append((label,r['card_id'],r['game'],r['name'],r['price_type'],r['latest_price'],r.get('low_price'),
                    r['sharpe_30d'],r['return_7d'],r['return_30d'],r['drawdown_30d'],
                    r['opportunity_score'],r.get('psr'),r.get('fdr_q'),r.get('autocorr_1'),r['observations'],r['obs_30d'],r['age_days'],
                    r.get('price_changes_30d'),t.get('liquidity'),t.get('p_sold'),t.get('p_rise'),t.get('median_price'),
                    t.get('win_at_low'),t.get('max_buy'),t.get('max_qty'),t.get('min_sell'),t.get('target_sell'),t.get('quick_sell'),
                    '; '.join(r.get('flags') or [])))
        self.save_csv(['ranking','card_id','game','name','price_type','latest_price_usd','low_listing_usd','sharpe_30d',
            'return_7d_pct','return_30d_pct','drawdown_30d_pct','opportunity_score','prob_sharpe_positive','fdr_q_value',
            'return_autocorr_lag1','observations_35d',
            'observations_30d','data_age_days','price_change_days_30d','liquidity','chance_sells','chance_price_rises',
            'forecast_median_price','win_prob_at_low','max_buy','max_qty','min_sell','target_sell','quick_sale',
            'excluded_reason'],rows,'market_rankings.csv')

    def collector_tab(self):
        p=self.tabs['Collectors']; self.section(p,'Market data','Covers Magic: The Gathering, Pokémon, One Piece and Riftbound. TCGCSV supplies daily TCGplayer prices; historical archives are optional and downloaded only when requested.')
        ttk.Label(p,text='Daily sync checks last-updated.txt first and skips unchanged data. It imports market/low/mid/high/direct-low prices for every supported game. Historical archives begin 2024-02-08 and require the 7-Zip command-line tool. A 45-day backfill is typically tens to a few hundred MB depending on source archive sizes; downloaded archives are discarded after import, and completed dates are remembered.',style='Small.TLabel',wraplength=940).pack(anchor='w',pady=(0,8))
        history=ttk.LabelFrame(p,text=' HISTORICAL PRICE BACKFILL ',padding=8); history.pack(fill='x',pady=(0,8))
        today=datetime.now(timezone.utc).date()
        default_end=today-timedelta(days=1); default_start=default_end-timedelta(days=44)
        self.backfill_start=tk.StringVar(value=f'{default_start:%m/%d/%Y}'); self.backfill_end=tk.StringVar(value=f'{default_end:%m/%d/%Y}')
        ttk.Label(history,text='Start (e.g. 9/1/2026)').pack(side='left',padx=(0,5))
        ttk.Entry(history,textvariable=self.backfill_start,width=12).pack(side='left',padx=(0,12))
        ttk.Label(history,text='End').pack(side='left',padx=(0,5))
        ttk.Entry(history,textvariable=self.backfill_end,width=12).pack(side='left',padx=(0,12))
        ttk.Button(history,text='Backfill historical prices',command=self.start_history_backfill).pack(side='left')
        mtgjson=ttk.LabelFrame(p,text=' MTG PRICE HISTORY (MTGJSON) ',padding=8); mtgjson.pack(fill='x',pady=(0,8))
        ttk.Button(mtgjson,text='Import last 90 days of MTG prices',command=self.start_mtgjson_import).pack(side='left')
        ttk.Label(mtgjson,text='Free MTGJSON TCGplayer history, matched to your synced MTG catalog. About a 60 MB download; run once (re-running only fills gaps). Pokémon is not covered.',style='Small.TLabel',wraplength=620).pack(side='left',padx=10)
        ttk.Label(p,text='Recent collection runs',font=('Helvetica',12,'bold')).pack(anchor='w')
        self.jobtree=self.gridview(p,('Time','Collector','Status','Records','Details'),4)
        self.log=tk.Text(p,height=10,bg='#0b1726',fg='#bcd8f2',insertbackground='white',wrap='word'); self.log.pack(fill='both',expand=True,pady=8)

    def start_history_backfill(self):
        if self.busy:
            messagebox.showinfo(APP,'A collector is already running. Wait for it to finish before starting historical backfill.'); return
        start=self.backfill_start.get().strip(); end=self.backfill_end.get().strip()
        try:
            iso_start,iso_end=parse_trade_date(start),parse_trade_date(end)
            if not iso_start or not iso_end: raise ValueError('Type dates like 10/29/2026, and not in the future.')
            start,end=iso_start,iso_end; start_day=date.fromisoformat(start); end_day=date.fromisoformat(end)
            if start_day < HISTORY_ARCHIVE_FIRST_DATE: raise ValueError(f'The archives start on {HISTORY_ARCHIVE_FIRST_DATE:%m/%d/%Y}.')
            if end_day < start_day: raise ValueError('End date must be on or after start date.')
            days=(end_day-start_day).days+1
            if days > 90:
                if not messagebox.askyesno(APP,f'This will process {days:,} daily archives. The full historical archive collection is around 1 GB; this range could transfer hundreds of MB. Continue?'): return
            elif not messagebox.askyesno(APP,f'This will download up to {days:,} daily archive files for every supported game. Each file is usually a few MB. 7-Zip must be installed. Already imported dates will be skipped. Continue?'): return
        except ValueError as exc:
            messagebox.showerror(APP,'Please check the dates. '+str(exc)); return
        def work(report): return backfill_tcgcsv_history(self.store,report,start,end)
        self.launch('TCGCSV historical price backfill',work)
    def start_mtgjson_import(self):
        if self.busy:
            messagebox.showinfo(APP,'Another download or job is still running — wait for it to finish (progress is shown at the bottom of the window).'); return
        if not messagebox.askyesno(APP,'Download MTGJSON card identifiers (~11 MB) and its 90-day price file (~45 MB) and import TCGplayer market history for MTG cards already in your catalog? Pokémon is not covered by MTGJSON. This takes a few minutes.'):
            return
        self.launch('MTGJSON 90-day MTG price history',lambda report: backfill_mtgjson_history(self.store,report))
    def settings_tab(self):
        p=self.tabs['Settings']
        ttk.Label(p,text='Settings',font=('Helvetica',16,'bold')).pack(anchor='w',pady=(4,4))
        self._build_pricing_controls(p)
        self.advanced_var=tk.BooleanVar(value=self.store.get_setting('advanced_tabs','0')=='1')
        ttk.Checkbutton(p,text='Show advanced tabs (market monitor, Sharpe rankings, data collectors)',variable=self.advanced_var,
                        command=self._apply_advanced).pack(anchor='w',pady=(4,4))
        self.section(p,'Data and safety','Everything runs on this computer: no account, no paid services, and nothing is ever bought or sold for you.')
        for label,value in [('Database',str(DB)),('Storage folder',str(ROOT)),('Daily market source','TCGCSV (MTG, Pokémon, One Piece, Riftbound)'),('Collection cadence','Daily; downloads only when new prices are published'),('Background sync','Optional macOS LaunchAgent or Windows scheduled task; works while the GUI is closed'),('Historical archive','TCGCSV archive (from 2024-02-08, needs 7-Zip) is offline; checked weekly and backfilled automatically when it returns. MTG history via the MTGJSON import in Collectors'),('External purchases','Disabled'),('Paid APIs','None. Free sources only: TCGCSV, MTGJSON (TCGplayer, Card Kingdom buylist, Cardmarket), Scryfall (sets, legality, EDHREC), FRED (T-bill, EUR/USD), and a small weekly PriceCharting sample (monthly history, 3 s between requests)')]:
            ttk.Label(p,text=f'{label}:  {value}',style='Small.TLabel',wraplength=1300).pack(anchor='w',pady=1)
        tools=ttk.Frame(p); tools.pack(anchor='w',pady=(8,0))
        ttk.Button(tools,text='Make a portable copy…',command=self.make_portable).pack(side='left',padx=(0,8))
        ttk.Button(tools,text='Export all cards to CSV',command=self.export_cards).pack(side='left',padx=(0,8))
        ttk.Button(tools,text='Open storage folder',command=self.open_folder).pack(side='left')
        portable=ROOT.parent==Path(__file__).resolve().parent
        ttk.Label(p,text=('Running as a portable copy: data is in the folder next to this script.' if portable else
                          'To move to another computer: Make a portable copy… onto a USB drive or external disk, then run the script from there.'),
                  style='Small.TLabel').pack(anchor='w',pady=(4,0))
        if sys.platform == 'darwin':
            row=ttk.Frame(p); row.pack(anchor='w',pady=(12,0))
            ttk.Button(row,text='Enable daily background sync',command=self.install_launch_agent).pack(side='left',padx=(0,8))
            ttk.Button(row,text='Disable background sync',command=self.remove_launch_agent).pack(side='left')
        elif sys.platform.startswith('win'):
            row=ttk.Frame(p); row.pack(anchor='w',pady=(12,0))
            ttk.Button(row,text='Enable daily background sync',command=self.install_windows_task).pack(side='left',padx=(0,8))
            ttk.Button(row,text='Disable background sync',command=self.remove_windows_task).pack(side='left')
            self.bg_note=tk.StringVar(value='')
            ttk.Label(row,textvariable=self.bg_note,style='Small.TLabel').pack(side='left',padx=(12,0))
            self._refresh_bg_note()
        self._upkeep_controls(p)
        if sys.platform.startswith('win'):
            self.notify_var=tk.BooleanVar(value=self.store.get_setting('notify_after_sync','1')=='1')
            ttk.Checkbutton(p,text='After each background sync, write the daily brief and show a Windows notification',variable=self.notify_var,
                            command=lambda:self.store.setting('notify_after_sync','1' if self.notify_var.get() else '0')).pack(anchor='w',pady=(10,0))
    def _upkeep_controls(self,p):
        box=ttk.LabelFrame(p,text=' DATA UPKEEP & OPTIONAL MODULES ',padding=8); box.pack(fill='x',pady=(12,0))
        self.cardmarket_var=tk.BooleanVar(value=self.cardmarket_on())
        ttk.Checkbutton(box,text='Cardmarket (EU) module: show EU prices in USD and flag cards rising in Europe before the US (signal only; MTG via MTGJSON)',
                        variable=self.cardmarket_var,command=self._toggle_cardmarket).pack(anchor='w')
        row=ttk.Frame(box); row.pack(fill='x',pady=(6,0))
        ttk.Label(row,text='Keep detailed daily price rows for (days, 0 = forever)',style='Small.TLabel').pack(side='left',padx=(0,4))
        self.retention_var=tk.StringVar(value=self.store.get_setting('raw_retention_days',str(RAW_RETENTION_DAYS)))
        ttk.Entry(row,textvariable=self.retention_var,width=6).pack(side='left',padx=(0,8))
        ttk.Button(row,text='Save',command=self._save_retention).pack(side='left',padx=(0,16))
        ttk.Button(row,text='Back up & tidy now',command=self._run_upkeep).pack(side='left')
        self.upkeep_note=tk.StringVar(value=f"Weekly with the background sync: backup of portfolio, trades, settings and the daily price history to "
                                            f"{ROOT/'backups'/'essentials.sqlite3'} (last: {self.store.get_setting('backup_at','never')}); "
                                            "raw rows older than the window are dropped (market and cheapest-listing prices are kept forever).")
        ttk.Label(box,textvariable=self.upkeep_note,style='Small.TLabel',wraplength=1200).pack(anchor='w',pady=(4,0))
    def _toggle_cardmarket(self):
        self.store.setting('cardmarket_module','1' if self.cardmarket_var.get() else '0')
        if self.cardmarket_var.get():
            threading.Thread(target=lambda: (refresh_fx(self.store),),daemon=True).start()
        self.populate_buy_list()
    def _save_retention(self):
        try: days=int(self.retention_var.get())
        except ValueError: messagebox.showerror(APP,'Enter a whole number of days (0 keeps raw rows forever).'); return
        if days and days<60: messagebox.showerror(APP,'Keep at least 60 days of raw rows (or 0 for forever).'); return
        self.store.setting('raw_retention_days',days); self.status.set(f'Raw TCGCSV rows kept for {days or "all"} days')
    def _run_upkeep(self):
        self.launch('Backup and database upkeep',lambda report: run_maintenance(self.store,report))
    def make_portable(self):
        folder=filedialog.askdirectory(title='Choose an empty folder for the portable copy (e.g. on a USB drive)')
        if not folder: return
        need=portable_size_estimate(); gb=lambda b: f'{b/1024**3:.1f} GB'
        try: free=shutil.disk_usage(folder).free
        except OSError: free=None
        if free is not None and free<need:
            messagebox.showerror(APP,f'Not enough space there: the copy can take up to {gb(need)} and that drive has {gb(free)} free. '
                                     'Choose a bigger drive, or free up space and try again.'); return
        fs=volume_format(folder)
        if fs and fs.upper().startswith('FAT') and need>FAT32_MAX_FILE:
            if not messagebox.askyesno(APP,f'That drive is formatted {fs}, which cannot hold a single file over 4 GB, and your price database '
                                           f'may be bigger than that. The copy will probably fail partway.\n\nTip: use a drive formatted exFAT or NTFS '
                                           '(Windows can reformat a USB drive: right-click it in File Explorer > Format; this erases it).\n\nTry anyway?'): return
        if not messagebox.askyesno(APP,f'Write a portable copy (the app, your portfolio, trades, settings and price history; up to {gb(need)}) to:\n{folder}\n\n'
                                       'This takes several minutes. Use one computer at a time with it.'): return
        self.launch('Portable copy',lambda report: make_portable_copy(self.store,folder,report))
    ADVANCED_TABS=('Overview','Sharpe & Opportunities','Collectors')
    def _apply_advanced(self):
        show=self.advanced_var.get(); self.store.setting('advanced_tabs','1' if show else '0')
        for name in self.ADVANCED_TABS:
            if show: self.nb.add(self.tabs[name])
            else: self.nb.hide(self.tabs[name])
    def install_windows_task(self):
        times=' and '.join(datetime.strptime(t,'%H:%M').strftime('%I:%M %p').lstrip('0') for t in WINDOWS_TASK_TIMES)
        if not messagebox.askyesno(APP,f'Create a Windows scheduled task that runs the TCGCSV daily sync at {times} local time, even when this app is closed? '
                'A run missed while the PC was off or asleep starts as soon as possible afterwards. It runs while you are signed in to Windows (no password is stored). '
                'Keep this script at its current path. No purchases are made.'):
            return
        try:
            install_windows_sync_task(windowless_python(),Path(__file__).resolve(),data=ROOT.resolve())
            self.status.set('Daily background sync enabled (Windows Task Scheduler)'); self._refresh_bg_note()
            messagebox.showinfo(APP,f'Daily background sync is enabled as the scheduled task "{WINDOWS_TASK_NAME}".\nOutput log: {ROOT/"daily-sync.log"}\nError log: {ROOT/"daily-sync-error.log"}')
        except Exception as e:
            messagebox.showerror(APP,'Could not enable daily background sync:\n'+str(e))
    def _refresh_bg_note(self):
        def worker():
            on=windows_sync_task_installed()
            text={True:'Status: ON (prices update every day, even when this app is closed)',
                  False:'Status: OFF (prices update only while this app is open)',None:''}[on]
            self.events.put(('bg_note',text))  # Tk calls belong to the main thread
        threading.Thread(target=worker,daemon=True).start()
    def remove_windows_task(self):
        try:
            remove_windows_sync_task()
            self.status.set('Daily background sync disabled'); self._refresh_bg_note()
            messagebox.showinfo(APP,'Daily background sync has been disabled.')
        except Exception as e:
            messagebox.showerror(APP,'Could not disable daily background sync:\n'+str(e))
    def launch_agent_file(self):
        return Path.home()/'Library'/'LaunchAgents'/'com.cardmarketterminal.daily-sync.plist'
    def install_launch_agent(self):
        if sys.platform != 'darwin':
            messagebox.showinfo(APP,'Background LaunchAgent setup is available on macOS only.'); return
        if not messagebox.askyesno(APP,'Install a macOS user LaunchAgent that runs the TCGCSV daily sync at 2:30 PM local time, even when the GUI is closed? It uses this script and the same local database. Keep this script at its current path after installation. No purchases are made.'):
            return
        try:
            script=Path(__file__).resolve()
            python=Path(sys.executable).resolve()
            if not script.is_file() or not python.exists():
                raise RuntimeError('Could not resolve the script or Python interpreter path.')
            agent=self.launch_agent_file(); agent.parent.mkdir(parents=True,exist_ok=True)
            log_path=ROOT/'daily-sync.log'
            error_log_path=ROOT/'daily-sync-error.log'
            payload={
                'Label':'com.cardmarketterminal.daily-sync',
                'ProgramArguments':[str(python),str(script),'--sync'],
                'EnvironmentVariables':{'CMT_DATA':str(ROOT.resolve())},  # same data folder as this session, whatever the shell had
                'StartCalendarInterval':{'Hour':14,'Minute':30},
                'RunAtLoad':False,
                'StandardOutPath':str(log_path),
                'StandardErrorPath':str(error_log_path),
                'ProcessType':'Background'
            }
            tmp=agent.with_suffix('.plist.partial')
            with open(tmp,'wb') as f: plistlib.dump(payload,f)
            tmp.replace(agent)
            domain=f'gui/{os.getuid()}'
            subprocess.run(['launchctl','bootout',domain,str(agent)],capture_output=True,text=True,check=False)
            result=subprocess.run(['launchctl','bootstrap',domain,str(agent)],capture_output=True,text=True,check=False)
            if result.returncode != 0:
                raise RuntimeError('LaunchAgent file was written but launchctl could not load it: '+(result.stderr.strip() or result.stdout.strip()))
            self.status.set('Daily background sync enabled for 2:30 PM local time')
            messagebox.showinfo(APP,'Daily background sync is enabled. Output log: '+str(log_path)+'\nError log: '+str(error_log_path))
        except Exception as e:
            messagebox.showerror(APP,'Could not enable daily background sync:\n'+str(e))
    def remove_launch_agent(self):
        if sys.platform != 'darwin': return
        agent=self.launch_agent_file(); domain=f'gui/{os.getuid()}'
        try:
            result=subprocess.run(['launchctl','bootout',domain,str(agent)],capture_output=True,text=True,check=False)
            err=(result.stderr+' '+result.stdout).lower()
            if result.returncode != 0 and agent.exists() and not any(x in err for x in ('could not find service','service not found','no such process')):
                raise RuntimeError(result.stderr.strip() or result.stdout.strip() or 'launchctl bootout failed')
            if agent.exists(): agent.unlink()
            self.status.set('Daily background sync disabled')
            messagebox.showinfo(APP,'Daily background sync has been disabled.')
        except Exception as e:
            messagebox.showerror(APP,'Could not disable daily background sync:\n'+str(e))
    def begin_activity(self,label):
        self.activity_progress.stop()
        self.activity_progress.configure(mode='indeterminate')
        self.activity_progress.start(12)
        self.activity_text.set('Working: '+label)

    def set_activity_progress(self,current,total,phase):
        if total and total > 0:
            self.activity_progress.stop()
            self.activity_progress.configure(mode='determinate',maximum=total)
            self.activity_progress['value']=max(0,min(current,total))
            pct=100.0*max(0,min(current,total))/total
            self.activity_text.set(f'{phase}: {current:,}/{total:,} ({pct:.0f}%)')
        else:
            self.activity_progress.stop()
            self.activity_progress.configure(mode='indeterminate')
            self.activity_progress.start(12)
            self.activity_text.set(str(phase))

    def end_activity(self,label,success=True):
        self.activity_progress.stop()
        self.activity_progress.configure(mode='determinate',maximum=1)
        self.activity_progress['value']=1 if success else 0
        self.activity_text.set(('Complete: ' if success else 'Failed: ')+label)

    def handle_async_event(self,op,payload):
        if op=='bg_note':
            self.bg_note.set(payload)
        elif op=='kpis':
            self.kpis.config(text=payload)
        elif op=='progress':
            self.set_activity_progress(*payload)
        elif op=='rank_progress':
            current,total,phase=payload
            if total and total>0:
                self.rank_progress.stop(); self.rank_progress.configure(mode='determinate',maximum=total)
                self.rank_progress['value']=max(0,min(current,total))
                pct=100.0*max(0,min(current,total))/total
                self.rank_progress_text.set(f'{phase}: {current:,}/{total:,} ({pct:.0f}%)')
            else:
                if str(self.rank_progress.cget('mode'))!='indeterminate':
                    self.rank_progress.configure(mode='indeterminate'); self.rank_progress.start(12)
                self.rank_progress_text.set(phase)
        elif op=='rankings_done':
            self.rankings_busy=False
            self.rank_refresh_button.configure(state='normal')
            self.rank_progress.stop(); self.rank_progress.configure(mode='determinate',maximum=1); self.rank_progress['value']=1
            saved=str(payload.get('saved_at') or '')[:16].replace('T',' ')
            self.rank_progress_text.set(f'Rankings ready (calculated {saved} UTC)' if saved else 'Rankings ready')
            self._index_rows(payload)
            self.populate_rankings(payload); self.refresh_views(); self._load_card_facts()
            self._ensure_forecast_model()
            self._start_annotation()  # same model, new rankings
        elif op=='annotated':
            key,results=payload
            if key!=self._annotation_pending or key[0]!=id(self.ranking_data): return  # superseded
            for row,values in zip(self.ranking_data['fresh'],results): row.update(values)
            self._annotation_key=key; self._annotation_pending=None
            self.rank_progress_text.set('Rankings, forecast and buy/sell prices ready')
            self.populate_rankings(self.ranking_data); self.populate_buy_list(); self.refresh_views()
        elif op=='model_ready':
            self.model_busy=False
            if payload['horizon']!=self.pricing['horizon']:
                self._ensure_forecast_model(); return
            self.forecast_model=payload; self.model_note.set(self._model_summary(payload)); self.load_backtest_view()
            self.rank_progress.stop(); self.rank_progress.configure(mode='determinate',maximum=1); self.rank_progress['value']=1
            self.rank_progress_text.set('Rankings and forecast ready')
            self._repaint_forecasts()
        elif op=='model_error':
            self.model_busy=False
            self.rank_progress.stop(); self.rank_progress_text.set('Forecast model failed')
            self.model_note.set('Forecast model failed: '+str(payload))
        elif op=='risk_free':
            rate,day=payload
            self.pricing_vars['risk_free'].set(f'{rate:g}')
            self.status.set(f'Risk-free rate set to {rate:g}% (3-month T-bill, FRED, {day}); recalculating Sharpe ratios')
            self.apply_pricing()
        elif op=='catalysts':
            count,notes=payload
            self.load_catalysts(); self.populate_sets()
            self.status.set(f'Release calendar refreshed ({count:,} set records)'+('; '+'; '.join(notes) if notes else ''))
        elif op=='set_names':
            self.set_name_map=payload; self.populate_sets()
        elif op=='longterm':
            lines=[l for l in self.check_details.get().split('\n') if 'Looking up long-term' not in l]
            self.check_details.set('\n'.join(lines+['• '+payload]))
        elif op=='facts':
            self.populate_today()
            if hasattr(self,'cycle_tree'): self.populate_cycle()
            self.card_facts=payload; attach_card_facts(self.ranking_data.get('fresh') or [],payload)
            self.populate_buy_list(); self.populate_alerts()
        elif op=='backtest':
            self.backtest_busy=False
            if isinstance(payload,str): self.backtest_note.set('Backtest failed: '+payload)
            else: self.backtest=payload; self.populate_backtest()
        elif op=='risk_free_error':
            self.status.set('Could not fetch the T-bill rate')
            messagebox.showerror(APP,'Could not fetch the 3-month T-bill rate from FRED:\n'+str(payload))
        elif op=='rankings_error':
            self.rankings_busy=False
            self.rank_refresh_button.configure(state='normal')
            self.rank_progress.stop(); self.rank_progress.configure(mode='determinate',maximum=1); self.rank_progress['value']=0
            self.rank_progress_text.set('Ranking calculation failed')
            self.ranking_note.set('Ranking refresh failed: '+str(payload))

    def logmsg(self,msg):
        self.log.insert('end',f'[{datetime.now().strftime("%H:%M:%S")}] {msg}\n'); self.log.see('end'); self.status.set(msg)
    def launch(self,label,work):
        if self.busy: messagebox.showinfo(APP,'Another download or job is still running — wait for it to finish (progress is shown at the bottom of the window).'); return
        self.busy=True; self.logmsg('Started '+label); self.begin_activity(label)
        def task():
            jid=None
            try:
                jid=self.store.start_job(label)
                def report(text): self.events.put(('log',text))
                report.progress=lambda current,total,phase: self.events.put(('progress',(current,total,phase)))
                count=work(report)
                self.store.end_job(jid,'finished',count,'Completed'); self.events.put(('done',f'{label}: {count:,} records'))
            except Exception as ex:
                if jid is not None:
                    try: self.store.end_job(jid,'error',0,repr(ex))
                    except Exception: pass
                self.events.put(('error',str(ex)))
        threading.Thread(target=task,daemon=True).start()
    def drain(self):
        try:
            while True:
                op,payload=self.events.get_nowait()
                if op=='log': self.logmsg(payload)
                elif op in ASYNC_EVENTS: self.handle_async_event(op,payload)
                elif op=='done': self.busy=False; self.end_activity(payload,True); self.logmsg(payload); self.refresh()
                elif op=='error': self.busy=False; self.end_activity(payload,False); self.logmsg('ERROR: '+payload); messagebox.showerror('Download or job failed',friendly_error(payload))
        except queue.Empty: pass
        self.after(200,self.drain)
    def refresh(self):
        # Counting millions of price rows takes seconds, so it runs off the GUI thread.
        def count_worker():
            try:
                with ReadOnlyStore() as reader:
                    cardcount=dict(reader.q("SELECT game,COUNT(*) FROM cards WHERE game IN ('MTG','Pokémon','One Piece','Riftbound') AND item_type='card' GROUP BY game"))
                    singles='        '.join(f"{g.upper()} SINGLES  {cardcount.get(g,0):,}" for g in SUPPORTED_GAMES)
                    productcount=reader.q("SELECT COUNT(*) FROM cards WHERE game IN ('MTG','Pokémon','One Piece','Riftbound') AND item_type='sealed_product'")[0][0]
                    prices=reader.q("SELECT COUNT(*) FROM daily")[0][0]
                    watched=reader.q("SELECT COUNT(*) FROM portfolio")[0][0]
                self.events.put(('kpis',f"{singles}        SEALED PRODUCTS  {productcount:,}        DAILY PRICE POINTS  {prices:,}        PORTFOLIO  {watched:,}"))
            except Exception as exc:
                self.events.put(('kpis','Dashboard counts unavailable: '+str(exc)))
        if not self.kpis.cget('text'): self.kpis.config(text='Counting cards and price observations…')
        threading.Thread(target=count_worker,daemon=True).start()
        self.clear(self.jobtree)
        for start,task,status,cnt,msg in self.store.q('SELECT started_at,task,status,count,message FROM jobs ORDER BY id DESC LIMIT 50'):
            self.jobtree.insert('', 'end', values=(start,task,status,cnt,msg))
        self.load_portfolio(); self.refresh_rankings()
    def clear(self,tree):
        for x in tree.get_children(): tree.delete(x)
    def _history_printing_chosen(self):
        self.history_series='market_'+self.history_printing.get(); self.load_history()
    def load_history(self):
        cid=self.history_id.get().strip(); self.clear(self.pricetree)
        self.history_chart_meta={}; self._show_history_stats()
        if not cid:
            self.history_title.set('No card selected'); self.history_status.set('Select a card to view history.')
            self._draw_history_chart([]); return
        card=self.store.q("SELECT name,game,item_type,set_code,collector_number,rarity FROM cards WHERE id=? AND game IN ('MTG','Pokémon','One Piece','Riftbound')",(cid,))
        if not card:
            self.history_title.set('Unknown card'); self.history_status.set('This record is not in the supported MTG/Pokémon catalog.')
            self._draw_history_chart([]); return
        name,game,item_type,set_code,number,rarity=card[0]
        self.history_results_frame.pack_forget()
        self.history_title.set(name)
        # high_raw is the single most expensive asking price (often a placeholder listing), not a sale.
        rows=self.store.q("SELECT source_time,price,currency,source,price_type,collected_at FROM prices WHERE card_id=? AND price_type NOT LIKE 'high_raw_%' ORDER BY source_time DESC LIMIT 4000",(cid,))
        daily=self.store.q('SELECT p.name,d.day,d.market,d.low,d.buylist,d.eu FROM daily d JOIN printings p ON p.id=d.printing '
                           'WHERE d.card=? ORDER BY d.day',(card_key(cid),))
        market=[(date.fromordinal(day).isoformat(),m/100.0,'market_'+name) for name,day,m,_l,_b,_e in daily if m]
        # One printing at a time: the one opened from the rankings or picked in the selector,
        # else Normal when the card has it, else its best other printing.
        types=sorted({t for _,_,t in market},key=_price_type_priority)
        if self.history_series in types: series_type=self.history_series
        elif RANK_PRICE_TYPE in types: series_type=RANK_PRICE_TYPE
        else: series_type=types[0] if types else None
        self.history_printing_box['values']=[t.partition('_')[2] for t in types]
        self.history_printing.set(series_type.partition('_')[2] if series_type else '')
        self.history_title.set(printing_label(name,series_type or ''))
        # The table lists the selected printing's market/low/mid/direct-low rows only.
        selected=(series_type or '').partition('_')[2]
        for row in rows:
            if not selected or row[4].partition('_')[2]==selected:
                self.pricetree.insert('','end',values=(row[0],money(row[1]),row[2],row[3],row[4],row[5]))
        points=[(day,price) for day,price,price_type in market if price_type==series_type]
        subtype=(series_type or '').partition('_')[2]
        mine=[row for row in daily if row[0]==subtype]
        low_price=next((l/100.0 for _n,day,_m,l,_b,_e in reversed(mine) if l),None)
        extras={'buylist':[(date.fromordinal(day).isoformat(),b/100.0) for _n,day,_m,_l,b,_e in mine if b],
                'eu':[(date.fromordinal(day).isoformat(),e/100.0) for _n,day,_m,_l,_b,e in mine if e]}
        metrics=calculate_market_metrics(points,risk_free=self.pricing['risk_free']/100.0)
        pricing=self._row_pricing({**metrics,'printing':subtype,'low_price':low_price}) if metrics.get('observations') else None
        release=self.store.q("SELECT MIN(released_on) FROM set_info WHERE game=? AND code=? AND source='scryfall'",(game,set_code)) or [(None,)]
        self.history_chart_meta={'title':f'{subtype or "Market"} market price','low':low_price,'forecast':pricing,
                                 'buylist':extras['buylist'],'release':release[0][0]}
        self._draw_history_chart(points)
        self._show_history_stats(metrics,points,low_price,pricing)
        self._prefill_trade(metrics if metrics.get('observations') else None,low_price,pricing)
        details=' · '.join(str(x) for x in (game,set_code,f'#{number}' if number else '',rarity,item_type.replace('_',' ')) if x)
        if not points:
            self.history_status.set(f'{details} — no saved market prices yet. Run a daily sync (and the MTGJSON import for MTG).')
        else:
            extra=f" · excluded from rankings: {', '.join(self.history_flags)}" if self.history_flags else ''
            if 'market ≪ low' in self.history_flags:
                extra+=(f" — TCGplayer's market price ({money(points[-1][1])}) is below every current listing ({money(low_price)}): it averages "
                        "recent sales of every condition, so a few cheap played-copy sales can drag it down. TCGplayer's site shows a "
                        "Near Mint price separately; use the listings, not this number, for this card.")
            row=self.row_index.get((cid,'market_'+subtype)) or {}
            facts=next(((getattr(self,'card_facts',None) or {})[k] for k in mtg_name_keys(name) if k in (getattr(self,'card_facts',None) or {})),None) if game=='MTG' else None
            side=[]
            if extras['buylist']: side.append(f"Card Kingdom buylist {money(extras['buylist'][-1][1])}"+
                                             (f" ({row['buylist_change_30d']:+.0f}% 30d)" if row.get('buylist_change_30d') is not None else ''))
            if extras['eu'] and self.cardmarket_on():
                rate=float(self.store.get_setting('eurusd','0') or 0)
                side.append(f"Cardmarket €{extras['eu'][-1][1]:.2f}"+(f" ≈ {money(extras['eu'][-1][1]*rate)}" if rate else '')+
                            (f" ({row['eu_change_30d']:+.0f}% 30d)" if row.get('eu_change_30d') is not None else ''))
            cycle=release_note(row) if row else None
            if cycle: side.append(cycle)
            if facts:
                side.append('legal: '+(facts['formats'].replace(',',', ') or 'none'))
                if facts['edhrec']: side.append(f"EDHREC #{facts['edhrec']:,}")
                side.append(f"printed in {facts['sets']} set(s)")
                if facts['reprint']: side.append(f"REPRINT announced: {facts['reprint']}")
                if facts['banned']: side.append(f"banned/restricted in {facts['banned']} (long-standing, already in the price)")
                if facts.get('legal_change'): side.append(f"LEGALITY CHANGED: {facts['legal_change']}")
            self.history_status.set(f'{details} · {len(points):,} daily {subtype} market points, {points[0][0]} → {points[-1][0]}{extra}'+
                                    (' · '+' · '.join(side) if side else ''))
    def save_csv(self,heads,rows,name):
        path=filedialog.asksaveasfilename(defaultextension='.csv',initialfile=name,filetypes=[('CSV (opens in Excel)','*.csv')])
        if not path:return
        rows=list(rows)
        try:
            with open(path,'w',newline='',encoding='utf-8-sig') as f:
                writer=csv.writer(f);writer.writerow([csv_heading(h) for h in heads]);writer.writerows(rows)
        except PermissionError:
            messagebox.showerror(APP,f'Could not save {Path(path).name}: it is probably open in Excel. Close it there and export again.'); return
        except OSError as exc:
            messagebox.showerror(APP,friendly_error(f'Could not save {path}: {exc}')); return
        self.status.set(f'Exported {len(rows):,} rows to {path}')
        if messagebox.askyesno(APP,f'Saved {len(rows):,} rows to:\n{path}\n\nOpen it now?'):
            try:
                if sys.platform.startswith('win'): os.startfile(path)
                else: subprocess.Popen(['open' if sys.platform=='darwin' else 'xdg-open',path])
            except OSError as exc: messagebox.showerror(APP,f'Could not open the file: {exc}')
    def export_history(self):
        cid=self.history_id.get().strip()
        if not cid:messagebox.showinfo(APP,'Load a card first: search for it above and double-click it.');return
        heads=['source_time','price','currency','source','price_type','collected_at']
        self.save_csv(heads,self.store.q("SELECT source_time,price,currency,source,price_type,collected_at FROM prices WHERE card_id=? AND price_type NOT LIKE 'high_raw_%' ORDER BY source_time",(cid,)),'card_history.csv')
    def export_cards(self):
        self.save_csv(['id','game','item_type','name','set_code','collector_number','rarity','finish'],self.store.q("SELECT id,game,item_type,name,set_code,collector_number,rarity,finish FROM cards WHERE game IN ('MTG','Pokémon','One Piece','Riftbound') ORDER BY game,name"),'cards.csv')
    def open_folder(self):
        import subprocess
        if sys.platform=='darwin': subprocess.Popen(['open',str(ROOT)])
        elif sys.platform.startswith('win'): os.startfile(str(ROOT))
        else: subprocess.Popen(['xdg-open',str(ROOT)])
    def close(self):
        if self.busy:
            messagebox.showwarning(APP,'A download or job is still running. Please wait for it to finish (progress is at the bottom of the window) '
                                       'before closing, so nothing is left half-saved.')
            return
        self.store.close();self.destroy()


class AutomatedTerminal(Terminal):
    """Single-file GUI with daily TCGCSV catalog and price synchronization."""
    def __init__(self):
        super().__init__()
        self.title('Card Market Terminal | Daily Card Prices')
        self.auto_enabled = tk.BooleanVar(value=self.store.get_setting('auto_collect','0')=='1')
        self.build_auto_controls(); self._auto_wrap()
        self.after(4000,self.schedule_tick)
        if not self.store.get_setting('catalysts_epoch',''): self.after(2500,self.refresh_catalysts_async)

    def build_auto_controls(self):
        p=self.tabs['Collectors']
        bar=ttk.LabelFrame(p,text=' DAILY TCGCSV SYNC ',padding=12)
        bar.pack(fill='x',before=self.log,pady=(0,8))
        ttk.Label(bar,text='Finds new products and imports daily TCGplayer prices for Magic, Pokémon, One Piece and Riftbound.',style='Small.TLabel').pack(anchor='w')
        ttk.Button(bar,text='Download today\'s prices now',command=self.start_tcgcsv).pack(side='left',padx=(0,12),pady=9)
        consent=ttk.Frame(p); consent.pack(fill='x',before=self.log,pady=(0,8))
        ttk.Checkbutton(consent,text='Enable daily automatic sync while this app is open',variable=self.auto_enabled,command=self.change_auto).pack(anchor='w')
        ttk.Label(consent,text='Uses TCGCSV documented pacing and a custom User-Agent. The daily build marker is checked first; unchanged data is not re-downloaded. This switch only works while the app is open; to update while it is closed, use Enable daily background sync in Settings.',style='Small.TLabel',wraplength=940).pack(anchor='w',pady=4)
        self.source_note=tk.StringVar(value='')
        ttk.Label(consent,textvariable=self.source_note,style='Small.TLabel',wraplength=940).pack(anchor='w')
        self.update_source_note()

    def update_source_note(self):
        self.source_note.set('Automatic updates '+('ON' if self.auto_enabled.get() else 'OFF')+
            ' | Dataset marker: '+(self.store.get_setting('tcgcsv_dataset_marker','not synced') or 'not synced')+
            ' | Last data import: '+(self.store.get_setting('tcgcsv_success','never') or 'never')+
            ' | Last source check: '+(self.store.get_setting('tcgcsv_last_check','never') or 'never'))

    def change_auto(self):
        if self.auto_enabled.get():
            ok=messagebox.askyesno('Authorize scheduled downloads',
              'Allow this app, while open, to check TCGCSV daily and sync both Magic and Pokémon if its daily dataset has changed? Requests are paced and the app stops if throttled. No paid services or transactions.')
            if not ok: self.auto_enabled.set(False)
        self.store.setting('auto_collect','1' if self.auto_enabled.get() else '0')
        self.update_source_note()

    def schedule_tick(self):
        try:
            if self.auto_enabled.get() and not self.busy:
                now=time.time()
                last_check=float(self.store.get_setting('tcgcsv_check_epoch','0') or 0)
                last_attempt=float(self.store.get_setting('tcgcsv_attempt','0') or 0)
                if now-last_check>=86400 and now-last_attempt>=3600:
                    self.store.setting('tcgcsv_attempt',now)
                    self.start_tcgcsv()
        except Exception as e: self.logmsg('Scheduler error: '+str(e))
        finally:
            self.after(60000,self.schedule_tick)

    def start_tcgcsv(self):
        if self.busy: messagebox.showinfo(APP,'Another download or job is still running — wait for it to finish (progress is shown at the bottom of the window).'); return
        self.store.setting('tcgcsv_attempt',time.time())
        def work(report):
            report('Source: TCGCSV daily build; all supported games; no individual card requests')
            count=sync_tcgcsv_daily(self.store,report)
            run_side_feeds(self.store,report)
            return count
        self.launch('TCGCSV daily price sync',work)

    def drain(self):
        try:
            while True:
                op,payload=self.events.get_nowait()
                if op=='log': self.logmsg(payload)
                elif op in ASYNC_EVENTS: self.handle_async_event(op,payload)
                elif op=='done':
                    self.busy=False; self.end_activity(payload,True); self.logmsg(payload); self.refresh(); self.update_source_note()
                    self.load_catalysts(); self._load_set_names()
                elif op=='error':
                    self.busy=False; self.end_activity(payload,False); self.logmsg('ERROR: '+payload); self.update_source_note()
                    messagebox.showerror('Collection error',payload)
        except queue.Empty: pass
        self.after(200,self.drain)

def run_side_feeds(store, report):
    """The free feeds besides TCGCSV, each best-effort so one outage never blocks the sync: release calendar (daily),
    MTGJSON buylist/Cardmarket (daily), Scryfall legality (weekly), TCGCSV archive watch (weekly)."""
    now=time.time(); age=lambda key: now-float(store.get_setting(key,'0') or 0)
    jobs=[('catalysts_epoch',20*3600,lambda: refresh_catalysts(store,report,include_tcgcsv=False)),
          ('mtgjson_today_epoch',12*3600,lambda: sync_mtgjson_today(store,report)),
          ('scryfall_oracle_epoch',6*86400,lambda: refresh_scryfall_oracle(store,report)),
          ('archive_check_epoch',6*86400,lambda: check_history_archive(store,report)),
          ('maintenance_epoch',6.5*86400,lambda: run_maintenance(store,report))]
    if store.get_setting('cardmarket_module','0')=='1': jobs.append(('fx_epoch',20*3600,lambda: refresh_fx(store,report)))
    for key,every,job in jobs:
        if age(key)<every: continue
        try:
            job(); store.setting(key,now)
        except Exception as exc:
            report(f'{key.replace("_epoch","").replace("_"," ")} skipped: {exc}')

def check_history_archive(store, report):
    """TCGCSV's daily price archive (from 2024-02-08, both games) went offline in 2026. Check weekly; when it is back,
    say so and backfill up to the last 400 days into the compact history automatically (needs 7-Zip)."""
    probe=(datetime.now(timezone.utc).date()-timedelta(days=3)).isoformat()
    req=urllib.request.Request(f'{HISTORY_ARCHIVE_BASE}/prices-{probe}.ppmd.7z',headers={'User-Agent':USER_AGENT},method='HEAD')
    try:
        with urllib.request.urlopen(req,timeout=30) as r: ok=r.status==200
    except urllib.error.HTTPError: ok=False
    store.setting('archive_available','1' if ok else '0')
    if not ok:
        report('TCGCSV price archive still offline (checked weekly)'); return 0
    if not find_7zip():
        report('TCGCSV price archive is back online: install 7-Zip to backfill history automatically'); return 0
    end=datetime.now(timezone.utc).date()-timedelta(days=2); start=max(HISTORY_ARCHIVE_FIRST_DATE,end-timedelta(days=399))
    report(f'TCGCSV price archive is back online: backfilling {start} to {end} into the compact history')
    notify_desktop('Card Market Terminal','TCGCSV price history is available again; backfilling up to 400 days.')
    return backfill_tcgcsv_history(store,report,start.isoformat(),end.isoformat())

# --- Upkeep: data health, weekly backup and raw-row retention, EUR/USD for the Cardmarket module ---
RAW_RETENTION_DAYS = 120   # raw TCGCSV rows (every field) kept this long; market and cheapest listing stay in daily forever
FX_SOURCE = 'https://fred.stlouisfed.org/graph/fredgraph.csv?id=DEXUSEU'  # US dollars per euro (FRED, free)

def fetch_eurusd():
    req=urllib.request.Request(FX_SOURCE,headers={'User-Agent':USER_AGENT,'Accept':'text/csv'})
    with urllib.request.urlopen(req,timeout=30) as r: lines=r.read().decode('utf-8-sig').strip().splitlines()
    for line in reversed(lines[1:]):
        day,_,value=line.partition(',')
        try: return float(value),day
        except ValueError: continue
    raise RuntimeError('FRED returned no EUR/USD rate')

def refresh_fx(store, report=lambda _m: None):
    rate,day=fetch_eurusd(); store.setting('eurusd',rate); store.setting('eurusd_day',day)
    report(f'EUR/USD {rate:g} (FRED, {day})'); return 1

def data_health(store, now=None):
    """Plain-language warnings about the data itself: a missed sync, a sync that returned far fewer prices than the one
    before (a partial TCGCSV build), or the history archive coming back."""
    now=now or time.time(); out=[]
    last=float(store.get_setting('tcgcsv_success_epoch','0') or 0)
    if last and now-last>36*3600: out.append(f'No successful TCGCSV sync for {(now-last)/3600:.0f} hours: type SYNC (prices may be stale)')
    if not last: out.append('No TCGCSV sync yet: type SYNC')
    warning=store.get_setting('sync_warning','')
    if warning: out.append(warning)
    if store.get_setting('archive_available','')=='1': out.append('TCGCSV price archive is online again: history backfill runs with the background sync')
    return out

def record_sync_counts(store, counts):
    """Compare this sync's priced-product count per game with the last one; a big drop means a partial dataset."""
    try: prior=json.loads(store.get_setting('sync_counts','{}') or '{}')
    except ValueError: prior={}
    low=[f'{g}: {n:,} vs {prior[g]:,} last sync' for g,n in counts.items() if prior.get(g) and n<0.8*prior[g]]
    store.setting('sync_warning',('Partial sync? '+'; '.join(low)+'. Rankings may miss cards until the next full sync.') if low else '')
    store.setting('sync_counts',json.dumps(counts))

def backup_essentials(store, report=lambda _m: None):
    """One rolling copy of what cannot be downloaded again - your portfolio, trades and settings, and the compact
    daily price history (TCGCSV's archive is offline and MTGJSON keeps only 90 days) - in backups/essentials.sqlite3."""
    folder=ROOT/'backups'; folder.mkdir(parents=True,exist_ok=True)
    tmp=folder/'essentials.partial.sqlite3'; final=folder/'essentials.sqlite3'
    if tmp.exists(): tmp.unlink()
    con=sqlite3.connect(DB); con.execute('PRAGMA busy_timeout=10000')
    try:
        con.execute('ATTACH DATABASE ? AS b',(str(tmp),))
        for table in ('settings','portfolio','trades','printings','daily','set_info','market_events','mtg_oracle'):
            con.execute(f'CREATE TABLE b.{table} AS SELECT * FROM main.{table}')
        con.commit(); con.execute('DETACH DATABASE b')
    finally: con.close()
    tmp.replace(final); store.setting('backup_at',utc())
    report(f'Backup written: {final} ({final.stat().st_size/1048576:,.0f} MB)'); return 1

def run_maintenance(store, report=lambda _m: None):
    """Weekly: back up the essentials, drop raw rows past the retention window (their market and cheapest-listing
    prices are already in the daily history) in small batches so the app stays responsive, and optimize."""
    backup_essentials(store,report)
    days=int(float(store.get_setting('raw_retention_days',RAW_RETENTION_DAYS) or 0)); removed=0
    if days>0 and store.get_setting('daily_version','')==str(DAILY_VERSION):
        cutoff=(date.today()-timedelta(days=days)).isoformat()
        while True:
            with store.lock:
                n=store.con.execute('DELETE FROM prices WHERE id IN (SELECT id FROM prices WHERE source_time<? LIMIT 100000)',(cutoff,)).rowcount
                store.con.commit()
            removed+=n
            if n<100000: break
        report(f'Removed {removed:,} raw price rows older than {days} days (kept in the compact daily history)')
    with store.lock:
        store.con.execute('PRAGMA optimize'); store.con.execute('PRAGMA wal_checkpoint(TRUNCATE)')
    return removed

def mass_entry_text(rows):
    """TCGplayer Mass Entry lines ('2 Card Name [SET]') for rows with a suggested quantity."""
    return '\n'.join(f"{r['qty']} {r['card_name']} [{r.get('set_code') or ''}]" for r in rows if r.get('qty'))

# --- Portable copy: the script plus everything it needs, to carry to another computer ---
PORTABLE_TABLES = ('settings','cards','tcgcsv_groups','set_info','portfolio','trades','printings','daily','mtg_oracle','market_events')
PORTABLE_FILES = ('rankings_cache.json.gz','forecast_model_7d.json','forecast_model_14d.json','forecast_model_30d.json',
                  'strategy_backtest.json','release_curves.json','mtgjson_cardIdentifiers.csv.xz','daily_brief.html','pricing_cache.pickle')
FAT32_MAX_FILE = 4*1024**3-1

def portable_size_estimate():
    """Upper bound for a portable copy in bytes: today's database (the copy leaves out raw rows, so it is smaller) plus saved files."""
    size=DB.stat().st_size if DB.exists() else 0
    return size+sum((ROOT/n).stat().st_size for n in PORTABLE_FILES if (ROOT/n).exists())+Path(__file__).stat().st_size

def volume_format(folder):
    """File system of the drive holding folder ('FAT32', 'NTFS', 'exFAT', ...) on Windows; None elsewhere or when unknown."""
    if not sys.platform.startswith('win'): return None
    try:
        import ctypes
        root=os.path.splitdrive(os.path.abspath(folder))[0]+'\\'
        name=ctypes.create_unicode_buffer(64)
        ok=ctypes.windll.kernel32.GetVolumeInformationW(ctypes.c_wchar_p(root),None,0,None,None,None,name,len(name))
        return name.value or None if ok else None
    except Exception: return None
PORTABLE_README = """Card Market Terminal - portable copy
=====================================
Run "Card Market Terminal.py" from this folder (double-click it, or: python "Card Market Terminal.py").
It uses the CardMarketTerminalData folder next to it, so your portfolio, trades, settings and price history come along.

On a new computer:
  1. Install Python 3 from python.org (tick "Add python.exe to PATH"; Tkinter is included). Nothing else is needed.
  2. Open the app. To keep prices updating while the app is closed, click Settings > Enable daily background sync on that computer.

Use one computer at a time: copy the whole folder back and forth (USB drive or external disk). Avoid running it
from a live cloud-sync folder on two computers at once, which can corrupt the database.
"""

def make_portable_copy(store, folder, report=lambda _m: None):
    """Write this script, a compact database (everything except raw rows already summarized in the daily history) and the
    saved calculations into folder, ready to run on another computer. Returns the copy's size in bytes."""
    target=Path(folder); data=target/'CardMarketTerminalData'; db=data/'market.sqlite3'
    if db.exists(): raise RuntimeError(f'{target} already holds a Card Market Terminal copy; choose an empty folder.')
    data.mkdir(parents=True,exist_ok=True)
    try:
        shutil.copy2(Path(__file__).resolve(),target/'Card Market Terminal.py')
        Store(db).close()  # creates the schema
        con=sqlite3.connect(db); con.execute('PRAGMA busy_timeout=30000')
        try:
            con.execute('ATTACH DATABASE ? AS src',(str(DB),))
            for table in PORTABLE_TABLES:
                emit_progress(report,0,0,f'Portable copy: {table}')
                cols=[r[1] for r in con.execute(f'PRAGMA src.table_info({table})')]
                names=','.join(cols)
                con.execute(f'DELETE FROM main.{table}')
                con.execute(f'INSERT INTO main.{table}({names}) SELECT {names} FROM src.{table}')
                con.commit(); report(f'Portable copy: {table} copied')
            con.execute('DETACH DATABASE src')
        finally: con.close()
        for name in PORTABLE_FILES:
            if (ROOT/name).exists(): shutil.copy2(ROOT/name,data/name)
    except BaseException:
        # A half-written copy would block the next try ("already holds a copy"); remove only what this run wrote.
        for f in [db,db.with_name(db.name+'-wal'),db.with_name(db.name+'-shm'),target/'Card Market Terminal.py',*(data/n for n in PORTABLE_FILES)]:
            try: f.unlink()
            except OSError: pass
        raise
    (target/'READ ME - portable copy.txt').write_text(PORTABLE_README,encoding='utf-8')
    size=sum(f.stat().st_size for f in target.rglob('*') if f.is_file())
    report(f'Portable copy ready in {target} ({size/1048576:,.0f} MB)')
    return size

def report_portfolio_alerts(store, report):
    """After a background sync, log every portfolio price alert that is now triggered."""
    risk_free=float(store.get_setting('pricing_risk_free',DEFAULT_RISK_FREE_PCT))/100.0
    data=load_rankings(rankings_signature(store,risk_free))
    if not data: return []
    index={(r['card_id'],r['price_type']):r for r in data['fresh']}
    hits=[]
    for cid,price_type,above,below in store.q('SELECT card_id,price_type,alert_above,alert_below FROM portfolio '
                                              'WHERE alert_above IS NOT NULL OR alert_below IS NOT NULL'):
        r=index.get((cid,price_type or RANK_PRICE_TYPE))
        if r:
            for hit in alert_hits(r['latest_price'],above,below): hits.append(f"ALERT {r['name']}: market {money(r['latest_price'])} {hit}")
    for line in hits: report(line)
    return hits

def run_headless_sync():
    """Run one source-marker-checked TCGCSV sync without opening Tkinter."""
    store=Store(); jid=None
    try:
        jid=store.start_job('TCGCSV daily price sync (headless)')
        print(f'[{utc()}] Card Market Terminal: checking TCGCSV daily dataset marker',flush=True)
        count=sync_tcgcsv_daily(store,lambda msg: print(msg,flush=True))
        store.end_job(jid,'finished',count,'Completed')
        print(f'Sync complete. {count:,} catalog records processed.',flush=True)
        try:
            log=lambda msg: print(msg,flush=True)
            run_side_feeds(store,log)
            precompute_market_views(store,log)
            alerts=report_portfolio_alerts(store,lambda msg: print(msg,flush=True))
            brief=write_daily_brief(store,lambda msg: print(msg,flush=True))
            # The weekly long-run sample (about 120 polite requests) runs after the brief so it never delays it.
            if time.time()-float(store.get_setting('longrun_epoch','0') or 0)>6.5*86400:
                try: refresh_longrun(store,log); store.setting('longrun_epoch',time.time())
                except Exception as exc: log(f'long-run sample skipped: {exc}')
            if brief and store.get_setting('notify_after_sync','1')=='1':
                _path,buy_now,signals=brief; health=data_health(store)
                notify_desktop('Card Market Terminal: '+('DATA WARNING' if health else 'daily brief ready'),
                               (health[0]+' · ' if health else '')+
                               f'{buy_now:,} buy-now printings · {len(alerts)} price alert(s) · {signals} portfolio signal(s). Type BRIEF in the app.')
        except Exception as e:
            # The sync itself succeeded; the app will just calculate rankings on its next launch.
            print(f'Precomputing rankings failed: {e}',file=sys.stderr,flush=True)
        return 0
    except Exception as e:
        if jid is not None:
            try: store.end_job(jid,'error',0,repr(e))
            except Exception: pass
        print(f'Sync failed: {e}',file=sys.stderr,flush=True)
        try:  # a silent failure would leave a non-technical user trading on stale prices
            if store.get_setting('notify_after_sync','1')=='1':
                notify_desktop(APP,'Daily price update failed: '+friendly_error(e).split(chr(10))[0][:180])
        except Exception: pass
        return 1
    finally:
        store.close()


def _test_pricing(**kw):
    """Default assumptions with shipping and the per-order fee zeroed, so tests can check the arithmetic directly."""
    return {**DEFAULT_PRICING,'fee_fixed':0.0,'ship_plain':0.0,'ship_tracked':0.0,'ship_in':0.0,'ship_charge':0.0,'min_roi':0.0,**kw}

class OfflineSelfTests(unittest.TestCase):
    """Offline regression tests; no GUI, network, API key, or extra package needed."""
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory()
        self.old_root,self.old_db=ROOT,DB
        globals()['ROOT']=Path(self.tmp.name)
        globals()['DB']=ROOT/'market.sqlite3'
        self.store=Store()

    def tearDown(self):
        try: self.store.close()
        except Exception: pass
        globals()['ROOT'],globals()['DB']=self.old_root,self.old_db
        self.tmp.cleanup()

    def test_history_archive_ingestion_only_imports_supported_games(self):
        day='2026-10-20'; root=ROOT/day
        for category,group,product in [('1','100','10'),('3','200','30'),('2','300','20')]:
            path=root/category/group/'prices'; path.parent.mkdir(parents=True,exist_ok=True)
            path.write_text(json.dumps({'success':True,'results':[{'productId':int(product),'subTypeName':'Normal','marketPrice':12.5,'lowPrice':10.0}]}),encoding='utf-8')
        now=utc(); rows=[]
        for category,product,game in [('1','10','MTG'),('3','30','Pokémon'),('2','20','Other Game')]:
            rows.append((f'tcgcsv:{category}:{product}',game,'Fixture Card','SET','1','Rare','Normal','{}',now,'card'))
        self.store.batch(rows)
        count=ingest_tcgcsv_archive_tree(self.store,ROOT,day,lambda _:None)
        self.assertEqual(count,4)
        ids={card_id_from_key(row[0]) for row in self.store.q('SELECT DISTINCT card FROM daily')}
        self.assertEqual(ids,{'tcgcsv:1:10','tcgcsv:3:30'},'archives go to the compact history only')
        self.assertEqual(self.store.q('SELECT market,low FROM daily WHERE card=?',(card_key('tcgcsv:1:10'),)),[(1250,1000)])
        self.assertEqual(self.store.q('SELECT COUNT(*) FROM prices')[0][0],0,'no raw rows (about a million per archive day)')

    def test_supported_game_scope_diagnostics_hide_other_games(self):
        now=utc(); self.store.batch([
            ('x:1','Other Game','Legacy Card','SET','1','Rare','Normal','{}',now,'card'),
            ('tcgcsv:1:1','MTG','Magic Card','SET','1','Rare','Normal','{}',now,'card')])
        diag=market_data_diagnostics(self.store,datetime(2026,10,23,tzinfo=timezone.utc).date())
        self.assertEqual(diag['total_cards'],1)

    def test_numeric_and_profit_validation(self):
        self.assertEqual(numeric('12.50'),12.5)
        for bad in (None,'bad',0,-1,'nan','inf',1e100): self.assertIsNone(numeric(bad))
        profit,roi=calculate_net_profit(20,35,10,4,2)
        self.assertAlmostEqual(profit,19.0)
        self.assertAlmostEqual(roi,19/44*100)
        with self.assertRaises(ValueError): calculate_net_profit(20,35,10,4,1.5)
        with self.assertRaises(ValueError): calculate_net_profit(20,-1,10,4,1)

    def test_product_classification(self):
        self.assertEqual(classify_tcgcsv_product('Lugia VSTAR',{'number':'139/195','rarity':'Ultra Rare'}),'card')
        self.assertEqual(classify_tcgcsv_product('Silver Tempest Booster Box',{'rarity':'Rare'}),'sealed_product')
        self.assertEqual(classify_tcgcsv_product('Tinker Bell',{}),'other')
        self.assertEqual(classify_tcgcsv_product('Code Card - Booster Bundle',{}),'other')

    def test_timestamp_formats(self):
        self.assertEqual(tcgcsv_timestamp('2026-10-23T20:06:07+0000'),'2026-10-23T20:06:07+00:00')
        self.assertEqual(tcgcsv_timestamp('2026-10-23'),'2026-10-23T00:00:00+00:00')
        self.assertEqual(tcgcsv_timestamp('not-a-date'),'not-a-date')

    def test_store_batch_and_price_deduplication(self):
        row=('tcgcsv:3:100','Pokémon','Test Card','SET','1/10','Rare','Normal','{}',utc(),'card')
        price=('tcgcsv:3:100','tcgcsv_tcgplayer','market_Normal','USD',12.5,'2026-10-23T20:00:00+00:00',utc())
        self.store.batch([row],[price]); self.store.batch([row],[price])
        self.assertEqual(self.store.q('SELECT COUNT(*) FROM cards')[0][0],1)
        self.assertEqual(self.store.q('SELECT COUNT(*) FROM prices')[0][0],1)
        self.assertEqual(self.store.q('SELECT item_type FROM cards')[0][0],'card')

    def test_migrates_old_database_schema(self):
        self.store.close()
        con=sqlite3.connect(DB)
        with con:
            con.execute('DROP TABLE cards')
            con.execute('''CREATE TABLE cards (id TEXT PRIMARY KEY, game TEXT NOT NULL, name TEXT NOT NULL,
                set_code TEXT, collector_number TEXT, rarity TEXT, finish TEXT, details TEXT, updated_at TEXT NOT NULL)''')
            con.execute("INSERT INTO cards VALUES('old:1','MTG','Old Card','SET','1','Rare','Normal','{}',?)",(utc(),))
            old_detail=json.dumps({'provider':'TCGCSV / TCGplayer cached product prices','extended_data':[]})
            con.execute("INSERT INTO cards VALUES('old:2','Pokémon','Silver Tempest Booster Box','SET','','','Normal',?,?)",(old_detail,utc()))
            con.execute('CREATE INDEX IF NOT EXISTS idx_prices_card_source_type_time ON prices(card_id,source,price_type,source_time)')
        con.close()  # the context manager only commits; Windows can't delete an open DB file
        self.store=Store()
        self.assertIn('item_type',{r[1] for r in self.store.q('PRAGMA table_info(cards)')})
        self.assertEqual(self.store.q("SELECT item_type FROM cards WHERE id='old:1'")[0][0],'card')
        self.assertEqual(self.store.q("SELECT item_type FROM cards WHERE id='old:2'")[0][0],'sealed_product')
        indexes={r[1] for r in self.store.q('PRAGMA index_list(prices)')}
        self.assertNotIn('idx_prices_card_source_type_time',indexes)

    def test_market_metrics_require_history_and_rank_positive_daily_series(self):
        today=datetime(2026,10,23,tzinfo=timezone.utc).date()
        rising=[]
        price=10.0
        for i in range(35):
            day=today-timedelta(days=34-i)
            price*=1.006 if i%3 else 1.012
            rising.append((day.isoformat()+'T20:00:00+00:00',price))
        metrics=calculate_market_metrics(rising,today)
        self.assertEqual(metrics['observations'],35)
        self.assertIsNotNone(metrics['sharpe_30d'])
        self.assertIsNotNone(metrics['return_7d'])
        self.assertIsNotNone(metrics['opportunity_score'])
        short=calculate_market_metrics(rising[-1:],today)
        self.assertIsNone(short['sharpe_30d'])
        self.assertIsNone(short['opportunity_score'])

    def test_sharpe_tolerates_two_missing_days_but_not_three(self):
        today=datetime(2026,10,23,tzinfo=timezone.utc).date()
        full=[]; price=10.0
        for i in range(35):
            price*=1.006 if i%3 else 1.012
            full.append(((today-timedelta(days=34-i)).isoformat()+'T20:00:00+00:00',price))
        def without(*days_ago):
            drop={(today-timedelta(days=d)).isoformat() for d in days_ago}
            return [p for p in full if p[0][:10] not in drop]
        two=calculate_market_metrics(without(9,20),today)
        self.assertEqual(two['obs_30d'],28)
        self.assertIsNotNone(two['sharpe_30d'])
        three=calculate_market_metrics(without(5,12,20),today)
        self.assertEqual(three['obs_30d'],27)
        self.assertIsNone(three['sharpe_30d'])

    def test_jump_share_separates_single_jumps_from_steady_rises(self):
        today=datetime(2026,10,23,tzinfo=timezone.utc).date()
        stamp=lambda i:(today-timedelta(days=34-i)).isoformat()+'T20:00:00+00:00'
        steady=[(stamp(i),10*(1.01**i)) for i in range(35)]
        jump=[(stamp(i),10.0 if i<30 else 30.0+i*0.01) for i in range(35)]
        self.assertLess(calculate_market_metrics(steady,today)['jump_share'],0.2)
        m=calculate_market_metrics(jump,today)
        self.assertGreater(m['jump_share'],0.9)
        self.assertIn('single jump',spike_flags(m))
        self.assertEqual(spike_flags({'latest_price':0.62,'low_price':None,'return_30d':5,'jump_share':0.1}),['under $1'])
        self.assertEqual(spike_flags({'latest_price':12.0,'low_price':5.0,'return_30d':5,'jump_share':0.1}),['market ≫ low'])
        self.assertEqual(spike_flags({'latest_price':28.29,'low_price':43.99,'return_30d':7,'jump_share':0.1}),['market ≪ low'],
                         'a market price dragged under every listing by played-copy sales (The Theorist, FRA #43)')
        self.assertEqual(spike_flags({'latest_price':12.0,'low_price':10.0,'return_30d':40,'jump_share':0.3}),[])

    def test_forecast_model_learns_from_history_and_backtests_out_of_sample(self):
        import random
        rng=random.Random(7); latest=datetime(2026,10,26).date(); now=utc(); rows=[]; prices=[]
        for k in range(240):
            cid=f'tcgcsv:1:{k}'; rising=k%2==0; price=5.0
            rows.append((cid,'MTG',f'Card {k}','SET','1','Rare','Normal','{}',now,'card'))
            for d in range(100,-1,-1):
                price*=(1.01 if rising else 1.0)+rng.uniform(-0.004,0.004)
                prices.append((cid,'mtgjson_tcgplayer','market_Normal','USD',price,(latest-timedelta(days=d)).isoformat()+'T12:00:00+00:00',now))
        self.store.batch(rows,prices)
        model=build_forecast_model(self.store,14,latest.isoformat())
        rising=forecast_for(model,35.0,7.0,6.0,'Normal',29,0.003); flat=forecast_for(model,0.0,0.0,6.0,'Normal',29,0.003)  # trades daily, calm
        self.assertGreater(forecast_prob_above(rising,0.0),0.9)
        self.assertLess(forecast_prob_above(flat,0.0),0.7)
        self.assertGreater(forecast_quantile(rising,0.5),0.10)
        bt=model['backtest']
        self.assertGreater(bt['test_samples'],0); self.assertGreater(bt['train_samples'],0)
        self.assertLess(bt['brier_model'],bt['brier_baseline'])
        save_forecast_model(model)
        self.assertEqual(load_forecast_model(14,latest.isoformat())['samples'],model['samples'])
        self.assertIsNone(load_forecast_model(14,'2026-10-25'),'a model for older data is rebuilt')

    def test_pricing_targets_follow_forecast_and_liquidity(self):
        fc={'key':'all','n':100,'bins':[[b,1] for b in range(-50,50)],'horizon':14}  # -25% .. +24.5%, uniform
        P=lambda **kw:_test_pricing(fee_pct=10.0,cost=0.5,win_pct=60.0,sell_through=0.5,min_profit=0.0,**kw)
        liquid=pricing_targets(10.0,8.0,fc,P(),changes_30d=None)
        self.assertAlmostEqual(liquid['p_rise'],0.49)
        self.assertAlmostEqual(liquid['max_buy'],10*(1+forecast_quantile(fc,0.4))*0.9-0.5)
        self.assertGreater(liquid['win_at_low'],liquid['win_at_market'])
        self.assertAlmostEqual(liquid['min_sell'],(8.0+0.5)/0.9)
        busy=pricing_targets(10.0,8.0,fc,P(),changes_30d=20)
        thin=pricing_targets(10.0,8.0,fc,P(),changes_30d=1)
        self.assertGreater(busy['p_sold'],thin['p_sold'])
        self.assertEqual((busy['max_qty'],thin['max_qty']),(4,0))  # 20×14/30×0.5 = 4.67; 1×14/30×0.5 = 0.23
        self.assertLess(thin['win_at_low'],busy['win_at_low'])
        self.assertIsNone(thin['max_buy'],'too illiquid to reach a 60% win chance at any price')
        self.assertTrue(0<thin['target_fill']<busy['target_fill']<=busy['p_sold'],'thin printings sell less often at any ask')
        grid=[(q,forecast_quantile(fc,q)) for q in SELL_GRID]
        later=10.0*(1+forecast_quantile(fc,0.5))*0.9-0.5  # an unsold copy sells later at the median
        evs=[(1-q)*busy['p_sold']*(10.0*(1+r)*0.9-0.5)+(1-(1-q)*busy['p_sold'])*later-8.0 for q,r in grid]
        self.assertAlmostEqual(busy['target_ev'],max(evs),msg='the ask maximizes expected profit, counting a later sale of an unsold copy')
        self.assertIsNone(pricing_targets(10.0,None,fc,_test_pricing(fee_pct=99.0,cost=50.0,win_pct=60.0))['max_buy'])

    def test_sharpe_subtracts_risk_free_and_liquidity_counts_price_moves(self):
        today=datetime(2026,10,23,tzinfo=timezone.utc).date(); price=10.0; points=[]
        for i in range(35):
            price*=1.002 if i%2 else 1.0005
            points.append(((today-timedelta(days=34-i)).isoformat()+'T20:00:00+00:00',price))
        zero=calculate_market_metrics(points,today,0.0); rf=calculate_market_metrics(points,today,0.0404)
        self.assertLess(rf['sharpe_30d'],zero['sharpe_30d'])
        flat_then_moves=[(p[0],10.0 if i<30 else 10.0+i) for i,p in enumerate(points)]
        self.assertEqual(calculate_market_metrics(flat_then_moves,today)['price_changes_30d'],5)
        self.assertEqual([liquidity_label(n) for n in (0,2,6,15,None)],['Very low','Low','Medium','High','—'])
        self.assertIsNone(parse_filter_value(' any ')); self.assertEqual(parse_filter_value('$1,250.5'),1250.5)
        with self.assertRaises(ValueError): parse_filter_value('abc')

    def test_rankings_are_saved_and_reused_until_the_data_changes(self):
        today=datetime.now(timezone.utc).date(); now=utc(); prices=[]
        self.store.batch([('tcgcsv:1:1','MTG','Saved Card','SET','1','Rare','Normal','{}',now,'card')])
        for i in range(35):
            stamp=(today-timedelta(days=34-i)).isoformat()+'T20:00:00+00:00'
            prices.append(('tcgcsv:1:1','tcgcsv_tcgplayer','market_Normal','USD',10*(1.006 if i%3 else 1.012)**i,stamp,now))
            prices.append(('tcgcsv:1:1','tcgcsv_tcgplayer','market_Foil','USD',3*(1.01 if i%2 else 1.002)**i,stamp,now))
        self.store.batch([],prices)
        self.store.setting('tcgcsv_dataset_marker','marker-1')
        signature=rankings_signature(self.store,0.0404)
        data=build_market_rankings(self.store,today,risk_free=0.0404)
        save_rankings(data,signature)
        loaded=load_rankings(signature)
        self.assertEqual([r['name'] for r in loaded['sharpe']],[r['name'] for r in data['sharpe']])
        self.assertEqual(loaded['sharpe'][0]['sharpe_30d'],data['sharpe'][0]['sharpe_30d'])
        self.assertEqual(len(loaded['opportunities_all']),len(data['opportunities_all']))
        self.assertIsNone(load_rankings(rankings_signature(self.store,0.05)),'a new risk-free rate recalculates')
        self.store.setting('tcgcsv_dataset_marker','marker-2')
        self.assertIsNone(load_rankings(rankings_signature(self.store,0.0404)),'new synced data recalculates')

    def test_buy_list_annotations_filters_and_recommendations(self):
        fc_bins=[[b,1] for b in range(-20,40)]  # -10% .. +19.5%
        model={'horizon':14,'buckets':{'all':{'n':len(fc_bins),'bins':fc_bins}}}
        pricing=_test_pricing(fee_pct=10.0,cost=0.5,win_pct=50.0,sell_through=1.0,min_profit=0.0)
        rows=[{'name':'Cheap Listing','card_id':'c:1','price_type':'market_Normal','printing':'Normal','game':'MTG','flags':[],
               'latest_price':20.0,'low_price':17.0,'return_30d':5.0,'return_7d':1.0,'price_changes_30d':20},
              {'name':'Full Price','card_id':'c:2','price_type':'market_Normal','printing':'Normal','game':'MTG','flags':[],
               'latest_price':20.0,'low_price':20.0,'return_30d':5.0,'return_7d':1.0,'price_changes_30d':20},
              {'name':'Spike','card_id':'c:3','price_type':'market_Normal','printing':'Normal','game':'MTG','flags':['single jump'],
               'latest_price':20.0,'low_price':17.0,'return_30d':5.0,'return_7d':1.0,'price_changes_30d':20}]
        for row,values in zip(rows,annotate_with_pricing(rows,model,pricing)): row.update(values)
        cheap,full,_=rows
        self.assertTrue(cheap['buyable']); self.assertFalse(full['buyable'])
        self.assertGreater(cheap['exp_profit_low'],0); self.assertLess(full['exp_profit_low'],0)
        self.assertLess(full['max_buy'],full['latest_price'],'fees push Max buy below market')
        listed=buy_list(rows,'Expected profit buying now ($/copy)')
        self.assertEqual([r['name'] for r in listed],['Cheap Listing','Full Price'],'excluded spikes never appear')
        self.assertEqual([r['name'] for r in buy_list(rows,'Win @ low',buyable_only=True)],['Cheap Listing'])
        self.assertTrue(buy_recommendation(cheap,14).startswith('BUY NOW'))
        self.assertTrue(buy_recommendation(full,14).startswith('BUY-IN TARGET'))
        self.assertEqual([r['name'] for r in filter_ranked_rows(rows,min_rise=0.5)],['Cheap Listing','Full Price','Spike'])
        self.assertEqual(filter_ranked_rows(rows,min_rise=0.9),[])
        self.assertEqual([r['name'] for r in filter_ranked_rows(rows,buyable_only=True)],['Cheap Listing','Spike'])
        self.assertEqual(parse_filter_value('40%'),40.0)

    def test_ranking_filters_and_price_slider_scale(self):
        rows=[{'name':'a','latest_price':0.5,'sharpe_30d':3.0},{'name':'b','latest_price':5.0,'sharpe_30d':None},
              {'name':'c','latest_price':50.0,'sharpe_30d':12.0},{'name':'d','latest_price':500.0,'sharpe_30d':-1.0}]
        names=lambda **kw:[r['name'] for r in filter_ranked_rows(rows,**kw)]
        self.assertEqual(names(),['a','b','c','d'])
        self.assertEqual(names(price_min=1.0,price_max=100.0),['b','c'])
        self.assertEqual(names(sharpe_min=0.0),['a','c'],'a Sharpe bound drops rows without a Sharpe')
        self.assertEqual(names(sharpe_max=5.0),['a','d'])
        for price in (0.10,1.0,37.77,5000.0):
            self.assertAlmostEqual(slider_to_price(price_to_slider(price)),price,places=6)
        self.assertAlmostEqual(slider_to_price(0),PRICE_SLIDER_MIN); self.assertAlmostEqual(slider_to_price(100),PRICE_SLIDER_MAX)

    def test_rankings_list_each_printing_and_exclude_listing_spikes(self):
        today=datetime(2026,10,23,tzinfo=timezone.utc).date(); now=utc(); rows=[]; prices=[]
        for cid,name,base,low in [('tcgcsv:1:1','Clean Card',10.0,9.5),('tcgcsv:1:2','Thin Market',10.0,3.0),('tcgcsv:1:3','Bulk Card',0.30,0.25)]:
            rows.append((cid,'MTG',name,'SET','1','Rare','Normal','{}',now,'card'))
            foil=base*5
            for i in range(35):
                stamp=(today-timedelta(days=34-i)).isoformat()+'T20:00:00+00:00'
                foil*=1.012 if i%2 else 1.004
                prices.append((cid,'tcgcsv_tcgplayer','market_Normal','USD',base*(1.006 if i%3 else 1.012)**i,stamp,now))
                prices.append((cid,'tcgcsv_tcgplayer','market_Foil','USD',foil,stamp,now))
            prices.append((cid,'tcgcsv_tcgplayer','low_Normal','USD',low*1.3,today.isoformat()+'T20:00:00+00:00',now))
        self.store.batch(rows,prices)
        result=build_market_rankings(self.store,today)
        # Foils are their own rows, with their own spike checks (no foil low listing here, so all foils pass).
        self.assertEqual(sorted(r['name'] for r in result['sharpe']),
                         ['Bulk Card (Foil)','Clean Card','Clean Card (Foil)','Thin Market (Foil)'])
        self.assertEqual({r['name']:r['flags'] for r in result['excluded']},{'Thin Market':['market ≫ low'],'Bulk Card':['under $1']})
        foil=next(r for r in result['sharpe'] if r['name']=='Clean Card (Foil)')
        self.assertEqual((foil['card_id'],foil['printing'],foil['card_name']),('tcgcsv:1:1','Foil','Clean Card'))
        self.assertEqual(len(result['sharpe_all']),6)
        self.assertEqual(printing_label('Lugia','market_Holofoil'),'Lugia (Holofoil)')
        self.assertEqual(printing_label('Lugia','market_Normal'),'Lugia')

    def test_market_rankings_query_returns_only_fresh_singles(self):
        today=datetime(2026,10,23,tzinfo=timezone.utc).date()
        rows=[]; prices=[]; now=utc()
        for cid,name,kind in [('tcgcsv:1:1','Rising Card','card'),('tcgcsv:1:2','Flat Card','card'),('tcgcsv:1:3','Booster Box','sealed_product')]:
            rows.append((cid,'MTG',name,'SET','1','Rare','Normal','{}',now,kind))
            value=10.0
            for i in range(35):
                day=today-timedelta(days=34-i)
                if name=='Rising Card': value*=1.006 if i%3 else 1.012
                stamp=day.isoformat()+'T20:00:00+00:00'
                prices.append((cid,'tcgcsv_tcgplayer','market_Normal','USD',value,stamp,now))
        self.store.batch(rows,prices)
        result=build_market_rankings(self.store,today)
        self.assertEqual({r['name'] for r in result['fresh']},{'Rising Card','Flat Card'})
        self.assertEqual(result['sharpe'][0]['name'],'Rising Card')
        self.assertEqual(result['opportunities'][0]['name'],'Rising Card')

    def test_empty_rankings_explain_stored_market_data_and_show_diagnostics(self):
        diag=market_data_diagnostics(self.store,datetime(2026,10,23,tzinfo=timezone.utc).date())
        self.assertEqual(diag['total_cards'],0)
        self.assertEqual(diag['market_prices'],0)
        self.assertEqual(diag['recent_market_prices'],0)

    def test_rankings_return_diagnostics_and_fallback_candidates(self):
        today=datetime(2026,10,23,tzinfo=timezone.utc).date(); now=utc()
        row=('tcgcsv:1:99','MTG','History Needed Card','SET','99','Rare','Normal','{}',now,'card')
        price=('tcgcsv:1:99','tcgcsv_tcgplayer','market_Normal','USD',12.5,today.isoformat()+'T20:00:00+00:00',now)
        self.store.batch([row],[price])
        result=build_market_rankings(self.store,today)
        self.assertEqual(len(result['fresh']),1)
        self.assertEqual(len(result['opportunities']),0)
        self.assertEqual(result['fresh'][0]['name'],'History Needed Card')
        self.assertEqual(result['diagnostics'],{},'diagnostics are only computed when nothing is fresh')
        stale=build_market_rankings(self.store,today+timedelta(days=60))
        self.assertEqual(stale['fresh'],[])
        self.assertEqual(stale['diagnostics']['market_prices'],1)

    def test_long_read_scan_does_not_block_store(self):
        now=utc()
        self.store.batch([(f'tcgcsv:1:{i}','MTG',f'Card {i}','SET','1','Rare','Normal','{}',now,'card') for i in range(10)])
        with ReadOnlyStore() as reader:
            scan=reader.iter_q('SELECT id FROM cards',fetch_size=2)
            next(scan)  # scan in progress
            outcome=[]
            def gui_thread_query():
                outcome.append(self.store.lock.acquire(timeout=2))
                if outcome[-1]: self.store.lock.release()
            worker=threading.Thread(target=gui_thread_query); worker.start(); worker.join()
            self.assertEqual(outcome,[True])
            self.assertEqual(1+sum(1 for _ in scan),10)
            with self.assertRaises(sqlite3.OperationalError):
                reader.q("INSERT INTO settings VALUES('x','y')")

    def test_ranking_progress_reports_scanned_cards(self):
        today=datetime(2026,10,23,tzinfo=timezone.utc).date()
        now=utc(); row=('tcgcsv:3:100','Pokémon','Progress Card','SET','1','Rare','Normal','{}',now,'card')
        prices=[]
        for i in range(3):
            day=today-timedelta(days=2-i)
            prices.append(('tcgcsv:3:100','tcgcsv_tcgplayer','market_Normal','USD',10+i,day.isoformat()+'T20:00:00+00:00',now))
        self.store.batch([row],prices)
        events=[]
        build_market_rankings(self.store,today,progress=lambda current,total,phase: events.append((current,total,phase)))
        self.assertTrue(events)
        self.assertEqual(events[-1][:2],(1,1),'progress counts catalog cards scanned')

    def test_tcgcsv_group_with_product_without_price_variants_does_not_crash(self):
        def fake_json(url,allow_not_found=False):
            if url.endswith('/products'):
                return {'success':True,'results':[{'productId':9,'name':'Card Without Market Quote',
                    'extendedData':[{'name':'Number','value':'1/10'},{'name':'Rarity','value':'Rare'}]}]}
            if url.endswith('/prices'):
                return {'success':True,'results':[]}
            raise AssertionError('Unexpected URL '+url)
        with mock.patch.object(sys.modules[__name__],'tcgcsv_json',side_effect=fake_json), mock.patch.object(time,'sleep',return_value=None):
            count=ingest_tcgcsv(self.store,lambda _:None,3,'Pokémon',
                {'groupId':3170,'name':'Fixture Set','abbreviation':'FX'},'2026-10-23T20:00:00+00:00')
        self.assertEqual(count,1)
        self.assertEqual(self.store.q('SELECT COUNT(*) FROM cards')[0][0],1)
        self.assertEqual(self.store.q('SELECT COUNT(*) FROM prices')[0][0],0)

    def test_tcgcsv_ingest_classifies_products_and_stores_variants(self):
        def fake_json(url,allow_not_found=False):
            if url.endswith('/products'):
                return {'success':True,'results':[
                    {'productId':1,'name':'Lugia VSTAR','extendedData':[{'name':'Number','value':'139/195'},{'name':'Rarity','value':'Ultra Rare'}]},
                    {'productId':2,'name':'Silver Tempest Booster Box','extendedData':[]}]}
            if url.endswith('/prices'):
                return {'success':True,'results':[
                    {'productId':1,'subTypeName':'Holofoil','marketPrice':20.5,'lowPrice':18},
                    {'productId':2,'subTypeName':'Normal','marketPrice':100.0}]}
            raise AssertionError('Unexpected URL '+url)
        with mock.patch.object(sys.modules[__name__],'tcgcsv_json',side_effect=fake_json), mock.patch.object(time,'sleep',return_value=None):
            count=ingest_tcgcsv(self.store,lambda _:None,3,'Pokémon',{'groupId':3170,'name':'Silver Tempest','abbreviation':'SIT'},'2026-10-23T20:00:00+00:00')
        self.assertEqual(count,2)
        kinds=dict(self.store.q('SELECT name,item_type FROM cards'))
        self.assertEqual(kinds['Lugia VSTAR'],'card')
        self.assertEqual(kinds['Silver Tempest Booster Box'],'sealed_product')
        self.assertEqual(self.store.q('SELECT COUNT(*) FROM prices')[0][0],3)

    def test_daily_sync_both_games_and_marker_skip(self):
        marker='2026-10-23T20:06:07+0000'
        def fake_text(_): return marker
        def fake_json(url,allow_not_found=False):
            parts=url.rstrip('/').split('/')
            if parts[-1]=='groups':
                cat=int(parts[-2]); return {'success':True,'results':[{'groupId':cat*10,'name':'Fixture Set','abbreviation':'FX'}]}
            cat=int(parts[-3]); gid=int(parts[-2]); pid=cat*100+gid
            if parts[-1]=='products': return {'success':True,'results':[{'productId':pid,'name':f'Fixture {cat}','extendedData':[{'name':'Number','value':'1/1'},{'name':'Rarity','value':'Rare'}]}]}
            if parts[-1]=='prices': return {'success':True,'results':[{'productId':pid,'marketPrice':10.0,'subTypeName':'Normal'}]}
            raise AssertionError(url)
        with mock.patch.object(sys.modules[__name__],'tcgcsv_text',side_effect=fake_text), mock.patch.object(sys.modules[__name__],'tcgcsv_json',side_effect=fake_json) as json_mock, mock.patch.object(time,'sleep',return_value=None):
            first=sync_tcgcsv_daily(self.store,lambda _:None)
            second=sync_tcgcsv_daily(self.store,lambda _:None)
        n=len(TCGCSV_CATEGORIES)
        self.assertEqual(first,n)
        self.assertEqual(second,0)
        self.assertEqual(self.store.q('SELECT COUNT(*) FROM cards')[0][0],n)
        self.assertEqual(self.store.q('SELECT COUNT(*) FROM prices')[0][0],n)
        self.assertEqual(self.store.get_setting('tcgcsv_dataset_marker'),marker)
        self.assertEqual(json_mock.call_count,3*n,'unchanged marker should skip every category/group endpoint')
        # A game added after today's sync is fetched at once, the others are not touched again.
        self.store.setting('tcgcsv_categories',json.dumps([c for c,_g in TCGCSV_CATEGORIES if c!=89]))
        with mock.patch.object(sys.modules[__name__],'tcgcsv_text',side_effect=fake_text), mock.patch.object(sys.modules[__name__],'tcgcsv_json',side_effect=fake_json) as json_mock, mock.patch.object(time,'sleep',return_value=None):
            added=sync_tcgcsv_daily(self.store,lambda _:None)
        self.assertEqual((added,json_mock.call_count),(1,3))
        self.assertEqual(json.loads(self.store.get_setting('tcgcsv_categories')),sorted(c for c,_g in TCGCSV_CATEGORIES),'no game is forgotten')

    def test_unchanged_group_catalogs_are_not_refetched(self):
        markers=iter(['2026-10-23T20:00:00+0000','2026-10-24T20:00:00+0000'])
        calls=[]
        def fake_json(url,allow_not_found=False):
            parts=url.rstrip('/').split('/'); calls.append(parts[-1])
            if parts[-1]=='groups':
                cat=int(parts[-2])
                return {'success':True,'results':[
                    {'groupId':cat*10,'name':'Set','modifiedOn':'2026-10-01T00:00:00'},
                    {'groupId':cat*10+1,'name':'Empty Set','modifiedOn':'2026-10-01T00:00:00'}]}
            cat=int(parts[-3]); gid=int(parts[-2]); pid=cat*100
            if gid%10: return {'success':True,'results':[]}
            if parts[-1]=='products': return {'success':True,'results':[{'productId':pid,'name':'Card','extendedData':[{'name':'Rarity','value':'Rare'}]}]}
            return {'success':True,'results':[{'productId':pid,'marketPrice':10.0+len(calls),'subTypeName':'Normal'}]}
        with mock.patch.object(sys.modules[__name__],'tcgcsv_text',side_effect=lambda _:next(markers)), mock.patch.object(sys.modules[__name__],'tcgcsv_json',side_effect=fake_json), mock.patch.object(time,'sleep',return_value=None):
            first=sync_tcgcsv_daily(self.store,lambda _:None)
            calls.clear()
            second=sync_tcgcsv_daily(self.store,lambda _:None)
        n=len(TCGCSV_CATEGORIES)
        self.assertEqual((first,second),(n,n))
        self.assertEqual(sorted(calls),['groups']*n+['prices']*n,'only prices for unchanged non-empty groups')
        self.assertEqual(self.store.q('SELECT COUNT(*) FROM prices')[0][0],2*n)

    def test_unknown_priced_product_forces_catalog_refresh(self):
        calls=[]
        def fake_json(url,allow_not_found=False):
            calls.append(url.rsplit('/',1)[-1])
            if url.endswith('/products'): return {'success':True,'results':[{'productId':6,'name':'New Card','extendedData':[]}]}
            return {'success':True,'results':[{'productId':6,'marketPrice':1.0}]}
        with mock.patch.object(sys.modules[__name__],'tcgcsv_json',side_effect=fake_json):
            products,_=fetch_tcgcsv_group(1,{'groupId':5},catalog_current=True,known_ids={'tcgcsv:1:5'})
            self.assertEqual(calls,['prices','products'])
            self.assertEqual(len(products),1)
            calls.clear()
            products,_=fetch_tcgcsv_group(1,{'groupId':5},catalog_current=True,known_ids={'tcgcsv:1:6'})
            self.assertIsNone(products)
            self.assertEqual(calls,['prices'])

    def test_failed_sync_does_not_advance_marker(self):
        def fake_text(_): return '2026-10-24T20:00:00+0000'
        def fake_json(url,allow_not_found=False):
            if url.endswith('/groups') and '/3/' in url:
                raise RuntimeError('simulated Pokémon failure')
            if url.endswith('/groups'): return {'success':True,'results':[{'groupId':10,'name':'MTG Set'}]}
            if url.endswith('/products'): return {'success':True,'results':[]}
            raise AssertionError(url)
        with mock.patch.object(sys.modules[__name__],'tcgcsv_text',side_effect=fake_text), mock.patch.object(sys.modules[__name__],'tcgcsv_json',side_effect=fake_json), mock.patch.object(time,'sleep',return_value=None):
            with self.assertRaisesRegex(RuntimeError,'simulated Pokémon failure'):
                sync_tcgcsv_daily(self.store,lambda _:None)
        self.assertEqual(self.store.get_setting('tcgcsv_dataset_marker',''),'')

    def test_group_fetch_error_stops_sync(self):
        def fake_json(url,allow_not_found=False):
            if url.endswith('/groups'): return {'success':True,'results':[{'groupId':1},{'groupId':2}]}
            raise RuntimeError('simulated group failure')
        with mock.patch.object(sys.modules[__name__],'tcgcsv_text',return_value='m'), mock.patch.object(sys.modules[__name__],'tcgcsv_json',side_effect=fake_json):
            with self.assertRaisesRegex(RuntimeError,'simulated group failure'):
                sync_tcgcsv_daily(self.store,lambda _:None)
        self.assertEqual(self.store.get_setting('tcgcsv_dataset_marker',''),'')

    def test_tcgcsv_404_empty_group_and_429_stop(self):
        not_found=urllib.error.HTTPError('https://tcgcsv.com/tcgplayer/3/1/products',404,'Not Found',None,None)
        with mock.patch.object(sys.modules[__name__],'tcgcsv_fetch',side_effect=not_found) as opened, mock.patch.object(time,'sleep',return_value=None):
            self.assertEqual(tcgcsv_json('https://tcgcsv.com/tcgplayer/3/1/products',allow_not_found=True)['results'],[])
            self.assertEqual(opened.call_count,1)
        throttled=urllib.error.HTTPError('https://tcgcsv.com/tcgplayer/3/groups',429,'Too Many Requests',None,None)
        with mock.patch.object(sys.modules[__name__],'tcgcsv_fetch',side_effect=throttled) as opened, mock.patch.object(time,'sleep',return_value=None):
            with self.assertRaisesRegex(RuntimeError,'wait at least 10 minutes'):
                tcgcsv_json('https://tcgcsv.com/tcgplayer/3/groups')
            self.assertEqual(opened.call_count,1)
        with self.assertRaisesRegex(RuntimeError,'cooldown is active'):
            reserve_tcgcsv_request()

    def test_persistent_request_budget_stops_at_cap(self):
        with mock.patch.object(sys.modules[__name__],'TCGCSV_DAILY_REQUEST_BUDGET',2):
            self.assertEqual(reserve_tcgcsv_request(),1)
            self.assertEqual(reserve_tcgcsv_request(),2)
            with self.assertRaisesRegex(RuntimeError,'safety budget reached'):
                reserve_tcgcsv_request()

    def test_sync_lock_blocks_concurrent_run_without_deleting_owner_lock(self):
        lock_path=ROOT/'tcgcsv_sync.lock'
        with tcgcsv_sync_lock():
            self.assertTrue(lock_path.exists())
            with self.assertRaisesRegex(RuntimeError,'already appears to be running'):
                with tcgcsv_sync_lock(): pass
            self.assertTrue(lock_path.exists())
        self.assertFalse(lock_path.exists())

    def test_empty_group_does_not_request_prices(self):
        calls=[]
        def fake_json(url,allow_not_found=False):
            calls.append(url)
            return {'success':True,'results':[]}
        with mock.patch.object(sys.modules[__name__],'tcgcsv_json',side_effect=fake_json):
            count=ingest_tcgcsv(self.store,lambda _:None,1,'MTG',{'groupId':999,'name':'Empty'},'2026-10-23T20:00:00+00:00')
        self.assertEqual(count,0)
        self.assertEqual(len(calls),1)

    def test_tcgcsv_retries_transient_server_error(self):
        unavailable=urllib.error.HTTPError('https://tcgcsv.com/tcgplayer/3/groups',503,'Service Unavailable',None,None)
        success=json.dumps({'success':True,'results':[]}).encode()
        with mock.patch.object(sys.modules[__name__],'tcgcsv_fetch',side_effect=[unavailable,success]) as opened, mock.patch.object(time,'sleep',return_value=None):
            result=tcgcsv_json('https://tcgcsv.com/tcgplayer/3/groups')
        self.assertEqual(result['results'],[])
        self.assertEqual(opened.call_count,2)

    def test_marker_endpoint_429_is_reported_without_retry(self):
        throttled=urllib.error.HTTPError(TCGCSV_LAST_UPDATED,429,'Too Many Requests',None,None)
        with mock.patch.object(sys.modules[__name__],'tcgcsv_fetch',side_effect=throttled) as opened, mock.patch.object(time,'sleep',return_value=None):
            with self.assertRaisesRegex(RuntimeError,'wait at least 10 minutes'):
                tcgcsv_text(TCGCSV_LAST_UPDATED)
        self.assertEqual(opened.call_count,1)

    def test_stream_json_object_member_handles_chunk_boundaries(self):
        doc='{"meta":{"date":"2026-10-26","n":[1,2]}, "data": {"a":{"x":1.25},"b":{"y":[10,200]},"c":12345}}'
        for chunk in (1,2,3,7,64):
            got=list(stream_json_object_member(io.StringIO(doc),'data',chunk_size=chunk))
            self.assertEqual(got,[('a',{'x':1.25}),('b',{'y':[10,200]}),('c',12345)])
        with self.assertRaises(ValueError):
            list(stream_json_object_member(io.StringIO('{"meta":{}}'),'data'))

    def test_mtgjson_history_maps_tcgplayer_ids_and_feeds_rankings(self):
        ids_path=ROOT/'cardIdentifiers.csv.xz'
        with lzma.open(ids_path,'wt',encoding='utf-8',newline='') as f:
            f.write('uuid,scryfallId,tcgplayerProductId,tcgplayerEtchedProductId\nu1,s1,500,\nu2,s2,600,601\nu3,s3,,\n')
        ids=load_mtgjson_tcgplayer_ids(ids_path)
        self.assertEqual(ids,{'u1':{'normal':'500','foil':'500'},'u2':{'normal':'600','foil':'600','etched':'601'}})
        today=datetime(2026,10,23,tzinfo=timezone.utc).date(); stamp=today.isoformat()
        series={(today-timedelta(days=34-i)).isoformat():round(10*(1.01**i),2) for i in range(35)}
        doc={'meta':{'date':stamp},'data':{
            'u1':{'paper':{'tcgplayer':{'currency':'USD','retail':{'normal':series},'buylist':{'normal':{stamp:1.0}}},
                           'cardmarket':{'currency':'EUR','retail':{'normal':{stamp:99.0}}}}},
            'u2':{'paper':{'tcgplayer':{'currency':'USD','retail':{'etched':{stamp:5.0}}}}},
            'u9':{'paper':{'tcgplayer':{'currency':'USD','retail':{'normal':{stamp:7.0}}}}}}}
        prices_path=ROOT/'AllPrices.json.xz'
        with lzma.open(prices_path,'wt',encoding='utf-8') as f: json.dump(doc,f)
        now=utc()
        self.store.batch([('tcgcsv:1:500','MTG','History Card','SET','1','Rare','Normal','{}',now,'card'),
                          ('tcgcsv:1:601','MTG','Etched Card','SET','2','Rare','Foil','{}',now,'card')])
        self.assertEqual(ingest_mtgjson_prices(self.store,prices_path,ids,lambda _:None),(36,2))
        types=dict(self.store.q("SELECT card_id,GROUP_CONCAT(DISTINCT price_type) FROM prices WHERE source='mtgjson_tcgplayer' GROUP BY card_id"))
        self.assertEqual(types,{'tcgcsv:1:500':'market_Normal','tcgcsv:1:601':'market_Foil'})
        result=build_market_rankings(self.store,today)
        self.assertEqual(result['sharpe'][0]['card_id'],'tcgcsv:1:500')
        self.assertEqual(result['sharpe'][0]['obs_30d'],30)

    def test_windows_task_xml_is_valid_and_quotes_paths(self):
        import xml.etree.ElementTree as ET
        text=windows_task_xml(r'C:\Py\pythonw.exe',r'C:\My Apps\cmt & co\card.py',datetime(2026,10,26).date())
        root=ET.fromstring(text.split('?>',1)[1])
        ns={'t':'http://schemas.microsoft.com/windows/2004/02/mit/task'}
        self.assertEqual(root.find('.//t:Command',ns).text,r'C:\Py\pythonw.exe')
        self.assertEqual(root.find('.//t:Arguments',ns).text,'"C:\\My Apps\\cmt & co\\card.py" --sync')
        text=windows_task_xml(r'C:\Py\pythonw.exe',r'C:\cmt\card.py',datetime(2026,10,26).date(),data=r'D:\Card Data')
        root=ET.fromstring(text.split('?>',1)[1])
        self.assertEqual(root.find('.//t:Arguments',ns).text,'C:\\cmt\\card.py --sync --data "D:\\Card Data"')
        self.assertEqual([e.text for e in root.findall('.//t:StartBoundary',ns)],['2026-10-26T14:30:00','2026-10-26T22:00:00'])
        self.assertEqual(root.find('.//t:StartWhenAvailable',ns).text,'true')

    def test_pacing_counts_latency_toward_interval(self):
        globals()['_tcgcsv_last_request']=0.0
        slept=[]
        clock=iter([100.0,100.0, 100.05,100.11, 100.5,100.5]).__next__
        for _ in range(3): pace_tcgcsv_request(clock=clock,sleep=slept.append)
        self.assertEqual(len(slept),1)
        self.assertAlmostEqual(slept[0],0.06)

    def test_fetch_reuses_connection_and_decodes_gzip(self):
        body=gzip.compress(b'{"ok":1}')
        class FakeResponse:
            status=200; reason='OK'; will_close=False; headers={}
            def read(self): return body
            def getheader(self,name,default=None): return {'Content-Encoding':'gzip'}.get(name,default)
        conn=mock.Mock(); conn.sock=None; conn.getresponse.return_value=FakeResponse()
        vars(_tcgcsv_http).pop('conns',None)
        try:
            with mock.patch.object(http.client,'HTTPSConnection',return_value=conn) as factory:
                self.assertEqual(tcgcsv_fetch('https://tcgcsv.com/a','application/json',5),b'{"ok":1}')
                self.assertEqual(tcgcsv_fetch('https://tcgcsv.com/b','application/json',5),b'{"ok":1}')
            self.assertEqual(factory.call_count,1)
            self.assertEqual(conn.request.call_count,2)
        finally:
            vars(_tcgcsv_http).pop('conns',None)
    def test_sharpe_is_autocorrelation_adjusted_and_significance_tested(self):
        import random
        rng=random.Random(3); today=datetime(2026,10,23,tzinfo=timezone.utc).date()
        shocks=[rng.gauss(0.004,0.01) for _ in range(40)]
        # A 4-day moving average of the shocks: positively autocorrelated, like TCGplayer's smoothed "market" price.
        smooth=[sum(shocks[i-3:i+1])/4 for i in range(3,38)]
        price=10.0; points=[]
        for i,r in enumerate(smooth):
            price*=math.exp(r); points.append(((today-timedelta(days=len(smooth)-1-i)).isoformat()+'T20:00:00+00:00',price))
        m=calculate_market_metrics(points,today)
        rets=[math.log(b[1]/a[1]) for a,b in zip(points[-30:],points[-29:])]
        naive=statistics.mean(rets)/statistics.stdev(rets)*math.sqrt(365)
        self.assertGreater(m['autocorr_1'],0.3)
        self.assertLess(abs(m['sharpe_30d']),abs(naive)*0.8,'autocorrelated returns must not get the full √365 scaling')
        self.assertTrue(0.0<=m['psr']<=1.0)
        self.assertEqual(m['psr']>0.5,m['sharpe_30d']>0)
        q=benjamini_hochberg([0.01,0.04,0.03,None,0.5])
        self.assertIsNone(q[3])
        for got,want in zip((q[0],q[1],q[2],q[4]),(0.04,0.04*4/3,0.04*4/3,0.5)): self.assertAlmostEqual(got,want)
        lo,hi=wilson_interval(0.5,100); self.assertTrue(lo<0.5<hi and hi-lo<0.2)
    def test_forecast_buckets_shrink_toward_parents_and_calibrate(self):
        model={'horizon':14,'buckets':{
            'all':{'n':1000,'bins':[[-20,500],[20,500]]},
            '4|1|N':{'n':0,'bins':[]},
            '4|1':{'n':30,'bins':[[20,30]]},
            't1':{'n':1000,'bins':[[-20,500],[20,500]]}}}
        fc=forecast_for(model,15.0,None,5.0,'Normal')
        self.assertEqual(fc['key'],'4|1')
        p=forecast_prob_above(fc,0.0)
        self.assertAlmostEqual(p,(30+FORECAST_PRIOR*0.5)/(30+FORECAST_PRIOR),'30 all-up samples are pulled toward the 50% parent')
        knots=isotonic_calibration([(0.2,100,30),(0.4,100,20),(0.6,100,50),(0.8,100,60)])
        rates=[k[1] for k in knots]; self.assertEqual(rates,sorted(rates))
        self.assertEqual((knots[0],knots[-1]),([0.0,0.0],[1.0,1.0]))
        for y in (0.1,0.3,0.55,0.9):
            self.assertAlmostEqual(apply_calibration(knots,invert_calibration(knots,y)),y,places=6)
        calibrated={k:v for k,v in model.items() if not k.startswith('_')}; calibrated['calibration_map']=[[0.0,0.0],[0.5,0.3],[1.0,1.0]]
        cfc=forecast_for(calibrated,None,None,50.0,'Normal')  # tier 2 has no bucket: the 50/50 'all' bucket
        self.assertAlmostEqual(forecast_prob_above(cfc,0.0),0.3)
        self.assertLess(forecast_mean(cfc),0.0,'the calibrated distribution shifts its mean down too')
        self.assertLess(forecast_quantile(cfc,0.5),0.0)
    def test_rankings_scan_reads_lows_sets_and_builds_indices(self):
        today=datetime(2026,10,23,tzinfo=timezone.utc).date(); now=utc(); rows=[]; prices=[]
        for k in range(30):
            cid=f'tcgcsv:1:{k}'; rows.append((cid,'MTG',f'Card {k}','ABC' if k<15 else 'XYZ','1','Rare','Normal','{}',now,'card'))
            for i in range(40):
                stamp=(today-timedelta(days=39-i)).isoformat()+'T20:00:00+00:00'
                prices.append((cid,'tcgcsv_tcgplayer','market_Normal','USD',5.0*(1.01**i if k<15 else 0.995**i),stamp,now))
            prices.append((cid,'tcgcsv_tcgplayer','low_Normal','USD',4.0,(today-timedelta(days=9)).isoformat()+'T20:00:00+00:00',now))
            prices.append((cid,'tcgcsv_tcgplayer','low_Normal','USD',4.5,today.isoformat()+'T20:00:00+00:00',now))
        self.store.batch(rows,prices)
        data=build_market_rankings(self.store,today)
        r=next(x for x in data['fresh'] if x['name']=='Card 0')
        self.assertEqual((r['low_price'],r['set_code'],r['observations']),(4.5,'ABC',36),'newest low; metrics use the latest 35 days')
        mtg=data['indices']['MTG']
        self.assertEqual(len(mtg),40)
        self.assertAlmostEqual(mtg[-1][1]/mtg[-2][1],math.exp((15*math.log(1.01)+15*math.log(0.995))/30),places=3)  # prices kept in cents
        self.assertEqual(mtg[-1][3:],[30,15,15])
        summary={s['set_code']:s for s in set_summary(data['fresh'])}
        self.assertAlmostEqual(summary['ABC']['change_7d'],(1.01**7-1)*100,delta=0.1)  # cents rounding
        self.assertLess(summary['XYZ']['change_30d'],0)
        s=index_summary(mtg); self.assertAlmostEqual(s['ew'],mtg[-1][1]); self.assertIsNotNone(s['ew_30d'])
    def test_movers_breadth_and_position_signals(self):
        rows=[{'name':n,'game':'MTG','latest_price':p,'return_7d':r7,'price_changes_30d':c,'flags':f,'drawdown_30d':0.0,'obs_30d':30}
              for n,p,r7,c,f in [('Up',10,12.0,10,[]),('Down',10,-8.0,10,[]),('Cheap',2,40.0,10,[]),('Thin',10,30.0,2,[]),('Spike',10,90.0,10,['single jump'])]]
        gainers,losers=market_movers(rows)
        self.assertEqual([r['name'] for r in gainers],['Up']); self.assertEqual([r['name'] for r in losers],['Down'])
        self.assertEqual(market_breadth(rows)['MTG']['n'],4)
        pricing=_test_pricing(fee_pct=10.0,cost=0.5,horizon=14)
        t={'quick_sell':9.9,'exp_sale_net':10.5,'max_qty':3}
        self.assertEqual(position_signal(10.0,10.0,2,8.0,t,pricing)[0],'HOLD')
        self.assertEqual(position_signal(10.0,10.0,9,8.0,t,pricing)[0],'TRIM')
        self.assertEqual(position_signal(10.0,10.0,2,8.0,dict(t,exp_sale_net=7.0),pricing)[0],'SELL')
        self.assertEqual(alert_hits(12.0,11.0,None),['≥ $11.00']); self.assertEqual(alert_hits(12.0,None,11.0),[])
    def test_catalyst_calendar_portfolio_migration_and_alerts(self):
        today=datetime(2026,10,23,tzinfo=timezone.utc).date()
        store_set_info(self.store,tcgcsv_group_set_rows('MTG',[{'groupId':1,'name':'Duskmourn','abbreviation':'DSK','publishedOn':'2026-11-01T00:00:00'},
                                                                 {'groupId':2,'name':'Old Set','abbreviation':'OLD','publishedOn':'2020-01-01T00:00:00'}]))
        store_set_info(self.store,[('MTG','DSK','Duskmourn','2026-11-01','expansion','scryfall')])
        cal=catalyst_calendar(self.store,today)
        self.assertEqual([(c['set_code'],c['source'],c['days']) for c in cal],[('DSK','scryfall',9)],'one row per set, Scryfall preferred')
        self.store.close()
        con=sqlite3.connect(DB)
        with con: con.execute("INSERT INTO watchlist VALUES('tcgcsv:1:1','2026-10-01')")
        con.close()
        self.store=Store()
        self.assertEqual(self.store.q('SELECT card_id,price_type,qty FROM portfolio'),[('tcgcsv:1:1','',0)])
        self.assertEqual(self.store.q('SELECT COUNT(*) FROM watchlist')[0][0],0)
        now=utc(); prices=[]
        self.store.batch([('tcgcsv:1:1','MTG','Alert Card','DSK','1','Rare','Normal','{}',now,'card')])
        for i in range(35):
            prices.append(('tcgcsv:1:1','tcgcsv_tcgplayer','market_Normal','USD',10+i*0.1,
                           (datetime.now(timezone.utc).date()-timedelta(days=34-i)).isoformat()+'T20:00:00+00:00',now))
        self.store.batch([],prices)
        self.store.execute("UPDATE portfolio SET alert_above=12")
        risk_free=float(DEFAULT_RISK_FREE_PCT)/100
        save_rankings(build_market_rankings(self.store,risk_free=risk_free),rankings_signature(self.store,risk_free))
        self.assertEqual(report_portfolio_alerts(self.store,lambda _m:None),['ALERT Alert Card: market $13.40 ≥ $12.00'])
    def test_positions_brief_and_sellable_quantity(self):
        self.assertEqual([poisson_even_odds_count(r) for r in (0.2,0.93,4.67,10.0)],[0,1,4,10])
        now=utc(); today=datetime.now(timezone.utc).date(); prices=[]
        self.store.batch([('tcgcsv:1:7','MTG','Brief Card','ABC','1','Rare','Normal','{}',now,'card')])
        for i in range(35):
            prices.append(('tcgcsv:1:7','tcgcsv_tcgplayer','market_Normal','USD',20*(1.004 if i%2 else 1.001)**i,
                           (today-timedelta(days=34-i)).isoformat()+'T20:00:00+00:00',now))
        prices.append(('tcgcsv:1:7','tcgcsv_tcgplayer','low_Normal','USD',14.0,today.isoformat()+'T20:00:00+00:00',now))
        self.store.batch([],prices)
        self.store.execute("INSERT INTO portfolio(card_id,price_type,qty,cost,alert_below,added_at) VALUES('tcgcsv:1:7','market_Normal',3,12.0,30.0,?)",(now,))
        data=build_market_rankings(self.store,today,risk_free=0.04)
        model={'horizon':14,'buckets':{'all':{'n':100,'bins':[[b,1] for b in range(-50,50)]}}}
        pricing=dict(DEFAULT_PRICING,played_ratio=0.65)  # the $14 low counts as Near Mint
        for row,values in zip(data['fresh'],annotate_with_pricing(data['fresh'],model,pricing)): row.update(values)
        index={(r['card_id'],r['price_type']):r for r in data['fresh']}
        pos=compute_positions(self.store,index,{'tcgcsv:1:7':data['fresh']},model,pricing)[0]
        self.assertEqual((pos['qty'],pos['alerts']),(3,['≤ $30.00']))
        unit=sale_net(14.0*0.99,pricing)
        self.assertAlmostEqual(pos['value'],3*unit); self.assertAlmostEqual(pos['pnl'],3*unit-36.0)
        html=daily_brief_html(data,model,pricing,[pos],[],{})
        for needle in ('Portfolio alerts','Brief Card','Buy now (a listing','Top losers','How to read this','name="viewport"'):
            self.assertIn(needle,html)
        self.assertTrue(html.startswith('<!doctype html>'))
        fc=forecast_for(model,None,None,20.0,'Normal')
        a=pricing_targets(20.0,15.0,fc,pricing,10); b=pricing_targets(20.0,15.0,fc,pricing,10)
        self.assertEqual(a,b,'per-bucket memoization returns identical results')
    def test_condition_shipping_and_position_sizing(self):
        p=dict(DEFAULT_PRICING)
        self.assertAlmostEqual(selling_costs(10.0,p),0.30+1.00+0.25)
        self.assertAlmostEqual(selling_costs(60.0,p),0.30+4.50+0.25,msg='tracked shipping from the threshold')
        self.assertAlmostEqual(selling_costs(3.0,p),0.30+1.00-0.99*(1-0.1325)+0.25,msg='buyer pays shipping on small orders')
        self.assertAlmostEqual(sale_net(100.0,p),100*(1-0.1325)-5.05)
        self.assertEqual([implied_condition(low,10.0,p) for low in (9.0,8.0,7.0,6.0,3.0,None)],['NM','NM','MP','HP','DMG','NM'])
        self.assertEqual(implied_condition(1.60,2.00,p),'NM','a 40¢ gap on a cheap card is noise')
        arb={'buylist':30.0,'low_price':20.0,'low_cond':'NM','return_30d':0,'buylist_change_30d':0}
        self.assertTrue(buylist_signals(arb,p)[0].startswith('ARB'))
        self.assertEqual(buylist_signals(dict(arb,buylist=21.5),p),[],'a spread under your minimum profit is not arbitrage')
        self.assertEqual(buylist_signals(dict(arb,buylist=3300.0,low_price=2500.0),p),[],'over your per-card limit')
        fc={'key':'all','n':100,'bins':[[b,1] for b in range(-20,60)],'horizon':14}
        t=pricing_targets(40.0,28.0,fc,p,20)
        by=t['max_buy_cond']
        self.assertEqual(t['low_cond'],'MP')
        self.assertTrue(by['NM']>by['LP']>by['MP']>by['HP'],'worse condition, lower max buy')
        free=pricing_targets(40.0,28.0,fc,_test_pricing(),20)
        self.assertGreater(free['max_buy'],t['max_buy'],'shipping and the per-order fee lower what you can pay')
        self.assertLess(t['win_at_low'],pricing_targets(40.0,28.0,fc,dict(p,played_ratio=0.5),20)['win_at_low'],
                        'a played-looking low is valued as played')
        buy=by['MP']*0.8
        qty,limit=suggested_quantity(t,buy,40.0*p['cond_MP'],dict(p,max_card=60.0))
        self.assertEqual((qty,limit),(int(60.0//(buy+p['ship_in'])),'card limit'))
        self.assertEqual(suggested_quantity(t,buy,40.0*p['cond_MP'],dict(p,max_card=60.0),held_card=60.0),(0,'card limit'))
        self.assertEqual(suggested_quantity(t,buy,40.0*p['cond_MP'],p,held_set=750.0)[1],'set limit')
        self.assertEqual(suggested_quantity(t,40.0,40.0,p),(0,'no edge'),'paying full market loses after costs')
        positions=[{'card_id':'a','price_type':'market_Normal','game':'MTG','set_code':'ABC','qty':10,'market':40.0,'cost':30.0,
                    'signal':'HOLD','detail':'ok'},
                   {'card_id':'b','price_type':'market_Normal','game':'MTG','set_code':'ABC','qty':20,'market':30.0,'cost':20.0,
                    'signal':'HOLD','detail':'ok'}]
        apply_position_limits(positions,dict(p,max_card=500.0,max_set_pct=15.0))
        self.assertEqual([x['signal'] for x in positions],['TRIM','TRIM'])
        self.assertIn('set ABC is 20% of capital',positions[0]['detail'])
        exp=portfolio_exposure(positions)
        self.assertEqual((exp['total'],exp['sets'][('MTG','ABC')]),(700.0,700.0))
        self.store.execute("DELETE FROM settings WHERE key='pricing_version'"); self.store.setting('pricing_cost','0.75')
        self.store.close(); self.store=Store()
        self.assertEqual(float(self.store.get_setting('pricing_cost')),DEFAULT_PRICING['cost'],'old all-in default migrates')
        self.store.setting('pricing_cost','0.6'); self.store.execute("DELETE FROM settings WHERE key='pricing_version'")
        self.store.close(); self.store=Store()
        self.assertEqual(self.store.get_setting('pricing_cost'),'0.6','a custom cost is kept')
    def test_backtest_is_walk_forward_and_scores_strategies(self):
        pricing=_test_pricing(win_pct=60.0,sell_through=0.5,horizon=14,min_profit=0.0)
        anchors=list(range(100,161,3))
        hist={a:{'all':{40 if a<140 else -100:6000}} for a in anchors}  # +20% early, -50% from day 140 on
        cases={a:[] for a in anchors}; cases[145]=[('Normal',0.0,0.0,10.0,12.0,20,None,None,None,None)]
        out=_run_strategies(anchors,hist,cases,14,date.fromordinal(170),pricing)
        r=out['strategies']['Buy-ins at Max buy · this model']
        self.assertEqual(r['trades'],1)
        self.assertAlmostEqual(r['total_pnl'],0.0,places=6,msg='day 145 trades only on outcomes known by then (+20%), never the later −50%')
        self.assertIsNone(out['strategies']['Buy now at cheapest listing · this model'],'no recorded listing, no buy-now trade')
        # Full pipeline: one scan builds rankings, models and the backtest; it is saved and reloaded for the same assumptions.
        import random
        rng=random.Random(5); latest=datetime.now(timezone.utc).date(); now=utc(); cards=[]; prices=[]
        for k in range(120):
            cid=f'tcgcsv:1:{k}'; price=6.0+k%7; drift=0.01 if k%2 else -0.006
            cards.append((cid,'MTG',f'BT {k}','SET','1','Rare','Normal','{}',now,'card'))
            for d in range(120,-1,-1):
                price*=1.0+drift+rng.uniform(-0.01,0.01)
                prices.append((cid,'tcgcsv_tcgplayer','market_Normal','USD',price,(latest-timedelta(days=d)).isoformat()+'T20:00:00+00:00',now))
        self.store.batch(cards,prices)
        full=dict(DEFAULT_PRICING); old_min=BACKTEST_MIN_TRAIN; globals()['BACKTEST_MIN_TRAIN']=200  # a small test market
        try:
            with ReadOnlyStore() as reader:
                data,models,bt=build_market_views(reader,0.04,latest.isoformat(),pricing=full)
                alone=run_strategy_backtest(reader,full,latest.isoformat())
        finally: globals()['BACKTEST_MIN_TRAIN']=old_min
        self.assertIsNotNone(models); self.assertGreater(bt['strategies']['Buy every card at market · no model']['trades'],0)
        self.assertEqual({k:(v or {}).get('trades') for k,v in bt['strategies'].items()},
                         {k:(v or {}).get('trades') for k,v in alone['strategies'].items()},'shared scan = separate scan')
        save_backtest(bt)
        self.assertIsNotNone(load_backtest(latest.isoformat(),full))
        self.assertIsNone(load_backtest(latest.isoformat(),dict(full,ship_in=2.0)),'new cost assumptions rebuild the backtest')
        self.assertLess(bt['strategies']['Buy every card at market · no model']['roi'],0,'buying at market loses to costs')
    def test_trade_log_ledger_and_learning(self):
        now=utc(); self.store.batch([('tcgcsv:1:9','MTG','Ledger Card','SET','1','Rare','Normal','{}',now,'card')])
        record_trade(self.store,'tcgcsv:1:9','market_Normal','BUY',2,10.0,'NM',None,1.0,'2026-10-01',11.0,1.5,0.62)
        record_trade(self.store,'tcgcsv:1:9','market_Normal','BUY',2,14.0,'NM',None,0.0,'2026-10-05',14.5,0.5,0.55)
        self.assertEqual(self.store.q("SELECT qty,cost FROM portfolio WHERE card_id='tcgcsv:1:9'"),[(4,12.25)])
        record_trade(self.store,'tcgcsv:1:9','market_Normal','SELL',3,20.0,'LP',6.0,3.0,'2026-10-20',25.0)
        self.assertEqual(self.store.q("SELECT qty FROM portfolio WHERE card_id='tcgcsv:1:9'")[0][0],1)
        with self.assertRaises(ValueError): record_trade(self.store,'tcgcsv:1:9','market_Normal','SELL',2,20.0)
        cols=('id','card_id','price_type','side','qty','price','condition','fees','shipping','traded_on','market','predicted_profit')
        trades=[dict(zip(cols,r)) for r in self.store.q(f"SELECT {','.join(cols)} FROM trades")]
        ledger=trade_ledger(trades)
        sale=ledger['sales'][0]
        self.assertAlmostEqual(sale['pnl'],60-6-3-3*12.25)
        self.assertAlmostEqual(sale['predicted'],3*1.0,msg='average predicted profit of the copies sold')
        self.assertEqual(ledger['open'][('tcgcsv:1:9','market_Normal')][0],1)
        learned=learn_from_trades(trades,dict(DEFAULT_PRICING))
        self.assertAlmostEqual(learned['cond_LP'][0],round((0.8+5*0.85)/6,3))
        self.assertAlmostEqual(learned['fee_pct'][0],round((10.0+5*13.25)/6,2))
        self.assertAlmostEqual(learned['ship_in'][0],round((0.5+0.0+5*0.5)/7,2))
        self.assertNotIn('sell_through',learned,'no liquidity recorded on these buys')
        record_trade(self.store,'tcgcsv:1:9','market_Normal','BUY',2,10.0,'NM',None,0.0,'2026-10-21',10.0,None,None,'',15)
        record_trade(self.store,'tcgcsv:1:9','market_Normal','SELL',3,12.0,'NM',1.0,1.0,'2026-10-31',12.0)
        cols2=cols+('changes',)
        trades=[dict(zip(cols2,r)) for r in self.store.q(f"SELECT {','.join(cols2)} FROM trades")]
        learned=learn_from_trades(trades,dict(DEFAULT_PRICING))
        self.assertIn('sell_through',learned); self.assertGreater(learned['sell_through'][0],0)
    def test_variants_are_detected_and_adapt(self):
        self.assertEqual(variant_of('MTG','Sol Ring - Dwarven (0409) (Serial Numbered)'),'Serial Numbered')
        self.assertEqual(variant_of('MTG','Brims Barone (Showcase) (Galaxy Foil)'),'Showcase + Galaxy Foil')
        self.assertEqual(variant_of('MTG','Lightning Bolt'),'Regular')
        self.assertEqual(variant_of('MTG','Plains (A)'),'Regular','single-letter art codes are not treatments')
        self.assertEqual(variant_of('Pokémon','Charizard ex - 199/165','Special Illustration Rare'),'Special Illustration Rare')
        self.assertEqual(variant_of('Pokémon','Pikachu (Cosmos Holo)','Rare'),'Rare · Cosmos Holo')
        keys=forecast_keys(0.05,0.0,20.0,'Normal',20,0.02,'Borderless')
        self.assertTrue(keys[0].endswith('|T:Borderless') and keys[-1]=='all')
        self.assertEqual(forecast_keys(0.05,0.0,20.0,'Normal',20,0.02,'Regular'),forecast_keys(0.05,0.0,20.0,'Normal',20,0.02),'Regular adds no level')
        # A variant with no history of its own borrows the general bucket; with enough outcomes it follows its own.
        general=keys[1]
        model={'horizon':14,'variants':['Borderless'],'buckets':{'all':{'n':1000,'bins':[[-10,500],[10,500]]},general:{'n':1000,'bins':[[-10,500],[10,500]]},
                                       keys[0]:{'n':5000,'bins':[[30,5000]]}}}
        self.assertGreater(forecast_prob_above(forecast_for(model,5.0,0.0,20.0,'Normal',20,0.02,'Borderless'),0.0),0.9)
        self.assertAlmostEqual(forecast_prob_above(forecast_for(model,5.0,0.0,20.0,'Normal',20,0.02,'Retro Frame'),0.0),0.5,places=2)
        rows=[{'game':'MTG','variant':'Borderless','name':'A (Borderless)','latest_price':10.0,'set_code':'X'}]
        self.assertEqual(record_new_variants(self.store,rows),[],'the first run only learns what exists')
        rows.append({'game':'MTG','variant':'Fracture Foil','name':'B (Fracture Foil)','latest_price':25.0,'set_code':'NEW'})
        self.assertEqual(record_new_variants(self.store,rows),[('MTG','Fracture Foil')])
        self.assertEqual(self.store.q("SELECT kind,subject FROM market_events"),[('new variant','Fracture Foil')])
        summary={v['set_code']:v for v in variant_summary([dict(r,flags=[],return_7d=1.0,return_30d=2.0,price_changes_30d=5) for r in rows])}
        self.assertEqual(set(summary),{'Borderless','Fracture Foil'})
    def test_minimum_profit_hides_trades_not_worth_handling(self):
        model={'horizon':14,'buckets':{'all':{'n':60,'bins':[[b,1] for b in range(-20,40)]}}}
        row={'name':'Thin Edge','card_id':'c:9','price_type':'market_Normal','printing':'Normal','game':'MTG','flags':[],
             'latest_price':3.0,'low_price':2.9,'return_30d':5.0,'return_7d':1.0,'price_changes_30d':20}
        prices={}
        for floor,roi in ((0.0,0.0),(0.5,0.0),(0.0,25.0),(5.0,0.0)):
            r=dict(row); r.update(annotate_with_pricing([r],model,_test_pricing(min_profit=floor,min_roi=roi,win_pct=50.0))[0])
            shown=buy_list([r],'Win @ low'); prices[(floor,roi)]=r['max_buy']
            if shown:  # Max buy itself leaves the minimum profit, so every row shown clears both floors
                cost=r['max_buy']
                self.assertGreaterEqual(r['exp_profit_max_buy']+1e-9,max(floor,roi/100*cost),(floor,roi))
        self.assertLess(prices[(0.5,0.0)],prices[(0.0,0.0)]); self.assertLess(prices[(0.0,25.0)],prices[(0.0,0.0)])
        self.assertIsNone(prices[(5.0,0.0)],'a $3 card cannot leave $5 of profit: no buy price')
        self.assertTrue(worth_it(4.0,40.0,{'min_profit':1.0,'min_roi':10.0})); self.assertFalse(worth_it(3.9,40.0,{'min_profit':1.0,'min_roi':10.0}))
    def test_release_cycle_curves_phase_and_presell(self):
        self.assertEqual([release_phase(a) for a in (-10,0,13,14,41,42,90,91,None)],[0,1,1,2,2,3,3,None,None])
        new=forecast_keys(0.05,0.0,20.0,'Normal',20,0.02,None,5); old=forecast_keys(0.05,0.0,20.0,'Normal',20,0.02,None,200)
        self.assertTrue(all('|P1' in k for k in new[:-2]) and 'L2' in new and new[-1]=='all')
        self.assertEqual(old,forecast_keys(0.05,0.0,20.0,'Normal',20,0.02),'mature cards keep their keys')
        today=datetime.now(timezone.utc).date(); release=today-timedelta(days=60); now=utc(); cards=[]; prices=[]
        store_set_info(self.store,[('MTG','NEW','New Set',release.isoformat(),'expansion','scryfall')])
        for k in range(40):
            cid=f'tcgcsv:1:{900+k}'; cards.append((cid,'MTG',f'New {k}','NEW','1','Rare','Normal','{}',now,'card'))
            for d in range(-30,61):  # presale hype, a drop at release, then a slow slide
                price=10.0*(2.0 if d<-7 else 1.5 if d<0 else 0.7 if d<20 else 0.6)
                prices.append((cid,'tcgcsv_tcgplayer','market_Normal','USD',price,(release+timedelta(days=d)).isoformat()+'T20:00:00+00:00',now))
        self.store.batch(cards,prices)
        curves=release_curves(self.store,today,dict(DEFAULT_PRICING))
        c=curves['MTG · regular']
        self.assertAlmostEqual(curve_change(c['curve'],-3,14),(0.7/1.5-1)*100,places=6)
        self.assertAlmostEqual(curve_change(c['curve'],0,30),(0.6/0.7-1)*100,places=6)
        trades={t['name']:t for t in c['trades']}
        self.assertGreater(trades['Pre-sell 7 days before release (vs selling on day 14)']['median'],0)
        self.assertLess(trades['Buy on release day, sell on day 30']['median'],0)
        rows=[{'game':'MTG','variant':'Regular','name':'Presale Card','card_id':'x','price_type':'market_Normal','flags':[],
               'latest_price':30.0,'days_since_release':-10}]
        opps=release_opportunities(rows,dict(DEFAULT_PRICING),curves)
        self.assertEqual([o['action'] for o in opps],['PRE-SELL'])
        self.assertEqual(buy_list([dict(rows[0],max_buy=10.0,worth=True)],'Win @ low',hide_reprints=True),[],'new sets are hidden while they slide')
    def test_plain_language_decisions(self):
        model={'horizon':14,'buckets':{'all':{'n':60,'bins':[[b,1] for b in range(-20,40)]}}}  # -10% .. +19.5%
        row={'name':'Check Card','card_name':'Check Card','card_id':'tcgcsv:1:5','price_type':'market_Normal','printing':'Normal','game':'MTG',
             'flags':[],'latest_price':40.0,'low_price':38.0,'return_30d':2.0,'return_7d':0.5,'price_changes_30d':20,'variant':'Regular','observations':40}
        p=dict(DEFAULT_PRICING)
        limit=pricing_targets(40.0,38.0,forecast_for(model,2.0,0.5,40.0,'Normal',20),p,20)['max_buy']
        self.assertEqual(decide_buy(row,model,p,'NM',round(limit-1,2))['verdict'],'YES')
        self.assertEqual(decide_buy(row,model,p,'NM',45.0)['verdict'],'NO')
        self.assertIn('Offer at most',decide_buy(row,model,p,'NM',45.0)['headline'])
        self.assertEqual(decide_buy(dict(row,flags=['market ≪ low']),model,p,'NM',10.0)['verdict'],'NO','untrustworthy prices are never a buy')
        self.assertEqual(decide_buy(dict(row,days_since_release=5),model,p,'NM',10.0)['verdict'],'NO','new sets are not bought while sliding')
        self.assertEqual(decide_buy(dict(row,banned='Pio,Mod'),model,p,'NM',round(limit-1,2))['verdict'],'YES','a standing ban is already priced in')
        recent=decide_buy(dict(row,legal_change='Banned/restricted in Mod (2026-10-20)'),model,p,'NM',round(limit-1,2))
        self.assertEqual(recent['verdict'],'YES'); self.assertTrue(any('legality just changed' in d for d in recent['details']),'a recent change is flagged, not blocked')
        sell=decide_sell(row,model,p,'NM',30.0)
        self.assertIn(sell['verdict'],('SELL','LIST HIGH')); self.assertTrue(any('profit on your $30.00 cost' in d for d in sell['details']))
        self.assertEqual(decide_buy(dict(row,observations=40),None,p,'NM',10.0)['verdict'],'NO DATA')
        young=decide_buy(dict(row,observations=2,game='Pokémon',latest_date='2026-10-27'),model,p,'NM',10.0)
        self.assertEqual(young['verdict'],'NOT YET'); self.assertIn('2026-11-24',young['headline'])
        self.assertEqual(decide_sell(dict(row,observations=2),model,p,'NM')['verdict'],'NOT YET')
        rows=[dict(row,max_buy=limit,buyable=False,worth=True,qty=2,exp_profit_max_buy=5.0,win=0.8,target_sell=42.0,
                   max_buy_cond={'NM':limit,'LP':limit*0.8,'MP':limit*0.6})]
        pos=[{'id':'tcgcsv:1:5#market_Normal','name':'Check Card','qty':3,'signal':'SELL','detail':'quick sale beats holding','market':40.0,'alerts':[]}]
        acts=todays_actions(rows,pos,p)
        self.assertEqual([a['action'] for a in acts],['SELL','TRADE-IN PRICE'],'your sells come first')
        self.assertEqual(confidence_label(0.85),'High'); self.assertEqual(confidence_label(0.7),'Medium'); self.assertEqual(confidence_label(0.4),'Low')
    def test_crossover_names_match_the_original_card(self):
        self.assertEqual(mtg_name_keys('Khan, Engineered Evil - Sheoldred, the Apocalypse (Borderless)'),
                         ['khan, engineered evil - sheoldred, the apocalypse','sheoldred, the apocalypse'])
        rows=[{'game':'MTG','card_name':'Sheoldred, the Apocalypse','name':'Sheoldred, the Apocalypse','variant':'Regular','printing':'Normal',
               'flags':[],'latest_price':80.0,'days_since_release':400},
              {'game':'MTG','card_name':'Khan, Engineered Evil - Sheoldred, the Apocalypse','name':'Khan','variant':'Regular','printing':'Normal',
               'flags':[],'latest_price':200.0,'days_since_release':-17,'card_id':'k','price_type':'market_Normal'}]
        curves={'MTG · regular':{'cards':100,'sets':['X'],'curve':[[d,(-0.84 if d>=0 else 0.0),-0.9,-0.8,100] for d in range(-30,91)],'trades':[]}}
        o=release_opportunities(rows,dict(DEFAULT_PRICING),curves)[0]
        self.assertAlmostEqual(o['move'],(80/200-1)*100,msg='a crossover reprint settles near the original card, not 84% lower')
    def test_portable_copy_carries_everything_needed(self):
        now=utc(); self.store.batch([('tcgcsv:1:3','MTG','Carry Card','SET','1','Rare','Normal','{}',now,'card')],
                                    [('tcgcsv:1:3','tcgcsv_tcgplayer','market_Normal','USD',5.0,'2026-10-20T20:00:00+00:00',now)])
        self.store.execute("INSERT INTO portfolio(card_id,price_type,qty,cost,added_at) VALUES('tcgcsv:1:3','market_Normal',2,4.0,?)",(now,))
        record_trade(self.store,'tcgcsv:1:3','market_Normal','BUY',1,4.0)
        (ROOT/'release_curves.json').write_text('{}',encoding='utf-8')
        target=Path(self.tmp.name)/'usb'
        make_portable_copy(self.store,target)
        self.assertTrue((target/'Card Market Terminal.py').exists() and (target/'READ ME - portable copy.txt').exists())
        con=sqlite3.connect(target/'CardMarketTerminalData'/'market.sqlite3')
        counts={t:con.execute(f'SELECT COUNT(*) FROM {t}').fetchone()[0] for t in ('cards','daily','portfolio','trades','prices')}
        con.close()
        self.assertEqual(counts,{'cards':1,'daily':1,'portfolio':1,'trades':1,'prices':0},'raw rows stay behind')
        self.assertTrue((target/'CardMarketTerminalData'/'release_curves.json').exists())
        with self.assertRaises(RuntimeError): make_portable_copy(self.store,target)
        self.assertGreater(portable_size_estimate(),0)
    def test_app_opens_while_the_background_update_is_writing(self):
        self.store.setting('advanced_tabs','0')
        other=sqlite3.connect(DB,timeout=0); other.execute('BEGIN IMMEDIATE')  # the daily update mid-write
        try:
            started=time.time(); s=Store(); s.setting('advanced_tabs','0')  # unchanged setting: no write needed
            self.assertLess(time.time()-started,5); s.con.close()
        finally: other.rollback(); other.close()
    def test_failed_portable_copy_can_be_retried(self):
        global PORTABLE_TABLES
        target=Path(self.tmp.name)/'usb2'; old=PORTABLE_TABLES
        PORTABLE_TABLES=('settings','no_such_table')  # fails partway, like a full drive
        try:
            with self.assertRaises(sqlite3.Error): make_portable_copy(self.store,target)
        finally: PORTABLE_TABLES=old
        self.assertFalse((target/'CardMarketTerminalData'/'market.sqlite3').exists(),'half-written copy removed')
        make_portable_copy(self.store,target)  # and a second try works
    def test_pricecharting_matching_and_summary(self):
        page=('<a href="https://www.pricecharting.com/game/pokemon-japanese-obsidian-flames/charizard-ex-223">x</a>'
              '<a href="https://www.pricecharting.com/game/pokemon-obsidian-flames/charizard-ex-215">x</a>'
              '<a href="https://www.pricecharting.com/game/pokemon-obsidian-flames/charizard-ex-223">x</a>')
        self.assertTrue(_pc_pick(page,'pokemon-','223/197').endswith('pokemon-obsidian-flames/charizard-ex-223'))
        self.assertTrue(_pc_pick(page,'pokemon-','999').endswith('charizard-ex-215'),'falls back to the first English match')
        self.assertIsNone(_pc_pick(page,'one-piece-','1'))
        res={'title':'Charizard ex #223','points':[[f'2025-{m:02d}',100.0+m] for m in range(1,13)]+[['2026-01',120.0]]}
        text=history_summary(res)
        self.assertIn('$120.00 now',text); self.assertIn('12 months +19%',text)
    def test_longrun_curves_pick_chase_by_release_month(self):
        rows=[]
        for k in range(20):
            # Cards 0-14 were the chase at release and fell 20% by month 3; cards 15-19 were cheap and later spiked 10x.
            pts=[['2025-01',100.0 if k<15 else 5.0],['2025-04',80.0 if k<15 else 50.0],['2026-01',90.0 if k<15 else 60.0]]
            rows.append((f'/game/pokemon-x/card-{k}','Pokémon','pokemon-x','2025-01-10',f'Card {k}',json.dumps(pts),utc()))
        self.store.executemany('INSERT INTO pc_series(url,game,slug,release,title,points,fetched_at) VALUES(?,?,?,?,?,?,?)',rows*1)
        for k in range(20,40):
            self.store.execute('INSERT INTO pc_series(url,game,slug,release,title,points,fetched_at) VALUES(?,?,?,?,?,?,?)',
                               (f'/game/pokemon-y/card-{k}','Pokémon','pokemon-y','2025-01-10',f'Card {k}',json.dumps([['2025-01',100.0],['2025-04',80.0],['2026-01',90.0]]),utc()))
        c=longrun_curves(self.store)['Pokémon']; c['sets']=c['sets']*3  # pretend enough sets for the action rules
        d={m:v for m,v,_a,_b,_n in c['curve']}
        self.assertAlmostEqual(d[3],-0.2,msg='later spikes of cards that were cheap at release are not in the sample')
        note=longrun_note({'game':'Pokémon','days_since_release':5},{'monthly':{'Pokémon':c}})
        self.assertIn('-20% by month 3',note)
        o=_monthly_opportunity({'game':'Pokémon','days_since_release':5,'latest_price':50.0,'name':'X','card_id':'x','price_type':'market_Normal'},
                               dict(DEFAULT_PRICING),{'Pokémon':c})
        self.assertEqual(o['action'],'PRE-SELL')
    def test_glossary_covers_names_and_aliases(self):
        self.assertEqual(glossary_lookup('Max buy NM · LP · MP')[0],'Max buy')
        self.assertEqual(glossary_lookup('win @ LOW')[0],'Win')
        self.assertEqual(glossary_lookup('Liq.')[0],'Liquidity')
        self.assertIsNone(glossary_lookup('no such column'))
        self.assertEqual(len({g[0] for g in GLOSSARY}),len(GLOSSARY),'no duplicate terms')
    def test_sell_advice_never_lowers_toward_a_higher_price(self):
        p=dict(DEFAULT_PRICING); checked=0
        for lo,hi in ((-20,10),(-10,25),(-5,5),(-30,0)):
            model={'horizon':14,'buckets':{'all':{'n':60,'bins':[[b,1] for b in range(lo,hi)]}}}
            for low in (20.0,30.0,38.0,40.0):
                row={'name':'C','card_name':'C','card_id':'tcgcsv:1:5','price_type':'market_Normal','printing':'Normal','game':'MTG','flags':[],
                     'latest_price':40.0,'low_price':low,'return_30d':0.0,'return_7d':0.0,'price_changes_30d':20,'variant':'Regular','observations':40}
                for cost in (None,10.0,45.0):
                    out=decide_sell(row,model,p,'NM',cost)
                    m=re.search(r'LIST AT \$([\d,.]+).*lower it toward \$([\d,.]+)',out['headline'])
                    if m: checked+=1; self.assertLess(float(m.group(2).rstrip('.')),float(m.group(1).rstrip('.')),out['headline'])
                    self.assertFalse(any('−$' in d and 'profit' in d for d in out['details']),'losses are called losses')
        self.assertGreater(checked,0)
    def test_every_setting_has_a_plain_validation_rule(self):
        rules={k for k,_l,_ok,_h in Terminal.PRICING_RULES}
        self.assertEqual(set(DEFAULT_PRICING)-rules,{'horizon'})
        for k,_l,ok,_h in Terminal.PRICING_RULES: self.assertTrue(ok(DEFAULT_PRICING[k]),k)
    def test_watchlist_alerts_reach_the_todo_list(self):
        pos=[{'id':'c#1','name':'Watched','qty':0,'signal':'HOLD','detail':'','market':5.0,'alerts':['≤ $6.00']},
             {'id':'c#2','name':'Held','qty':3,'signal':'SELL','detail':'sell it','market':40.0,'alerts':['≥ $30.00']}]
        acts=todays_actions([],pos,dict(DEFAULT_PRICING))
        self.assertEqual([(a['name'],a['action']) for a in acts],[('Watched','CHECK'),('Held','SELL')])
        self.assertIn('alert',acts[1]['why'])
    def test_friendly_errors(self):
        self.assertIn('internet connection',friendly_error('<urlopen error [Errno 11001] getaddrinfo failed>'))
        self.assertIn('slow down',friendly_error('HTTP Error 429: Too Many Requests'))
        self.assertIn('Details: HTTP Error 503',friendly_error('HTTP Error 503: Service Unavailable'))
        self.assertEqual(friendly_error('something odd'),'something odd')
    def test_csv_headings_are_readable(self):
        self.assertEqual(csv_heading('return_7d_pct'),'Return 7d %')
        self.assertEqual(csv_heading('latest_price_usd'),'Latest price $')
        self.assertEqual(csv_heading('ck_buylist'),'CK buylist')
        self.assertEqual(csv_heading('Card'),'Card')
    def test_trade_dates_accept_us_format(self):
        self.assertEqual(parse_trade_date('10/01/2026'),'2026-10-01'); self.assertEqual(parse_trade_date('2026-10-01'),'2026-10-01')
        self.assertEqual(parse_trade_date(''),date.today().isoformat()); self.assertIsNone(parse_trade_date('soon'))
        self.assertIsNone(parse_trade_date((date.today()+timedelta(days=3)).isoformat()))
    def test_every_overview_tile_name_is_explained(self):
        for key in Terminal.MONITOR_TILES:
            self.assertTrue(glossary_lookup(key),key); self.assertTrue(glossary_lookup(Terminal.MONITOR_TILE_NAMES.get(key,key)),key)
        self.assertEqual(set(Terminal.CYCLE_PHASES),{(-14,0),(0,14),(14,42),(42,90)})
    def test_buy_list_skips_cards_the_checker_calls_too_new(self):
        row={'card_id':1,'price_type':'market_Normal','name':'X','game':'MTG','flags':[],'max_buy':5.0,'latest_price':8.0,
             'price_changes_30d':20,'latest_date':'2026-10-28'}
        key=next(iter(BUY_LIST_SORTS))
        self.assertEqual(len(buy_list([dict(row,observations=40)],key)),1)
        self.assertEqual(buy_list([dict(row,observations=29)],key),[])
    def test_pricing_cache_round_trip(self):
        global _pricing_cache_path
        import tempfile
        old=_pricing_cache_path; tmp=tempfile.TemporaryDirectory()
        try:
            _pricing_cache_path=lambda: Path(tmp.name)/'pc.pickle'
            data={'signature':['x',1]}; model={'data_date':'2026-10-28','samples':5,'horizon':14,'built_at':'t'}
            rows=[{'card_id':'a'},{'card_id':'b'}]; exp={'cards':{},'sets':{},'total':0.0}
            key=pricing_cache_key(data,model,dict(DEFAULT_PRICING),exp,rows)
            self.assertIsNone(load_pricing_cache(key,2))
            save_pricing_cache(key,[{'max_buy':1.0},{'max_buy':None}])
            self.assertEqual(load_pricing_cache(key,2),[{'max_buy':1.0},{'max_buy':None}])
            other=pricing_cache_key(data,model,dict(DEFAULT_PRICING,fee_pct=10.0),exp,rows)
            self.assertNotEqual(key,other); self.assertIsNone(load_pricing_cache(other,2),'changed settings recompute')
            self.assertIsNone(pricing_cache_key({},model,dict(DEFAULT_PRICING),exp,rows))
        finally:
            _pricing_cache_path=old; tmp.cleanup()
    def test_cheap_holdings_are_bundled_and_trim_wording(self):
        pricing=dict(DEFAULT_PRICING)
        pos=[{'id':'c#1','name':'Bulk Card','qty':4,'signal':'TRIM','detail':'x','market':0.5,'alerts':[]}]
        acts=todays_actions([],pos,pricing)
        self.assertEqual(acts[0]['action'],'BUNDLE')
        _sig,text=position_signal(5.0,4.8,4,None,{'quick_sell':4.7,'exp_sale_net':3.0,'max_qty':0},pricing)
        self.assertNotIn('about 0',text); self.assertIn('rarely sells',text)
    def test_single_pass_views_match_separate_builds(self):
        import random
        rng=random.Random(11); latest=datetime.now(timezone.utc).date(); now=utc(); rows=[]; prices=[]
        for k in range(60):
            cid=f'tcgcsv:1:{k}'; price=8.0; rows.append((cid,'MTG',f'Card {k}','SET','1','Rare','Normal','{}',now,'card'))
            for d in range(100,-1,-1):
                price*=1.0+rng.uniform(-0.02,0.025)
                stamp=(latest-timedelta(days=d)).isoformat()
                prices.append((cid,'mtgjson_tcgplayer','market_Normal','USD',price*1.01,stamp+'T12:00:00+00:00',now))
                prices.append((cid,'tcgcsv_tcgplayer','market_Normal','USD',price,stamp+'T20:00:00+00:00',now))
        self.store.batch(rows,prices)
        data,models,_bt=build_market_views(self.store,0.04,latest.isoformat())
        alone=build_market_rankings(self.store,risk_free=0.04,scan_days=FORECAST_LOOKBACK_DAYS)
        self.assertEqual([(r['name'],r['sharpe_30d'],r['latest_price']) for r in data['fresh']],
                         [(r['name'],r['sharpe_30d'],r['latest_price']) for r in alone['fresh']])
        last=next(r for r in data['fresh'] if r['name']=='Card 59')
        self.assertEqual(last['latest_price'],round(prices[-1][4],2),'TCGCSV wins a day both sources cover (stored in cents)')
        separate=build_forecast_models(self.store,FORECAST_HORIZONS,latest.isoformat())
        for h in FORECAST_HORIZONS:
            self.assertEqual(models[h]['buckets'],separate[h]['buckets']); self.assertEqual(models[h]['backtest'],separate[h]['backtest'])
        self.assertIsNone(build_market_views(self.store,0.04,(latest-timedelta(days=1)).isoformat())[1],'a stale day hint drops the models')


def run_self_tests():
    suite=unittest.defaultTestLoader.loadTestsFromTestCase(OfflineSelfTests)
    result=unittest.TextTestRunner(verbosity=2).run(suite)
    return 0 if result.wasSuccessful() else 1

if __name__=='__main__':
    if '--self-test' in sys.argv:
        sys.exit(run_self_tests())
    if '--sync' in sys.argv:
        if sys.stdout is None or sys.stderr is None:
            # pythonw.exe (Task Scheduler) has no console; use the same logs as the macOS LaunchAgent.
            ROOT.mkdir(parents=True,exist_ok=True)
            sys.stdout=open(ROOT/'daily-sync.log','a',encoding='utf-8')
            sys.stderr=open(ROOT/'daily-sync-error.log','a',encoding='utf-8')
        sys.exit(run_headless_sync())
    if tk is None:
        print("Tkinter GUI could not start: No module named 'tkinter'",file=sys.stderr)
        print('Install a Python with Tk support (python.org; Homebrew: python-tk; Linux: python3-tk).',file=sys.stderr)
        sys.exit(1)
    try: AutomatedTerminal().mainloop()
    except sqlite3.OperationalError as e:
        if 'locked' not in str(e).lower(): raise
        try:
            root=tk.Tk(); root.withdraw()
            messagebox.showinfo(APP,"Today's prices are being saved by the daily background update right now, so the app can't open yet.\n\n"
                                    'Please wait a few minutes and open it again. (This only happens if you open the app while the update is running.)')
            root.destroy()
        except tk.TclError: print('The price database is busy with the daily update; try again in a few minutes.',file=sys.stderr)
        sys.exit(1)
    except tk.TclError as e:
        print('Tkinter GUI could not start:',e,file=sys.stderr)
        print('On macOS, use Python installed from python.org with Tk support.',file=sys.stderr)
        sys.exit(1)
