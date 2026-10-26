#!/usr/bin/env python3
"""Card Market Terminal v1.1 — single-file, stdlib-only desktop application.

Run the GUI:       python3 card_market_terminal_single.py
Run a headless sync: python3 card_market_terminal_single.py --sync
Run offline tests: python3 card_market_terminal_single.py --self-test

The TCGCSV collector checks its daily build marker and uses a custom User-Agent and
request pacing. It does not place trades or perform per-card rapid polling.
"""
import csv
import gzip
import io
import zipfile
import tempfile
import json
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
import urllib.error
import unittest
from unittest import mock
import plistlib
import subprocess
import shutil
from contextlib import contextmanager
from datetime import datetime, timezone, timedelta
from pathlib import Path
import tkinter as tk
from tkinter import ttk, filedialog, messagebox

APP = 'Card Market Terminal'
SUPPORTED_GAMES = ('MTG', 'Pokémon')
HISTORY_ARCHIVE_BASE = 'https://tcgcsv.com/archive/tcgplayer'
HISTORY_ARCHIVE_FIRST_DATE = datetime(2024, 2, 8).date()
ROOT = Path.home() / 'CardMarketTerminalData'
DB = ROOT / 'market.sqlite3'
USER_AGENT = 'CardMarketTerminal/1.1 (daily market-data research; local desktop application)'
BULK_INDEX = 'https://api.scryfall.com/bulk-data'
TCGCSV_BASE = 'https://tcgcsv.com/tcgplayer'
TCGCSV_LAST_UPDATED = 'https://tcgcsv.com/last-updated.txt'
TCGCSV_CATEGORIES = [(1, 'MTG'), (3, 'Pokémon')]
TCGCSV_DAILY_REQUEST_BUDGET = 8000  # keep a safety margin below TCGCSV's 10,000/day warning
_tcgcsv_budget_lock = threading.Lock()

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


def calculate_market_metrics(points, today=None):
    # Sharpe uses consecutive daily log returns from the latest 30-calendar-day
    # window and is suppressed unless there are 30 observations and 20 one-day returns.
    today=today or datetime.now(timezone.utc).date()
    if isinstance(today,datetime): today=today.date()
    by_day={}
    for stamp,raw_price in points:
        day=_source_day(stamp); price=numeric(raw_price)
        if day is None or price is None: continue
        prior=by_day.get(day)
        if prior is None or str(stamp)>prior[0]: by_day[day]=(str(stamp),price)
    series=sorted((day,item[1]) for day,item in by_day.items())
    if not series: return {
        'observations':0,'obs_30d':0,'latest_date':None,'latest_price':None,
        'age_days':None,'return_7d':None,'return_30d':None,'drawdown_30d':None,
        'sharpe_30d':None,'opportunity_score':None,'consecutive_returns':0
    }
    latest_day,latest_price=series[-1]
    age_days=max(0,(today-latest_day).days)

    def pct_change(days,tolerance):
        target=latest_day-timedelta(days=days)
        candidates=[]
        for day,price in series:
            distance=abs((day-target).days)
            if distance<=tolerance:
                candidates.append((distance,0 if day<=target else 1,day,price))
        if not candidates: return None
        base=min(candidates)[3]
        return (latest_price/base-1.0)*100 if base>0 else None

    return_7d=pct_change(7,2)
    return_30d=pct_change(30,3)
    window_start=latest_day-timedelta(days=29)
    recent=[(day,price) for day,price in series if window_start<=day<=latest_day]
    obs_30d=len(recent)
    high=max((price for day,price in series if latest_day-timedelta(days=29)<=day<=latest_day),default=None)
    drawdown=((latest_price/high)-1.0)*100 if high and high>0 else None
    daily_returns=[]
    for (day0,p0),(day1,p1) in zip(recent,recent[1:]):
        if (day1-day0).days==1 and p0>0 and p1>0:
            daily_returns.append(math.log(p1/p0))
    sharpe=None
    if obs_30d>=30 and len(daily_returns)>=20:
        volatility=statistics.stdev(daily_returns)
        if volatility>1e-9:
            sharpe=(statistics.mean(daily_returns)/volatility)*math.sqrt(365.0)
            if not math.isfinite(sharpe): sharpe=None

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
        'observations':len(series),'obs_30d':obs_30d,'latest_date':latest_day.isoformat(),
        'latest_price':latest_price,'age_days':age_days,'return_7d':return_7d,
        'return_30d':return_30d,'drawdown_30d':drawdown,'sharpe_30d':sharpe,
        'opportunity_score':score,'consecutive_returns':len(daily_returns)
    }


def _price_type_priority(price_type):
    subtype=str(price_type).partition('_')[2].strip().lower()
    preferred=['normal','nonfoil','non-foil','holofoil','foil','reverse holofoil','etched']
    try: return preferred.index(subtype)
    except ValueError: return len(preferred)+1


def build_market_rankings(store, today=None, progress=None):
    # Stream recent history so a large local database is not materialized in RAM.
    today=today or datetime.now(timezone.utc).date()
    if isinstance(today,datetime): today=today.date()
    cutoff=(today-timedelta(days=35)).isoformat()
    where="c.game IN ('MTG','Pokémon') AND c.item_type='card' AND p.source='tcgcsv_tcgplayer' AND p.price_type LIKE 'market_%' AND p.price>0 AND p.source_time>=?"
    total_rows=store.q('SELECT COUNT(*) FROM prices p JOIN cards c ON c.id=p.card_id WHERE '+where,(cutoff+'T00:00:00',))[0][0]
    if progress: progress(0,total_rows,'Scanning recent daily prices')
    chosen={}; current_id=None; current_type=None; current_game=None; current_name=None; points=[]; processed=0

    def flush_series():
        if current_id is None or not points: return
        metrics=calculate_market_metrics(points,today)
        if not metrics.get('observations'): return
        candidate={**metrics,'card_id':current_id,'game':current_game,'name':current_name,
                   'price_type':current_type,'series_count':metrics['observations']}
        old=chosen.get(current_id)
        if (old is None or candidate['series_count']>old['series_count'] or
            (candidate['series_count']==old['series_count'] and
             _price_type_priority(candidate['price_type'])<_price_type_priority(old['price_type']))):
            chosen[current_id]=candidate

    sql='''SELECT c.id,c.game,c.name,p.price_type,p.price,p.source_time
           FROM prices p JOIN cards c ON c.id=p.card_id
           WHERE c.game IN ('MTG','Pokémon') AND c.item_type='card' AND p.source='tcgcsv_tcgplayer'
             AND p.price_type LIKE 'market_%' AND p.price>0 AND p.source_time>=?
           ORDER BY c.id,p.price_type,p.source_time'''
    for cid,game,name,price_type,price,stamp in store.iter_q(sql,(cutoff+'T00:00:00',)):
        processed += 1
        if progress and (processed % 500 == 0 or processed == total_rows):
            progress(processed,total_rows,'Calculating Sharpe & opportunities')
        key=(cid,price_type)
        if current_id is None:
            current_id,current_type,current_game,current_name=cid,price_type,game,name
        elif key!=(current_id,current_type):
            flush_series(); points=[]
            current_id,current_type,current_game,current_name=cid,price_type,game,name
        points.append((stamp,price))
    flush_series()
    if progress and (total_rows == 0 or processed < total_rows):
        progress(total_rows,total_rows,'Ranking calculations complete')
    all_rows=list(chosen.values())
    fresh=[r for r in all_rows if r['age_days'] is not None and r['age_days']<=3]
    sharpe_rows=sorted((r for r in fresh if r['sharpe_30d'] is not None),
                       key=lambda r:(-r['sharpe_30d'],-(r['return_30d'] or -1e9),r['name']))
    opportunity_rows=sorted((r for r in fresh if r['opportunity_score'] is not None),
                            key=lambda r:(-r['opportunity_score'],-(r['return_7d'] or -1e9),r['name']))
    diagnostics = market_data_diagnostics(store, today)
    return {'all':all_rows,'fresh':fresh,'sharpe':sharpe_rows,'opportunities':opportunity_rows,
            'diagnostics':diagnostics}


def market_data_diagnostics(store, today=None):
    """Summarize local source coverage so an empty ranking is explainable."""
    today=today or datetime.now(timezone.utc).date()
    if isinstance(today,datetime): today=today.date()
    cutoff=(today-timedelta(days=35)).isoformat()+'T00:00:00'
    total_cards=store.q("SELECT COUNT(*) FROM cards WHERE game IN ('MTG','Pokémon')")[0][0]
    item_types={str(kind or 'unknown'):count for kind,count in store.q(
        "SELECT item_type,COUNT(*) FROM cards WHERE game IN ('MTG','Pokémon') GROUP BY item_type")}
    total_prices=store.q("SELECT COUNT(*) FROM prices p JOIN cards c ON c.id=p.card_id WHERE c.game IN ('MTG','Pokémon')")[0][0]
    tcgcsv_prices=store.q("SELECT COUNT(*) FROM prices p JOIN cards c ON c.id=p.card_id WHERE c.game IN ('MTG','Pokémon') AND p.source='tcgcsv_tcgplayer'")[0][0]
    market_prices=store.q("SELECT COUNT(*) FROM prices p JOIN cards c ON c.id=p.card_id WHERE c.game IN ('MTG','Pokémon') AND p.source='tcgcsv_tcgplayer' AND p.price_type LIKE 'market_%' AND p.price>0")[0][0]
    recent_market_prices=store.q("SELECT COUNT(*) FROM prices p JOIN cards c ON c.id=p.card_id WHERE c.game IN ('MTG','Pokémon') AND p.source='tcgcsv_tcgplayer' AND p.price_type LIKE 'market_%' AND p.price>0 AND p.source_time>=?",(cutoff,))[0][0]
    recent_singles=store.q("""SELECT COUNT(*) FROM prices p JOIN cards c ON c.id=p.card_id
        WHERE c.game IN ('MTG','Pokémon') AND c.item_type='card' AND p.source='tcgcsv_tcgplayer' AND p.price_type LIKE 'market_%'
          AND p.price>0 AND p.source_time>=?""",(cutoff,))[0][0]
    latest=store.q("SELECT MAX(p.source_time) FROM prices p JOIN cards c ON c.id=p.card_id WHERE c.game IN ('MTG','Pokémon') AND p.source='tcgcsv_tcgplayer' AND p.price_type LIKE 'market_%' AND p.price>0")
    return {'total_cards':total_cards,'item_types':item_types,'total_prices':total_prices,
            'tcgcsv_prices':tcgcsv_prices,'market_prices':market_prices,
            'recent_market_prices':recent_market_prices,'recent_singles_price_rows':recent_singles,
            'latest_market_source_time':latest[0][0] if latest else None}

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

def request_json(url):
    req = urllib.request.Request(url, headers={'User-Agent': USER_AGENT, 'Accept': 'application/json'})
    with urllib.request.urlopen(req, timeout=40) as f: return json.load(f)

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

def choose_scryfall_bulk():
    """Choose a whole-catalog export, supporting current JSONL and legacy JSON metadata."""
    payload = request_json(BULK_INDEX)
    items = payload.get('data', []) if isinstance(payload, dict) else []
    entry = next((item for item in items if isinstance(item, dict) and
                  item.get('type') == 'default_cards'), None)
    if entry is None:
        raise RuntimeError('Scryfall bulk index does not contain default_cards')
    url = entry.get('jsonl_download_uri') or entry.get('download_uri')
    if not url:
        raise RuntimeError('Scryfall default_cards has no supported download URL; fields: ' +
                           ', '.join(sorted(entry.keys())))
    from urllib.parse import urlsplit
    host = (urlsplit(url).hostname or '').lower()
    if urlsplit(url).scheme != 'https' or host != 'data.scryfall.io':
        raise RuntimeError('Unexpected Scryfall bulk download host: ' + host)
    suffix = '.jsonl.gz' if url.lower().split('?')[0].endswith('.jsonl.gz') else \
             '.jsonl' if url.lower().split('?')[0].endswith('.jsonl') else \
             '.json.gz' if url.lower().split('?')[0].endswith('.json.gz') else '.json'
    return entry, url, suffix

class Store:
    def __init__(self):
        ROOT.mkdir(parents=True, exist_ok=True)
        self.con = sqlite3.connect(DB, check_same_thread=False)
        self.lock = threading.RLock()
        with self.lock:
            self.con.executescript('''
            PRAGMA journal_mode=WAL;
            PRAGMA busy_timeout=10000;
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
            CREATE INDEX IF NOT EXISTS idx_prices_card_source_type_time ON prices(card_id,source,price_type,source_time);
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
            ''')
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
            self.con.commit()
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
    def get_setting(self,k,default=''):
        r=self.q('SELECT value FROM settings WHERE key=?',(k,)); return r[0][0] if r else default
    def setting(self,k,v): self.execute('INSERT INTO settings VALUES(?,?) ON CONFLICT(key) DO UPDATE SET value=excluded.value',(k,str(v)))
    def batch(self,rows, prices=()):
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
                self.con.commit()
            except Exception:
                self.con.rollback()
                raise
    def start_job(self,task): return self.execute('INSERT INTO jobs(started_at,task,status,count,message) VALUES(?,?,?,?,?)',(utc(),task,'running',0,''))
    def end_job(self,id,status,count,msg): self.execute('UPDATE jobs SET ended_at=?,status=?,count=?,message=? WHERE id=?',(utc(),status,count,str(msg)[:800],id))
    def close(self):
        with self.lock: self.con.close()

def stream_array(path):
    """Stream objects from a JSON top-level array without loading the entire file."""
    decoder=json.JSONDecoder(); buf=''; ix=0; first=True; ended=False
    opener = gzip.open if str(path).endswith('.gz') else open
    with opener(path,'rt',encoding='utf-8') as f:
        while True:
            if ix >= len(buf):
                chunk=f.read(262144)
                if not chunk: break
                buf=chunk; ix=0
            c=buf[ix]
            if c.isspace() or c==',': ix+=1; continue
            if first:
                if c!='[': raise ValueError('Expected a top-level JSON array')
                first=False; ix+=1; continue
            if c==']': ended=True; break
            while True:
                try: obj, end=decoder.raw_decode(buf,ix); ix=end; yield obj; break
                except json.JSONDecodeError:
                    extra=f.read(262144)
                    if not extra: raise ValueError('Incomplete JSON object')
                    buf=buf[ix:]+extra; ix=0
            if ix > 1000000: buf=buf[ix:]; ix=0
    if not ended: raise ValueError('JSON array did not close')

def stream_scryfall(path):
    opener = gzip.open if str(path).endswith('.gz') else open
    with opener(path, 'rt', encoding='utf-8') as f:
        first = f.read(4096).lstrip()
    if first.startswith('['):
        yield from stream_array(path)
    else:
        with opener(path, 'rt', encoding='utf-8') as f:
            for lineno, line in enumerate(f, 1):
                if line.strip():
                    try:
                        yield json.loads(line)
                    except json.JSONDecodeError as e:
                        raise ValueError(f'Invalid JSONL record on line {lineno}: {e}') from e

def ingest_scryfall(path, store, report):
    # Scryfall bulk default_cards: one object per gameplay card; all_cards for printings.
    batch=[]; prices=[]; count=0; now=utc()
    for c in stream_scryfall(path):
        if not isinstance(c,dict) or not c.get('id'): continue
        cid='mtg:'+str(c['id']); name=c.get('name','Unknown')
        finish=','.join(c.get('finishes') or [])
        details=json.dumps({'scryfall_id':c['id'],'oracle_id':c.get('oracle_id'),
         'released_at':c.get('released_at'),'set_name':c.get('set_name'),
         'scryfall_uri':c.get('scryfall_uri'),'image':(c.get('image_uris') or {}).get('small')},ensure_ascii=False)
        batch.append((cid,'MTG',name,c.get('set',''),str(c.get('collector_number','')),c.get('rarity',''),finish,details,now,'card'))
        # Price values in Scryfall's bulk file are reference prices, not sale executions.
        p=c.get('prices') or {}; t=c.get('updated_at') or now
        for key in ('usd','usd_foil','usd_etched'):
            v=numeric(p.get(key))
            if v is not None: prices.append((cid,'scryfall_bulk',f'reference_{key}','USD',v,t,now))
        count+=1
        if len(batch)>=750:
            store.batch(batch,prices); batch=[]; prices=[]
            if count%7500==0:
                report(f'MTG: {count:,} printings imported')
                emit_progress(report, count, 0, f'Scryfall import: {count:,} cards processed')
    if batch: store.batch(batch,prices)
    emit_progress(report, count, 1, f'Scryfall import complete: {count:,} cards')
    return count

def ingest_pokemon(path,store,report):
    # Accept Pokémon TCG GitHub JSON set files (list) or {'data':[...]} API exports.
    with open(path,encoding='utf-8') as f: obj=json.load(f)
    entries=obj.get('data',[]) if isinstance(obj,dict) else obj
    if not isinstance(entries,list): raise ValueError('Expected JSON array or object with data array')
    batch=[]; prices=[]; now=utc()
    emit_progress(report, 0, len(entries), 'Importing Pokémon JSON: '+Path(path).name)
    for entry_index,c in enumerate(entries,1):
        if not isinstance(c,dict) or not c.get('id'):
            if entry_index % 100 == 0 or entry_index == len(entries):
                emit_progress(report, entry_index, len(entries), 'Importing Pokémon JSON: '+Path(path).name)
            continue
        cid='pokemon:'+str(c['id']); s=c.get('set') or {}; s=s if isinstance(s,dict) else {}
        details=json.dumps({'supertype':c.get('supertype'),'subtypes':c.get('subtypes'),
          'set_name':s.get('name'),'images':c.get('images'),'rarity':c.get('rarity')},ensure_ascii=False)
        batch.append((cid,'Pokémon',c.get('name','Unknown'),s.get('id',''),str(c.get('number','')),c.get('rarity',''),'unknown',details,now,'card'))
        if entry_index % 100 == 0 or entry_index == len(entries):
            emit_progress(report, entry_index, len(entries), 'Importing Pokémon JSON: '+Path(path).name)
        # These third-party fields can be stale. Treat as source reference, never as sale data.
        for source,key in [('tcgplayer', 'tcgplayer'),('cardmarket','cardmarket')]:
            d=c.get(key) or {}; update=d.get('updatedAt') or now
            if source=='tcgplayer':
                for category, vals in (d.get('prices') or {}).items():
                    for typ in ('market','mid','low'):
                        val=numeric((vals or {}).get(typ))
                        if val: prices.append((cid,'pokemon_dataset_tcgplayer',f'reference_{category}_{typ}','USD',val,update,now))
            # Exclude EUR Cardmarket quotes unless currency conversion and provenance are provided.
    store.batch(batch,prices)
    emit_progress(report, len(entries), max(1,len(entries)), 'Pokémon import complete: '+Path(path).name)
    report(f'Pokémon: imported {len(batch):,} cards')
    return len(batch)


def tcgcsv_text(url):
    """Fetch a small TCGCSV text resource with pacing and bounded transient retries."""
    req=urllib.request.Request(url, headers={'User-Agent':USER_AGENT,'Accept':'text/plain,*/*'})
    for attempt in range(4):
        time.sleep(0.11)
        try:
            reserve_tcgcsv_request()
            with urllib.request.urlopen(req, timeout=30) as r:
                return r.read().decode('utf-8-sig').strip()
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
    req=urllib.request.Request(url, headers={'User-Agent':USER_AGENT,'Accept':'application/json'})
    for attempt in range(4):
        time.sleep(0.11)  # documented minimum pacing between requests
        try:
            reserve_tcgcsv_request()
            with urllib.request.urlopen(req, timeout=45) as r:
                payload=json.load(r)
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

def ingest_tcgcsv(store, report, category_id, game, group, dataset_time):
    """Sync one TCGCSV group: product catalog plus daily market-price observations."""
    group_id=group.get('groupId')
    if group_id is None: return 0
    base=f'{TCGCSV_BASE}/{category_id}/{group_id}'
    products=tcgcsv_results(tcgcsv_json(base+'/products',allow_not_found=True),base+'/products')
    if not products:
        report(f'{game}: group {group_id} has no products; skipped')
        return 0
    price_rows=tcgcsv_results(tcgcsv_json(base+'/prices',allow_not_found=True),base+'/prices')
    by_product={}
    for pr in price_rows:
        if isinstance(pr,dict) and pr.get('productId') is not None:
            by_product.setdefault(str(pr['productId']),[]).append(pr)
    now=utc(); cards=[]; prices=[]
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
            subtype=str(item.get('subTypeName') or 'Unspecified')
            for field,label in [('marketPrice','market'),('lowPrice','low'),('midPrice','mid'),
                                ('highPrice','high_raw'),('directLowPrice','direct_low')]:
                val=numeric(item.get(field))
                if val is not None:
                    prices.append((cid,'tcgcsv_tcgplayer',f'{label}_{subtype}','USD',val,dataset_time,now))
    store.batch(cards,prices)
    return len(cards)

def _sync_tcgcsv_daily_locked(store, report):
    """Check the daily TCGCSV build marker, then sync Magic and Pokémon only if changed."""
    report('Checking TCGCSV last-updated marker')
    emit_progress(report,0,0,'Checking TCGCSV dataset marker')
    raw=tcgcsv_text(TCGCSV_LAST_UPDATED)
    if not raw: raise RuntimeError('TCGCSV last-updated.txt was empty')
    previous=store.get_setting('tcgcsv_dataset_marker','')
    if previous == raw:
        store.setting('tcgcsv_check_epoch',time.time())
        store.setting('tcgcsv_last_check',utc())
        report('TCGCSV dataset is unchanged; no duplicate download or price snapshot created')
        emit_progress(report,1,1,'Dataset unchanged — no download needed')
        return 0
    source_time=tcgcsv_timestamp(raw)
    total=0
    for category_id,game in TCGCSV_CATEGORIES:
        report(f'Loading {game} group catalog (category {category_id})')
        emit_progress(report,0,0,f'Loading {game} group catalog')
        groups=tcgcsv_results(tcgcsv_json(f'{TCGCSV_BASE}/{category_id}/groups'),f'{game} groups')
        report(f'{game}: {len(groups):,} groups found; syncing products and daily prices')
        emit_progress(report,0,len(groups),f'Syncing {game} groups')
        game_total=0
        for idx,group in enumerate(groups,1):
            game_total+=ingest_tcgcsv(store,report,category_id,game,group,source_time)
            emit_progress(report,idx,len(groups),f'{game}: syncing groups')
            if idx%20==0 or idx==len(groups):
                report(f'{game}: groups {idx:,}/{len(groups):,}; products synced {game_total:,}')
        total+=game_total
    # Only mark the source marker successful after BOTH categories complete.
    store.setting('tcgcsv_dataset_marker',raw)
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
    """Import one extracted TCGCSV daily archive for the supported MTG/Pokémon categories."""
    day = archive_day.isoformat() if hasattr(archive_day, 'isoformat') else str(archive_day)
    source_time = day + 'T20:00:00+00:00'
    valid_ids = {row[0] for row in store.q("SELECT id FROM cards WHERE id LIKE 'tcgcsv:1:%' OR id LIKE 'tcgcsv:3:%'")}
    if not valid_ids:
        raise RuntimeError('No TCGCSV catalog records are stored yet. Run a successful MTG + Pokémon daily sync before backfilling history.')
    collected_at = utc(); pending = []; processed = 0; files_seen = 0
    root = Path(extract_root)
    for path in root.rglob('prices'):
        parts = path.relative_to(root).parts
        try: idx = parts.index(day)
        except ValueError: continue
        if len(parts) <= idx + 3: continue
        category = parts[idx + 1]
        if category not in ('1', '3'): continue
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
            subtype = str(item.get('subTypeName') or 'Unspecified')
            for field, label in [('marketPrice','market'),('lowPrice','low'),('midPrice','mid'),
                                 ('highPrice','high_raw'),('directLowPrice','direct_low')]:
                val = numeric(item.get(field))
                if val is not None:
                    pending.append((cid,'tcgcsv_tcgplayer',f'{label}_{subtype}','USD',val,source_time,collected_at))
            if len(pending) >= 5000:
                store.batch([], pending); processed += len(pending); pending.clear()
    if pending:
        store.batch([], pending); processed += len(pending)
    if files_seen == 0:
        raise RuntimeError(f'No MTG/Pokémon price files were found in the extracted {day} archive; refusing to mark this date complete.')
    report(f'{day}: inspected {files_seen:,} MTG/Pokémon group price files; processed {processed:,} matching price observations')
    return processed


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
    sevenzip = shutil.which('7zz') or shutil.which('7z') or shutil.which('7za')
    if not sevenzip:
        raise RuntimeError('Historical archives require the 7-Zip command-line tool. On macOS with Homebrew, install it with: brew install sevenzip. Then reopen the app and retry.')
    days=[]; current=start
    while current <= end:
        days.append(current); current += timedelta(days=1)
    completed_raw = store.get_setting('tcgcsv_archive_backfill_dates','[]')
    try: completed=set(json.loads(completed_raw))
    except (ValueError,TypeError): completed=set()
    total_inserted=0; missing=0; skipped=0; processed=0
    if not store.q("SELECT 1 FROM cards WHERE id LIKE 'tcgcsv:1:%' OR id LIKE 'tcgcsv:3:%' LIMIT 1") or not store.get_setting('tcgcsv_dataset_marker',''):
        raise RuntimeError('Complete a successful Collectors → Sync MTG + Pokémon now first. The historical backfill needs the finished catalog to match archive product IDs to card names.')
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

class Terminal(tk.Tk):
    def __init__(self):
        super().__init__(); self.store=Store(); self.events=queue.Queue(); self.busy=False
        self.title('Card Market Terminal  |  MTG + Pokémon'); self.geometry('1230x790'); self.minsize(900,580)
        self.colors={'bg':'#0d1523','panel':'#182337','light':'#dbe7fa','muted':'#95aac7','accent':'#5ca9ff'}
        self.configure(bg=self.colors['bg']); self.theme(); self.make_ui()
        self.refresh(); self.after(200,self.drain); self.protocol('WM_DELETE_WINDOW',self.close)
    def theme(self):
        st=ttk.Style(self); st.theme_use('clam')
        st.configure('.',font=('Helvetica',11),background=self.colors['bg'],foreground=self.colors['light'])
        st.configure('TFrame',background=self.colors['bg']); st.configure('Panel.TFrame',background=self.colors['panel'])
        st.configure('TLabel',background=self.colors['bg'],foreground=self.colors['light']); st.configure('Small.TLabel',font=('Helvetica',10),foreground=self.colors['muted'])
        st.configure('TButton',padding=(13,8),background='#273c59',foreground='#f4f7fd')
        st.map('TButton',background=[('active','#365a86')]); st.configure('TNotebook',borderwidth=0)
        st.configure('TNotebook.Tab',padding=(14,11),background='#192a40',foreground='#dbe7fa')
        st.map('TNotebook.Tab',background=[('selected','#345d88')]); st.configure('Treeview',rowheight=29,background='#17253a',fieldbackground='#17253a',foreground='#e3eeff')
        st.configure('Treeview.Heading',background='#253b57',foreground='#e7f0ff',font=('Helvetica',10,'bold'))
        st.map('Treeview',background=[('selected','#3b648f')])
        st.configure('TEntry',fieldbackground='#eff5ff',foreground='#13223a')
    def make_ui(self):
        top=ttk.Frame(self,padding=(18,14)); top.pack(fill='x')
        ttk.Label(top,text='CARD MARKET TERMINAL',font=('Helvetica',21,'bold')).pack(side='left')
        ttk.Label(top,text='MTG + POKÉMON  •  LOCAL FIRST  •  NO PAID APIS',style='Small.TLabel').pack(side='right')
        self.nb=ttk.Notebook(self); self.nb.pack(fill='both',expand=True,padx=16,pady=(0,4))
        self.tabs={}
        for name in ['Overview','Card Explorer','Market History','Watchlist','Opportunity Lab','Sharpe & Opportunities','Collectors','Paper Trades','Settings']:
            fr=ttk.Frame(self.nb,padding=13); self.nb.add(fr,text=name); self.tabs[name]=fr
        self.overview(); self.explorer(); self.history_tab(); self.watch_tab(); self.opportunity_tab(); self.sharpe_opportunities_tab(); self.collector_tab(); self.paper_tab(); self.settings_tab()
        activity=ttk.Frame(self,padding=(18,0,18,2)); activity.pack(fill='x')
        self.activity_text=tk.StringVar(value='Activity: idle')
        ttk.Label(activity,textvariable=self.activity_text,style='Small.TLabel',width=38).pack(side='left',padx=(0,8))
        self.activity_progress=ttk.Progressbar(activity,mode='indeterminate',length=340,maximum=100)
        self.activity_progress.pack(side='left',fill='x',expand=True)
        self.status=tk.StringVar(value='Ready — no automatic external polling')
        ttk.Label(self,textvariable=self.status,style='Small.TLabel').pack(anchor='w',padx=20,pady=(0,8))
    def section(self,parent,title,desc=''):
        ttk.Label(parent,text=title,font=('Helvetica',16,'bold')).pack(anchor='w',pady=(4,4))
        if desc: ttk.Label(parent,text=desc,style='Small.TLabel',wraplength=1000).pack(anchor='w',pady=(0,12))
    def gridview(self,parent,cols,height=13):
        frame=ttk.Frame(parent); frame.pack(fill='both',expand=True,pady=7)
        tree=ttk.Treeview(frame,columns=cols,show='headings',height=height)
        for col in cols:
            tree.heading(col,text=col); tree.column(col,width=150 if len(cols)>4 else 210,anchor='w')
        vs=ttk.Scrollbar(frame,orient='vertical',command=tree.yview); tree.configure(yscrollcommand=vs.set)
        tree.pack(side='left',fill='both',expand=True); vs.pack(side='left',fill='y'); return tree
    def overview(self):
        p=self.tabs['Overview']; self.section(p,'Market overview','Local, source-attributed market observations. No fabricated live prices or assumed trades.')
        self.kpis=ttk.Label(p,text='',font=('Helvetica',14)); self.kpis.pack(anchor='w',pady=8)
        ttk.Label(p,text='Recent collection runs',font=('Helvetica',13,'bold')).pack(anchor='w',pady=(20,0))
        self.jobtree=self.gridview(p,('Time','Collector','Status','Records','Details'),9)
        ttk.Button(p,text='Refresh dashboard',command=self.refresh).pack(anchor='w')
    def explorer(self):
        p=self.tabs['Card Explorer']; self.section(p,'Find cards and products','Search the local catalog by name or product ID. Individual cards are classified separately from sealed products and other items.')
        bar=ttk.Frame(p); bar.pack(fill='x')
        self.search=tk.StringVar(); ttk.Entry(bar,textvariable=self.search,width=44).pack(side='left',padx=(0,9))
        self.game=tk.StringVar(value='All'); ttk.Combobox(bar,textvariable=self.game,values=['All','MTG','Pokémon'],state='readonly',width=12).pack(side='left',padx=(0,8))
        ttk.Button(bar,text='Search',command=self.find).pack(side='left')
        ttk.Button(bar,text='Add selected to watchlist',command=self.watch_selected).pack(side='left',padx=10)
        self.cards=self.gridview(p,('ID','Game','Item type','Name','Set','Number','Rarity'),17)
        self.cards.bind('<Double-1>',lambda e:self.card_detail())
        ttk.Button(p,text='View selected card history',command=self.card_detail).pack(anchor='w')
    def history_tab(self):
        p=self.tabs['Market History']
        self.section(p,'Market history','Daily TCGplayer cached estimates, not verified individual sales. Run a historical backfill from Collectors to populate earlier dates.')
        bar=ttk.Frame(p); bar.pack(fill='x',pady=(0,5))
        self.history_search=tk.StringVar(); self.history_game=tk.StringVar(value='All')
        ttk.Entry(bar,textvariable=self.history_search,width=38).pack(side='left',padx=(0,8))
        ttk.Combobox(bar,textvariable=self.history_game,values=['All','MTG','Pokémon'],state='readonly',width=10).pack(side='left',padx=(0,8))
        ttk.Button(bar,text='Find cards',command=self.search_history_cards).pack(side='left',padx=(0,8))
        ttk.Button(bar,text='Load selected history',command=self.load_selected_history).pack(side='left')
        self.history_results=self.gridview(p,('ID','Game','Card','Set','Type'),5)
        self.history_results.column('ID',width=0,minwidth=0,stretch=False)
        self.history_results.bind('<Double-1>',lambda _e:self.load_selected_history())
        self.history_id=tk.StringVar(value='')
        self.history_status=tk.StringVar(value='Search for a card above, or open history from Card Explorer / Sharpe & Opportunities.')
        ttk.Label(p,textvariable=self.history_status,style='Small.TLabel',wraplength=1000).pack(anchor='w',pady=(2,5))
        self.history_chart=tk.Canvas(p,height=150,bg='#0b1726',highlightthickness=1,highlightbackground='#253b57')
        self.history_chart.pack(fill='x',expand=False,pady=(0,5))
        self.history_chart_points=[]
        self.history_chart.bind('<Configure>',lambda _e:self._draw_history_chart(self.history_chart_points))
        self.pricetree=self.gridview(p,('Source time','Price','Currency','Source','Kind','Collected at'),8)
        ttk.Button(p,text='Export visible card history (CSV)',command=self.export_history).pack(anchor='w')
        self._draw_history_chart([])

    def search_history_cards(self):
        needle=self.history_search.get().strip(); game=self.history_game.get(); self.clear(self.history_results)
        sql="SELECT id,game,name,set_code,item_type FROM cards WHERE game IN ('MTG','Pokémon')"; args=[]
        if needle:
            sql+=' AND (name LIKE ? OR id LIKE ?)'; args.extend(['%'+needle+'%']*2)
        if game!='All': sql+=' AND game=?'; args.append(game)
        sql+=' ORDER BY name LIMIT 200'
        rows=self.store.q(sql,tuple(args))
        for row in rows: self.history_results.insert('','end',values=row)
        self.history_status.set(f'Found {len(rows):,} matching MTG/Pokémon records. Double-click a card to load its saved price observations.')

    def load_selected_history(self):
        selected=self.history_results.selection()
        if not selected:
            messagebox.showinfo(APP,'Search for a card and select a result first.'); return
        values=self.history_results.item(selected[0],'values')
        if values:
            self.history_id.set(values[0]); self.load_history()

    def _draw_history_chart(self, points):
        self.history_chart_points=list(points)
        canvas=self.history_chart; canvas.delete('all')
        width=max(300,canvas.winfo_width()); height=max(100,canvas.winfo_height())
        left,right,top,bottom=58,width-18,14,height-30
        canvas.create_text(12,12,anchor='nw',fill='#95aac7',text='Market price trend (daily market metric)')
        if not points:
            canvas.create_text(width/2,height/2,fill='#95aac7',text='No saved market history for this card yet')
            return
        vals=[float(x[1]) for x in points if x[1] is not None and float(x[1])>0]
        if len(vals)<1: return
        lo=min(vals); hi=max(vals)
        if hi<=lo: hi=lo*1.05 if lo else 1.0
        for i in range(5):
            y=top+(bottom-top)*i/4
            value=hi-(hi-lo)*i/4
            canvas.create_line(left,y,right,y,fill='#253b57')
            canvas.create_text(left-7,y,anchor='e',fill='#95aac7',text=f'${value:,.2f}')
        xy=[]
        n=len(points)
        for i,(day,price) in enumerate(points):
            if price is None or float(price)<=0: continue
            x=left+(right-left)*(i/max(1,n-1))
            y=top+(bottom-top)*(hi-float(price))/(hi-lo)
            xy.extend((x,y))
        if len(xy)>=4: canvas.create_line(*xy,fill='#5ca9ff',width=2,smooth=False)
        canvas.create_text(left,bottom+12,anchor='w',fill='#95aac7',text=str(points[0][0])[:10])
        canvas.create_text(right,bottom+12,anchor='e',fill='#95aac7',text=str(points[-1][0])[:10])
    def watch_tab(self):
        p=self.tabs['Watchlist']; self.section(p,'Watchlist','Tracking does not trigger external requests; it marks cards for later permitted source integrations.')
        self.watchtree=self.gridview(p,('Card ID','Game','Card','Added'),16)
        bar=ttk.Frame(p); bar.pack(fill='x')
        ttk.Button(bar,text='Remove selected',command=self.unwatch).pack(side='left'); ttk.Button(bar,text='Refresh',command=self.load_watch).pack(side='left',padx=8)
    def opportunity_tab(self):
        p=self.tabs['Opportunity Lab']; self.section(p,'Opportunity research and net-profit estimator','Manual research tool. Not an automated buy signal, Sharpe estimate, or prediction.')
        box=ttk.Frame(p); box.pack(anchor='w',pady=12)
        self.inputs={}
        for row,(key,value) in enumerate([('Buy price',20),('Potential resale',35),('Selling fee %',13.25),('Other costs',4),('Quantity',1)]):
            ttk.Label(box,text=key,width=20).grid(row=row,column=0,sticky='w',pady=5)
            var=tk.StringVar(value=str(value)); ttk.Entry(box,textvariable=var,width=15).grid(row=row,column=1,sticky='w'); self.inputs[key]=var
        ttk.Button(box,text='Calculate',command=self.calculate).grid(row=6,column=0,sticky='w',pady=14)
        self.profit=tk.StringVar(value='Fill values and calculate.'); ttk.Label(p,textvariable=self.profit,font=('Helvetica',13,'bold')).pack(anchor='w',pady=10)
        ttk.Label(p,text='Reminder: reference prices do not prove a resale is executable. Model taxes, grading, fees, delivery, inventory and holding risk before investing.',style='Small.TLabel',wraplength=900).pack(anchor='w')
    def sharpe_opportunities_tab(self):
        p=self.tabs['Sharpe & Opportunities']
        self.section(p,'Best risk-adjusted history and potential opportunities',
            'Rankings use TCGCSV cached daily market prices for individual cards only. Sharpe requires 30 daily observations and at least 20 consecutive daily returns; opportunity scores are research priorities, not buy signals.')
        bar=ttk.Frame(p); bar.pack(fill='x',pady=(0,5))
        self.rank_refresh_button=ttk.Button(bar,text='Refresh rankings',command=self.refresh_rankings)
        self.rank_refresh_button.pack(side='left',padx=(0,8))
        ttk.Button(bar,text='Add selected card to watchlist',command=self.add_ranked_to_watchlist).pack(side='left',padx=(0,8))
        ttk.Button(bar,text='Export rankings CSV',command=self.export_rankings).pack(side='left')
        self.ranking_note=tk.StringVar(value='Waiting for market data…')
        ttk.Label(p,textvariable=self.ranking_note,style='Small.TLabel',wraplength=1050).pack(anchor='w',pady=(2,4))
        rank_progress_row=ttk.Frame(p); rank_progress_row.pack(fill='x',pady=(0,6))
        self.rank_progress_text=tk.StringVar(value='Rankings have not been calculated yet')
        ttk.Label(rank_progress_row,textvariable=self.rank_progress_text,style='Small.TLabel',width=42).pack(side='left',padx=(0,8))
        self.rank_progress=ttk.Progressbar(rank_progress_row,mode='indeterminate',length=300,maximum=100)
        self.rank_progress.pack(side='left',fill='x',expand=True)
        self.rankings_busy=False
        panels=ttk.Frame(p); panels.pack(fill='both',expand=True)
        left=ttk.LabelFrame(panels,text=' BEST 30-DAY SHARPE RATIOS ',padding=7)
        right=ttk.LabelFrame(panels,text=' POTENTIAL OPPORTUNITIES / HISTORY BUILDING ',padding=7)
        self.sharpe_empty_text=tk.StringVar(value='No valid Sharpe ratios yet. Requires 30 daily observations and at least 20 consecutive daily returns.')
        self.sharpe_empty_label=ttk.Label(left,textvariable=self.sharpe_empty_text,style='Small.TLabel',wraplength=430)
        self.sharpe_empty_label.pack(anchor='w',fill='x',pady=(0,5))
        left.pack(side='left',fill='both',expand=True,padx=(0,6))
        right.pack(side='left',fill='both',expand=True,padx=(6,0))
        self.sharpe_tree=self.gridview(left,('ID','Card','Game','Price','Sharpe','30d %','Obs'),14)
        self.sharpe_tree.column('ID',width=0,minwidth=0,stretch=False)
        for col,width in [('Card',155),('Game',58),('Price',68),('Sharpe',66),('30d %',66),('Obs',48)]:
            self.sharpe_tree.column(col,width=width,minwidth=width,stretch=(col=='Card'))
        self.opportunity_tree=self.gridview(right,('ID','Card','Game','Price','Score','7d %','30d %','DD','State'),14)
        self.opportunity_tree.column('ID',width=0,minwidth=0,stretch=False)
        for col,width in [('Card',145),('Game',55),('Price',62),('Score',55),('7d %',52),('30d %',55),('DD',48),('State',82)]:
            self.opportunity_tree.column(col,width=width,minwidth=width,stretch=(col=='Card'))
        self.sharpe_tree.bind('<Double-1>',lambda _e:self.open_ranked_history(self.sharpe_tree))
        self.opportunity_tree.bind('<Double-1>',lambda _e:self.open_ranked_history(self.opportunity_tree))
        self.ranking_data={'all':[],'fresh':[],'sharpe':[],'opportunities':[]}

    def _fmt_pct(self,value):
        return '—' if value is None else f'{value:+.1f}%'

    def refresh_rankings(self):
        if not hasattr(self,'ranking_note') or self.rankings_busy: return
        self.rankings_busy=True
        self.rank_refresh_button.configure(state='disabled')
        self.ranking_note.set('Calculating rankings from recent daily price observations…')
        self.rank_progress.stop(); self.rank_progress.configure(mode='indeterminate'); self.rank_progress.start(12)
        self.rank_progress_text.set('Starting ranking calculation…')
        def worker():
            try:
                progress=lambda current,total,phase: self.events.put(('rank_progress',(current,total,phase)))
                data=build_market_rankings(self.store,progress=progress)
                self.events.put(('rankings_done',data))
            except Exception as exc:
                self.events.put(('rankings_error',str(exc)))
        threading.Thread(target=worker,daemon=True).start()

    def populate_rankings(self,data):
        self.ranking_data=data
        self.clear(self.sharpe_tree); self.clear(self.opportunity_tree)
        for r in data['sharpe'][:30]:
            self.sharpe_tree.insert('','end',values=(r['card_id'],r['name'],r['game'],money(r['latest_price']),
                f"{r['sharpe_30d']:.2f}",self._fmt_pct(r['return_30d']),r['obs_30d']))
        # When no score is supportable yet, show real cards being tracked instead of
        # leaving both tables blank. These rows are explicitly marked Needs history.
        visible_opportunities=data['opportunities'][:30]
        fallback_mode=not visible_opportunities and bool(data['fresh'])
        if fallback_mode:
            visible_opportunities=sorted(data['fresh'],key=lambda r:(-r['observations'],r['name'].casefold()))[:30]
        for r in visible_opportunities:
            scored=r['opportunity_score'] is not None
            state=('30d Sharpe' if r['sharpe_30d'] is not None else 'Provisional') if scored else 'Needs history'
            self.opportunity_tree.insert('','end',values=(r['card_id'],r['name'],r['game'],money(r['latest_price']),
                f"{r['opportunity_score']:.0f}" if scored else '—',self._fmt_pct(r['return_7d']),self._fmt_pct(r['return_30d']),
                self._fmt_pct(r['drawdown_30d']),state))
        fresh=len(data['fresh']); sharp=len(data['sharpe']); opp=len(data['opportunities'])
        if sharp:
            self.sharpe_empty_label.pack_forget()
        else:
            self.sharpe_empty_label.pack(anchor='w',fill='x',pady=(0,5))
        diag=data.get('diagnostics',{})
        if fresh and not sharp and not opp:
            note=(f'{fresh:,} currently priced singles found. The right table lists cards being tracked, not ranked buys. '
                  'Scores stay blank until at least 8 daily observations and a usable return window; 30-day Sharpe needs '
                  '30 daily observations plus 20 consecutive daily returns. No values are invented.')
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
            note=(f'{fresh:,} current priced singles | {sharp:,} with a valid 30-day Sharpe | {opp:,} scored research candidates. '
                  'Cached market prices are estimates, not verified sale prices; score is not a buy signal.')
        self.ranking_note.set(note)

    def open_ranked_history(self,tree):
        selected=tree.selection()
        if not selected: return
        values=tree.item(selected[0],'values')
        if not values: return
        self.history_id.set(values[0]); self.nb.select(self.tabs['Market History']); self.load_history()

    def add_ranked_to_watchlist(self):
        for tree in (self.sharpe_tree,self.opportunity_tree):
            selected=tree.selection()
            if selected:
                values=tree.item(selected[0],'values')
                if values:
                    cid=values[0]
                    self.store.execute('INSERT OR IGNORE INTO watchlist VALUES(?,?)',(cid,utc()))
                    self.load_watch(); self.status.set('Added '+cid+' to watchlist'); return
        messagebox.showinfo(APP,'Select a card in either ranking table first.')

    def export_rankings(self):
        rows=[]
        for label,key in [('Sharpe','sharpe'),('Opportunity','opportunities')]:
            for r in self.ranking_data.get(key,[])[:250]:
                rows.append((label,r['card_id'],r['game'],r['name'],r['price_type'],r['latest_price'],
                    r['sharpe_30d'],r['return_7d'],r['return_30d'],r['drawdown_30d'],
                    r['opportunity_score'],r['observations'],r['obs_30d'],r['age_days']))
        self.save_csv(['ranking','card_id','game','name','price_type','latest_price_usd','sharpe_30d',
            'return_7d_pct','return_30d_pct','drawdown_30d_pct','opportunity_score','observations_35d',
            'observations_30d','data_age_days'],rows,'market_rankings.csv')

    def collector_tab(self):
        p=self.tabs['Collectors']; self.section(p,'MTG + Pokémon market data','This terminal is limited to Magic: The Gathering and Pokémon. TCGCSV supplies daily TCGplayer cached prices; historical archives are optional and downloaded only when requested.')
        ttk.Label(p,text='Daily sync checks last-updated.txt first and skips unchanged data. It imports market/low/mid/high/direct-low metrics for MTG and Pokémon only. Historical archives begin 2024-02-08 and require the 7-Zip command-line tool. A 45-day backfill is typically tens to a few hundred MB depending on source archive sizes; downloaded archives are discarded after import, and completed dates are remembered.',style='Small.TLabel',wraplength=940).pack(anchor='w',pady=(0,8))
        daily=ttk.LabelFrame(p,text=' DAILY SYNC ',padding=8); daily.pack(fill='x',pady=(0,8))
        ttk.Button(daily,text='Sync MTG + Pokémon now',command=self.start_tcgcsv).pack(side='left')
        history=ttk.LabelFrame(p,text=' HISTORICAL PRICE BACKFILL ',padding=8); history.pack(fill='x',pady=(0,8))
        today=datetime.now(timezone.utc).date()
        default_end=today-timedelta(days=1); default_start=default_end-timedelta(days=44)
        self.backfill_start=tk.StringVar(value=default_start.isoformat()); self.backfill_end=tk.StringVar(value=default_end.isoformat())
        ttk.Label(history,text='Start (YYYY-MM-DD)').pack(side='left',padx=(0,5))
        ttk.Entry(history,textvariable=self.backfill_start,width=12).pack(side='left',padx=(0,12))
        ttk.Label(history,text='End').pack(side='left',padx=(0,5))
        ttk.Entry(history,textvariable=self.backfill_end,width=12).pack(side='left',padx=(0,12))
        ttk.Button(history,text='Backfill historical prices',command=self.start_history_backfill).pack(side='left')
        self.log=tk.Text(p,height=14,bg='#0b1726',fg='#bcd8f2',insertbackground='white',wrap='word'); self.log.pack(fill='both',expand=True,pady=8)

    def start_history_backfill(self):
        if self.busy:
            messagebox.showinfo(APP,'A collector is already running. Wait for it to finish before starting historical backfill.'); return
        start=self.backfill_start.get().strip(); end=self.backfill_end.get().strip()
        try:
            start_day=datetime.strptime(start,'%Y-%m-%d').date(); end_day=datetime.strptime(end,'%Y-%m-%d').date()
            if start_day < HISTORY_ARCHIVE_FIRST_DATE: raise ValueError(f'Archives start on {HISTORY_ARCHIVE_FIRST_DATE.isoformat()}.')
            if end_day < start_day: raise ValueError('End date must be on or after start date.')
            days=(end_day-start_day).days+1
            if days > 90:
                if not messagebox.askyesno(APP,f'This will process {days:,} daily archives. The full historical archive collection is around 1 GB; this range could transfer hundreds of MB. Continue?'): return
            elif not messagebox.askyesno(APP,f'This will download up to {days:,} daily archive files for MTG and Pokémon. Each file is usually a few MB. 7-Zip must be installed. Already imported dates will be skipped. Continue?'): return
        except ValueError as exc:
            messagebox.showerror(APP,'Invalid backfill date range: '+str(exc)); return
        def work(report): return backfill_tcgcsv_history(self.store,report,start,end)
        self.launch('TCGCSV historical price backfill',work)
    def paper_tab(self):
        p=self.tabs['Paper Trades']; self.section(p,'Paper-trading ledger','Manual hypothetical fills. These are simulations and do not reflect verified available listings.')
        form=ttk.Frame(p); form.pack(fill='x'); self.paper={}
        for i,(k,v) in enumerate([('Card ID',''),('Side','BUY'),('Quantity','1'),('Price','10'),('Fees','0'),('Notes','')]):
            ttk.Label(form,text=k).grid(row=0,column=i,sticky='w',padx=3)
            var=tk.StringVar(value=v); self.paper[k]=var
            if k=='Side': w=ttk.Combobox(form,textvariable=var,values=['BUY','SELL'],state='readonly',width=8)
            else: w=ttk.Entry(form,textvariable=var,width=22 if k in ('Card ID','Notes') else 10)
            w.grid(row=1,column=i,sticky='w',padx=3)
        ttk.Button(p,text='Record paper trade',command=self.record_trade).pack(anchor='w',pady=12)
        self.trades=self.gridview(p,('Time','Card','Side','Qty','Unit price','Fees','Notes'),14)
    def settings_tab(self):
        p=self.tabs['Settings']; self.section(p,'Data settings and safety','Single-script application. Standard-library Python only: tkinter, sqlite3 and urllib.')
        for label,value in [('Database',str(DB)),('Storage folder',str(ROOT)),('Daily market source','TCGCSV (Magic category 1; Pokémon category 3)'),('Collection cadence','Daily; only syncs when TCGCSV build marker changes'),('Background sync','Optional macOS LaunchAgent; works while the GUI is closed'),('Historical archive','Backfill from 2024-02-08 in Collectors; requires 7-Zip command line'),('External purchases','Disabled'),('Paid APIs','Not used by this collector')]:
            ttk.Label(p,text=f'{label}:  {value}',wraplength=950).pack(anchor='w',pady=7)
        ttk.Button(p,text='Export all cards to CSV',command=self.export_cards).pack(anchor='w',pady=16)
        ttk.Button(p,text='Open storage folder',command=self.open_folder).pack(anchor='w')
        if sys.platform == 'darwin':
            row=ttk.Frame(p); row.pack(anchor='w',pady=(12,0))
            ttk.Button(row,text='Enable daily background sync',command=self.install_launch_agent).pack(side='left',padx=(0,8))
            ttk.Button(row,text='Disable background sync',command=self.remove_launch_agent).pack(side='left')
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
        if op=='progress':
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
            self.rank_progress_text.set('Rankings ready')
            self.populate_rankings(payload)
        elif op=='rankings_error':
            self.rankings_busy=False
            self.rank_refresh_button.configure(state='normal')
            self.rank_progress.stop(); self.rank_progress.configure(mode='determinate',maximum=1); self.rank_progress['value']=0
            self.rank_progress_text.set('Ranking calculation failed')
            self.ranking_note.set('Ranking refresh failed: '+str(payload))

    def logmsg(self,msg):
        self.log.insert('end',f'[{datetime.now().strftime("%H:%M:%S")}] {msg}\n'); self.log.see('end'); self.status.set(msg)
    def launch(self,label,work):
        if self.busy: messagebox.showinfo(APP,'A collector is already running.'); return
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
                elif op in ('progress','rank_progress','rankings_done','rankings_error'): self.handle_async_event(op,payload)
                elif op=='done': self.busy=False; self.end_activity(payload,True); self.logmsg(payload); self.refresh()
                elif op=='error': self.busy=False; self.end_activity(payload,False); self.logmsg('ERROR: '+payload); messagebox.showerror('Collection error',payload)
        except queue.Empty: pass
        self.after(200,self.drain)
    def fetch_scryfall(self):
        if not messagebox.askyesno('Bulk download','Download Scryfall bulk card data? This may be hundreds of MB. One user-triggered bulk file, not per-card requests.'): return
        def work(report):
            report('Checking bulk dataset index')
            best, url, suffix = choose_scryfall_bulk()
            updated=best.get('updated_at','')[:10]
            fname=ROOT / ('scryfall_default_'+updated+suffix)
            if fname.exists(): report('Using existing bulk file '+fname.name)
            else:
                report('Downloading updated bulk snapshot '+updated)
                download(url,fname,report)
            report('Importing bulk card data')
            return ingest_scryfall(fname,self.store,report)
        self.launch('Scryfall daily bulk',work)
    def pick_scryfall(self):
        path=filedialog.askopenfilename(title='Choose Scryfall bulk JSON',filetypes=[('Scryfall bulk','*.json *.jsonl *.gz'),('All','*')])
        if path: self.launch('Local MTG bulk',lambda report:ingest_scryfall(path,self.store,report))
    def pick_pokemon(self):
        paths=filedialog.askopenfilenames(title='Choose Pokémon set JSON files',filetypes=[('JSON','*.json'),('All','*')])
        if paths:
            def work(report):
                n=0
                for path in paths: n+=ingest_pokemon(path,self.store,report)
                return n
            self.launch('Local Pokémon JSON',work)
    def refresh(self):
        cardcount=self.store.q("SELECT game,COUNT(*) FROM cards WHERE game IN ('MTG','Pokémon') AND item_type='card' GROUP BY game")
        productcount=self.store.q("SELECT COUNT(*) FROM cards WHERE game IN ('MTG','Pokémon') AND item_type='sealed_product'")[0][0]
        prices=self.store.q("SELECT COUNT(*) FROM prices p JOIN cards c ON c.id=p.card_id WHERE c.game IN ('MTG','Pokémon')")[0][0]; watched=self.store.q("SELECT COUNT(*) FROM watchlist w JOIN cards c ON c.id=w.card_id WHERE c.game IN ('MTG','Pokémon')")[0][0]
        mtg=dict(cardcount).get('MTG',0); poke=dict(cardcount).get('Pokémon',0)
        self.kpis.config(text=f'MTG SINGLES  {mtg:,}        POKÉMON SINGLES  {poke:,}        SEALED PRODUCTS  {productcount:,}        PRICE OBSERVATIONS  {prices:,}        WATCHLIST  {watched:,}')
        self.clear(self.jobtree)
        for start,task,status,cnt,msg in self.store.q('SELECT started_at,task,status,count,message FROM jobs ORDER BY id DESC LIMIT 50'):
            self.jobtree.insert('', 'end', values=(start,task,status,cnt,msg))
        self.load_watch(); self.load_trades(); self.refresh_rankings()
    def clear(self,tree):
        for x in tree.get_children(): tree.delete(x)
    def find(self):
        needle=self.search.get().strip(); game=self.game.get(); self.clear(self.cards)
        sql="SELECT id,game,item_type,name,set_code,collector_number,rarity FROM cards WHERE game IN ('MTG','Pokémon')"; args=[]
        if needle: sql+=' AND (name LIKE ? OR id LIKE ?)'; args.extend(['%'+needle+'%']*2)
        if game!='All':sql+=' AND game=?';args.append(game)
        sql+=' ORDER BY name LIMIT 500'
        for row in self.store.q(sql,tuple(args)): self.cards.insert('','end',values=row)
        self.status.set('Showing up to 500 results. Narrow your search for more precise matches.')
    def selected_card(self):
        ids=self.cards.selection()
        return self.cards.item(ids[0],'values')[0] if ids else None
    def watch_selected(self):
        cid=self.selected_card()
        if not cid: messagebox.showinfo(APP,'Select a card first.');return
        self.store.execute('INSERT OR IGNORE INTO watchlist VALUES(?,?)',(cid,utc())); self.load_watch(); self.status.set('Added '+cid+' to watchlist')
    def card_detail(self):
        cid=self.selected_card()
        if cid:
            self.history_id.set(cid); self.nb.select(self.tabs['Market History']); self.load_history()
    def load_history(self):
        cid=self.history_id.get().strip(); self.clear(self.pricetree)
        if not cid:
            self.history_status.set('Select a card to view history.'); self._draw_history_chart([]); return
        card=self.store.q("SELECT name,game,item_type FROM cards WHERE id=? AND game IN ('MTG','Pokémon')",(cid,))
        if not card:
            self.history_status.set('This record is not in the supported MTG/Pokémon catalog.'); self._draw_history_chart([]); return
        rows=self.store.q('SELECT source_time,price,currency,source,price_type,collected_at FROM prices WHERE card_id=? ORDER BY source_time DESC LIMIT 2000',(cid,))
        for row in rows: self.pricetree.insert('','end',values=(row[0],money(row[1]),row[2],row[3],row[4],row[5]))
        market=self.store.q("SELECT source_time,price,price_type FROM prices WHERE card_id=? AND source='tcgcsv_tcgplayer' AND price_type LIKE 'market_%' AND price>0 ORDER BY source_time,CASE WHEN price_type='market_Normal' THEN 0 WHEN price_type='market_Nonfoil' THEN 1 ELSE 2 END",(cid,))
        # Collapse subtype variants to one point per day, preferring Normal when present.
        by_day={}
        for stamp,price,price_type in market:
            day=str(stamp)[:10]
            if day not in by_day or price_type == 'market_Normal':
                by_day[day]=float(price)
        points=sorted(by_day.items())
        self._draw_history_chart(points)
        if not rows:
            self.history_status.set(f"{card[0][1]} · {card[0][0]} — no saved price observations yet. Run a successful daily sync, then use Collectors → Backfill historical prices.")
        else:
            self.history_status.set(f"{card[0][1]} · {card[0][0]} · {len(rows):,} price observations · {len(points):,} daily market points · earliest {points[0][0] if points else 'n/a'} · latest {points[-1][0] if points else 'n/a'}")
    def load_watch(self):
        self.clear(self.watchtree)
        for row in self.store.q("SELECT w.card_id,c.game,c.name,w.added_at FROM watchlist w JOIN cards c ON c.id=w.card_id WHERE c.game IN ('MTG','Pokémon') ORDER BY w.added_at DESC"):
            self.watchtree.insert('','end',values=row)
    def unwatch(self):
        sel=self.watchtree.selection()
        if sel:
            cid=self.watchtree.item(sel[0],'values')[0]
            self.store.execute('DELETE FROM watchlist WHERE card_id=?',(cid,));self.load_watch()
    def calculate(self):
        try:
            v={k:float(x.get()) for k,x in self.inputs.items()}
            gross,roi=calculate_net_profit(v['Buy price'],v['Potential resale'],v['Selling fee %'],v['Other costs'],v['Quantity'])
            self.profit.set(f'Illustrative net P/L: {money(gross)}   |   ROI: {roi:.1f}%' if roi is not None else f'Illustrative net P/L: {money(gross)}   |   ROI: N/A (zero cost)')
        except (ValueError,ZeroDivisionError) as ex: messagebox.showerror('Invalid inputs',str(ex))
    def record_trade(self):
        try:
            cid=self.paper['Card ID'].get().strip(); side=self.paper['Side'].get()
            qty=int(self.paper['Quantity'].get()); price=float(self.paper['Price'].get()); fee=float(self.paper['Fees'].get())
            if not cid or side not in ('BUY','SELL') or qty<=0 or price<0 or fee<0: raise ValueError('Invalid trade fields')
            if not self.store.q("SELECT 1 FROM cards WHERE id=? AND game IN ('MTG','Pokémon')",(cid,)):
                raise ValueError('Card ID must belong to an MTG or Pokémon catalog record. Search Card Explorer and copy its ID.')
            self.store.execute('INSERT INTO paper_trades(created_at,card_id,side,quantity,price,fee,notes) VALUES(?,?,?,?,?,?,?)',(utc(),cid,side,qty,price,fee,self.paper['Notes'].get()))
            self.load_trades();self.status.set('Paper trade recorded; no order placed')
        except ValueError as e:messagebox.showerror('Invalid trade',str(e))
    def load_trades(self):
        self.clear(self.trades)
        for row in self.store.q("SELECT t.created_at,t.card_id,t.side,t.quantity,t.price,t.fee,t.notes FROM paper_trades t JOIN cards c ON c.id=t.card_id WHERE c.game IN ('MTG','Pokémon') ORDER BY t.id DESC LIMIT 400"):self.trades.insert('','end',values=row)
    def save_csv(self,heads,rows,name):
        path=filedialog.asksaveasfilename(defaultextension='.csv',initialfile=name,filetypes=[('CSV','*.csv')])
        if not path:return
        with open(path,'w',newline='',encoding='utf-8-sig') as f:
            writer=csv.writer(f);writer.writerow(heads);writer.writerows(rows)
        self.status.set('Exported '+path)
    def export_history(self):
        cid=self.history_id.get().strip()
        if not cid:messagebox.showinfo(APP,'Enter a card ID first.');return
        heads=['source_time','price','currency','source','price_type','collected_at']
        self.save_csv(heads,self.store.q('SELECT source_time,price,currency,source,price_type,collected_at FROM prices WHERE card_id=? ORDER BY source_time',(cid,)),'card_history.csv')
    def export_cards(self):
        self.save_csv(['id','game','item_type','name','set_code','collector_number','rarity','finish'],self.store.q("SELECT id,game,item_type,name,set_code,collector_number,rarity,finish FROM cards WHERE game IN ('MTG','Pokémon') ORDER BY game,name"),'cards.csv')
    def open_folder(self):
        import subprocess
        if sys.platform=='darwin': subprocess.Popen(['open',str(ROOT)])
        elif sys.platform.startswith('win'): os.startfile(str(ROOT))
        else: subprocess.Popen(['xdg-open',str(ROOT)])
    def close(self):
        if self.busy:
            messagebox.showwarning(APP,'A collector is still running. Wait for it to finish before closing so the database connection is not interrupted.')
            return
        self.store.close();self.destroy()


# Collection extensions: only bulk archives, never card-by-card API polling.
POKEMON_ARCHIVE = 'https://codeload.github.com/PokemonTCG/pokemon-tcg-data/zip/refs/heads/master'

class AutomatedTerminal(Terminal):
    """Single-file GUI with daily TCGCSV catalog and price synchronization."""
    def __init__(self):
        super().__init__()
        self.title('Card Market Terminal | Daily MTG + Pokémon Market Data')
        self.auto_enabled = tk.BooleanVar(value=self.store.get_setting('auto_collect','0')=='1')
        self.build_auto_controls()
        self.after(4000,self.schedule_tick)

    def build_auto_controls(self):
        p=self.tabs['Collectors']
        bar=ttk.LabelFrame(p,text=' DAILY TCGCSV SYNC ',padding=12)
        bar.pack(fill='x',before=self.log,pady=(0,8))
        ttk.Label(bar,text='Automatically discovers products and imports daily TCGplayer market metrics for Magic and Pokémon.',style='Small.TLabel').pack(anchor='w')
        ttk.Button(bar,text='Sync MTG + Pokémon now',command=self.start_tcgcsv).pack(side='left',padx=(0,12),pady=9)
        consent=ttk.Frame(p); consent.pack(fill='x',before=self.log,pady=(0,8))
        ttk.Checkbutton(consent,text='Enable daily automatic sync while this app is open',variable=self.auto_enabled,command=self.change_auto).pack(anchor='w')
        ttk.Label(consent,text='Uses TCGCSV documented pacing and a custom User-Agent. The daily build marker is checked first; unchanged data is not re-downloaded. Scheduled jobs do not run while the app is closed.',style='Small.TLabel',wraplength=940).pack(anchor='w',pady=4)
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
        if self.busy: messagebox.showinfo(APP,'A collector is already running.'); return
        self.store.setting('tcgcsv_attempt',time.time())
        def work(report):
            report('Source: TCGCSV daily build; Magic + Pokémon; no individual card requests')
            count=sync_tcgcsv_daily(self.store,report)
            return count
        self.launch('TCGCSV daily MTG + Pokémon sync',work)

    def drain(self):
        try:
            while True:
                op,payload=self.events.get_nowait()
                if op=='log': self.logmsg(payload)
                elif op in ('progress','rank_progress','rankings_done','rankings_error'): self.handle_async_event(op,payload)
                elif op=='done':
                    self.busy=False; self.end_activity(payload,True); self.logmsg(payload); self.refresh(); self.update_source_note()
                elif op=='error':
                    self.busy=False; self.end_activity(payload,False); self.logmsg('ERROR: '+payload); self.update_source_note()
                    messagebox.showerror('Collection error',payload)
        except queue.Empty: pass
        self.after(200,self.drain)

def run_headless_sync():
    """Run one source-marker-checked TCGCSV sync without opening Tkinter."""
    store=Store(); jid=None
    try:
        jid=store.start_job('TCGCSV daily MTG + Pokémon sync (headless)')
        print('Card Market Terminal: checking TCGCSV daily dataset marker',flush=True)
        count=sync_tcgcsv_daily(store,lambda msg: print(msg,flush=True))
        store.end_job(jid,'finished',count,'Completed')
        print(f'Sync complete. {count:,} catalog records processed.',flush=True)
        return 0
    except Exception as e:
        if jid is not None:
            try: store.end_job(jid,'error',0,repr(e))
            except Exception: pass
        print(f'Sync failed: {e}',file=sys.stderr,flush=True)
        return 1
    finally:
        store.close()


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
        ids={row[0] for row in self.store.q('SELECT DISTINCT card_id FROM prices')}
        self.assertEqual(ids,{'tcgcsv:1:10','tcgcsv:3:30'})

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
        with sqlite3.connect(DB) as con:
            con.execute('DROP TABLE cards')
            con.execute('''CREATE TABLE cards (id TEXT PRIMARY KEY, game TEXT NOT NULL, name TEXT NOT NULL,
                set_code TEXT, collector_number TEXT, rarity TEXT, finish TEXT, details TEXT, updated_at TEXT NOT NULL)''')
            con.execute("INSERT INTO cards VALUES('old:1','MTG','Old Card','SET','1','Rare','Normal','{}',?)",(utc(),))
            old_detail=json.dumps({'provider':'TCGCSV / TCGplayer cached product prices','extended_data':[]})
            con.execute("INSERT INTO cards VALUES('old:2','Pokémon','Silver Tempest Booster Box','SET','','','Normal',?,?)",(old_detail,utc()))
        self.store=Store()
        self.assertIn('item_type',{r[1] for r in self.store.q('PRAGMA table_info(cards)')})
        self.assertEqual(self.store.q("SELECT item_type FROM cards WHERE id='old:1'")[0][0],'card')
        self.assertEqual(self.store.q("SELECT item_type FROM cards WHERE id='old:2'")[0][0],'sealed_product')

    def test_stream_scryfall_json_and_jsonl_gzip(self):
        arr=ROOT/'array.json'; arr.write_text('[{"id":"a"},{"id":"b"}]',encoding='utf-8')
        self.assertEqual([x['id'] for x in stream_scryfall(arr)],['a','b'])
        gz=ROOT/'records.jsonl.gz'
        with gzip.open(gz,'wt',encoding='utf-8') as f: f.write('{"id":"c"}\n{"id":"d"}\n')
        self.assertEqual([x['id'] for x in stream_scryfall(gz)],['c','d'])

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
        self.assertEqual(result['diagnostics']['recent_market_prices'],1)

    def test_ranking_progress_reports_scanned_price_rows(self):
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
        self.assertEqual(events[-1][0],3)
        self.assertEqual(events[-1][1],3)

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
        self.assertEqual(first,2)
        self.assertEqual(second,0)
        self.assertEqual(self.store.q('SELECT COUNT(*) FROM cards')[0][0],2)
        self.assertEqual(self.store.q('SELECT COUNT(*) FROM prices')[0][0],2)
        self.assertEqual(self.store.get_setting('tcgcsv_dataset_marker'),marker)
        self.assertEqual(json_mock.call_count,6,'unchanged marker should skip every category/group endpoint')

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

    def test_tcgcsv_404_empty_group_and_429_stop(self):
        not_found=urllib.error.HTTPError('https://tcgcsv.com/tcgplayer/3/1/products',404,'Not Found',None,None)
        with mock.patch.object(urllib.request,'urlopen',side_effect=not_found) as opened, mock.patch.object(time,'sleep',return_value=None):
            self.assertEqual(tcgcsv_json('https://tcgcsv.com/tcgplayer/3/1/products',allow_not_found=True)['results'],[])
            self.assertEqual(opened.call_count,1)
        throttled=urllib.error.HTTPError('https://tcgcsv.com/tcgplayer/3/groups',429,'Too Many Requests',None,None)
        with mock.patch.object(urllib.request,'urlopen',side_effect=throttled) as opened, mock.patch.object(time,'sleep',return_value=None):
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
        success=io.BytesIO(json.dumps({'success':True,'results':[]}).encode())
        with mock.patch.object(urllib.request,'urlopen',side_effect=[unavailable,success]) as opened, mock.patch.object(time,'sleep',return_value=None):
            result=tcgcsv_json('https://tcgcsv.com/tcgplayer/3/groups')
        self.assertEqual(result['results'],[])
        self.assertEqual(opened.call_count,2)

    def test_marker_endpoint_429_is_reported_without_retry(self):
        throttled=urllib.error.HTTPError(TCGCSV_LAST_UPDATED,429,'Too Many Requests',None,None)
        with mock.patch.object(urllib.request,'urlopen',side_effect=throttled) as opened, mock.patch.object(time,'sleep',return_value=None):
            with self.assertRaisesRegex(RuntimeError,'wait at least 10 minutes'):
                tcgcsv_text(TCGCSV_LAST_UPDATED)
        self.assertEqual(opened.call_count,1)


def run_self_tests():
    suite=unittest.defaultTestLoader.loadTestsFromTestCase(OfflineSelfTests)
    result=unittest.TextTestRunner(verbosity=2).run(suite)
    return 0 if result.wasSuccessful() else 1

if __name__=='__main__':
    if '--self-test' in sys.argv:
        sys.exit(run_self_tests())
    if '--sync' in sys.argv:
        sys.exit(run_headless_sync())
    try: AutomatedTerminal().mainloop()
    except tk.TclError as e:
        print('Tkinter GUI could not start:',e,file=sys.stderr)
        print('On macOS, use Python installed from python.org with Tk support.',file=sys.stderr)
        sys.exit(1)
