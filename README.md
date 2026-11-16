# Card Market Terminal

A single-file desktop app (Python + Tkinter) for tracking and analysing prices of trading card singles for
**Magic: The Gathering, Pokémon, One Piece and Riftbound**. It downloads free daily TCGplayer price data, keeps a
local SQLite history, and shows market indices, movers, rankings, forecasts, buy/sell price suggestions after fees,
a set calendar, and a portfolio with hold/sell signals.

It is a research tool. It does not place trades, connect to a marketplace account, or buy or sell anything.

## Quick start

```
# Windows
py "Card Market Terminal.py"

# macOS / Linux
python3 "Card Market Terminal.py"
```

Then click **1. Download today's prices** on the Today tab (or type `SYNC` in the command box). Prices, rankings and
the daily brief are stored in `~/CardMarketTerminalData` by default (see [Data and files](#data-and-files)).

## Features

- **Command line** (top of the window, `Ctrl+K` to focus). Type a card name to open its chart, or a command:

  | Command | Opens |
  |---|---|
  | `TODAY` (`DO`, `CHECK`) | What to buy and sell today, plus the "should I buy at this price / what should I sell for" checker |
  | `<card name>` | The card's chart; add `FOIL` for the foil printing |
  | `MON` (`TOP`, `MOV`, `IDX`) | Market monitor: indices, breadth, movers, best buys, alerts |
  | `BUY` (`LOOK`) | Cards to look for, after fees, liquidity and forecast |
  | `RANK` (`SHARPE`) | Risk-adjusted rankings and momentum |
  | `SETS`, `CAL`, `SECT` | Set heatmap and release calendar |
  | `SET <code>` | Cards to look for in one set, e.g. `SET DSK` |
  | `CYCLE` (`NEW`, `PRESELL`), `VARIANTS` | Release-cycle curves; variant summary |
  | `PORT` (`W`, `WATCH`) | Portfolio and watchlist with sell signals |
  | `BT`, `BACKTEST`, `TRADES` | Strategy backtest and your trade log |
  | `HIST` (`GP`) | Market history |
  | `COL` | Collectors (data downloads) |
  | `SYNC` | Download today's prices now |
  | `BRIEF` | Open the daily brief (HTML) |
  | `GLOSSARY`, `DEFINE <word>` | Explain a column or term |
  | `HELP` | Command list |

- **Tabs:** Today, Overview, Cards to Look For, Sharpe & Opportunities, Market History, Sets & Catalysts,
  Portfolio, Backtest & Trades, Collectors, Settings. Overview, Sharpe & Opportunities and Collectors are hidden
  unless **Settings > Show advanced tabs** is ticked; typing their command (`MON`, `RANK`, `COL`) also opens them.
  Clicking a column heading explains it.
- **Analytics:** per-printing returns and Sharpe ratio (Newey-West adjusted, Benjamini-Hochberg significance),
  liquidity labels, spike/listing-artifact filtering, market indices and breadth, calibrated 7/14/30-day
  forecasts, release-phase and long-run set curves, and a strategy backtest.
- **Pricing:** buy limits and suggested list prices after TCGplayer-style fees, shipping, card condition and
  position-size limits (Kelly fraction, per-card and per-set caps).
- **Portfolio:** holdings and watch-only entries with price alerts, a buy/sell trade log, and suggested pricing
  settings learned from your trades (applied only when you click Apply).
- **Exports:** CSV exports (rankings, buy list, sets, portfolio, trades, card history, all cards) and a TCGplayer
  Mass Entry text copy.
- **Background sync:** optional daily sync while the app is closed (Windows Task Scheduler or macOS LaunchAgent).
- **Portable copy:** copy the script and its data to a USB drive to use on another computer.

## Requirements

- Python 3.8 or newer with Tkinter (a current 3.x release is recommended). The script uses only the standard
  library; there is nothing to `pip install`.
  - Windows: the python.org installer includes Tkinter.
  - macOS: use Python from python.org (the app says so if Tk fails to start). Homebrew Python needs
    `brew install python-tk`.
  - Linux: install your distribution's Tk package (for example `python3-tk`).
- Internet access for data downloads.
- Optional: **7-Zip** command line (`7zz`, `7z` or `7za` on PATH, or `7-Zip\7z.exe` under Program Files on
  Windows). Needed only for the TCGCSV historical archive backfill.
- Background sync is built in for Windows and macOS only, and desktop notifications for Windows only. On Linux
  the GUI and `--sync` work; schedule `--sync` yourself (for example with cron) if you want daily updates.

## Running

The script file name contains spaces, so quote it.

| Task | Windows | macOS / Linux |
|---|---|---|
| Open the GUI | `py "Card Market Terminal.py"` | `python3 "Card Market Terminal.py"` |
| One headless sync (no window) | `py "Card Market Terminal.py" --sync` | `python3 "Card Market Terminal.py" --sync` |
| Offline self-tests | `py "Card Market Terminal.py" --self-test` | `python3 "Card Market Terminal.py" --self-test` |

`--self-test` runs the built-in unittest suite (no GUI, no network). `--sync` downloads the day's TCGCSV data,
runs the side feeds, precomputes rankings, logs triggered portfolio alerts and writes the daily brief. It exits
with code 1 only if the TCGCSV sync itself fails; errors in the later steps are printed but still exit 0. Run from a
terminal, it prints to the console; the log files below are written only by scheduled runs.

### First run

The Today tab shows a **Getting started** panel until prices are stored.

1. **1. Download today's prices** (or type `SYNC`). The first sync downloads the full catalog for all four games
   and takes about 10-20 minutes; later syncs take a minute or two.
2. Optional: **2. Turn on daily updates** installs background sync (same as Settings > **Enable daily background
   sync**; Windows and macOS). Alternatively tick "Enable daily automatic sync while this app is open" on the
   Collectors tab.
3. **3. Set my selling fees and shipping** opens Settings: set your fees, shipping and capital.
4. Optional, for MTG history right away: Collectors > **Import last 90 days of MTG prices** (MTGJSON, about
   60 MB download). Requires a completed sync first.

The Collectors tab is hidden by default: type `COL` or tick **Settings > Show advanced tabs**.

### Background sync

| Platform | Mechanism | Schedule | Logs |
|---|---|---|---|
| Windows | Scheduled task `CardMarketTerminal Daily Sync` (runs `pythonw.exe <script> --sync --data <data folder>`, signed-in user, no stored password, catches up after sleep) | 14:30 and 22:00 local | `daily-sync.log`, `daily-sync-error.log` in the data folder |
| macOS | LaunchAgent `~/Library/LaunchAgents/com.cardmarketterminal.daily-sync.plist` | 14:30 local | same files |
| Linux | None built in | - | - |

Both point at the script's current path and the current Python interpreter. If you move the script or change
Python, disable and re-enable background sync.

## Configuration

### Environment variable

| Variable | Effect |
|---|---|
| `CMT_DATA` | Path of the data folder. Overrides the default location (see below). |

Background sync uses the data folder the app was using when you enabled it: the macOS LaunchAgent sets `CMT_DATA`
to it, and the Windows task passes it as `--data FOLDER`. If you later change `CMT_DATA` or move the data
folder, disable and re-enable background sync.

No other environment variables, API keys or config files are read. (On Windows, `ProgramFiles`,
`ProgramFiles(x86)` and `ProgramW6432` are read only to locate 7-Zip.)

### In-app settings

Settings are stored in the `settings` table of the database and edited in the GUI.

- **Pricing assumptions** (Settings tab). Defaults: selling fee 13.25%, fixed per-order fee $0.30, per-card
  handling cost $0.25, outgoing shipping $1.00 plain / $4.50 tracked from $50, shipping charged to the buyer
  $0.99 below $5, inbound shipping $0.50 per card, horizon 14 days, required win probability 60%, sell-through
  0.5, capital $5,000, max $250 per card, max 15% per set, Kelly fraction 0.25, minimum profit $1.00 and ROI 10%,
  condition multipliers LP 0.85 / MP 0.70 / HP 0.55 / DMG 0.40, played-copy ratio 0.80.
- **Risk-free rate** for Sharpe calculations: default 4.04%; **Fetch T-bill rate** updates it from FRED.
- **Show advanced tabs.**
- **Enable daily automatic sync while this app is open** (Collectors tab). Checks once a day; retries at most
  hourly.
- Data upkeep (Settings tab):
  - **Cardmarket (EU) module:** shows EU prices in USD and flags MTG cards rising in Europe first. Uses MTGJSON
    plus the FRED EUR/USD rate.
  - **Keep detailed daily price rows for N days** (default 120, minimum 60, 0 = forever).
  - **Back up & tidy now.**
  - Windows only: **After each background sync, write the daily brief and show a Windows notification** (default
    on; the brief is written either way, this switch controls the notification).

## Data sources

All sources are free and need no account or key. Requests send the User-Agent
`CardMarketTerminal/<version> (daily market-data research; local desktop application)`.

| Source | Used for | Frequency |
|---|---|---|
| TCGCSV (`tcgcsv.com/tcgplayer`) | Daily TCGplayer catalog and prices (market, low, mid, high, direct low) for categories 1 MTG, 3 Pokémon, 68 One Piece, 89 Riftbound; set lists | Daily. Checks `last-updated.txt` first and skips unchanged builds. Paced at 0.11 s between requests, capped at 8,000 requests/day. HTTP 429 stops the sync and blocks requests for 10 minutes. |
| TCGCSV archive (`tcgcsv.com/archive/tcgplayer`) | Historical daily prices from 2024-02-08 (`.ppmd.7z`, needs 7-Zip) | On request; availability checked weekly (the archive was offline at time of writing) |
| MTGJSON (`mtgjson.com/api/v5`) | MTG card identifiers; 90-day TCGplayer history; Card Kingdom buylist and Cardmarket (EUR) prices | Identifiers weekly; today's prices daily; 90-day import on request |
| Scryfall (`api.scryfall.com`) | MTG set list and release dates; oracle bulk file for format legality, bans and EDHREC rank | Set list daily; oracle bulk weekly |
| FRED (`fred.stlouisfed.org`) | 3-month T-bill rate (`DTB3`); EUR/USD (`DEXUSEU`) for the Cardmarket module | On request; EUR/USD daily when the module is on |
| PriceCharting (`www.pricecharting.com`) | Monthly long-term price history for a card ("Long-term history") and a weekly sample of set chase cards for long-run curves (MTG, Pokémon, One Piece) | On request / weekly; one request every 3 s; cached 7 days |

## Data and files

Data folder (`ROOT`), chosen in this order:

1. `--data FOLDER` on the command line (used by the Windows scheduled task), then `CMT_DATA`, if set.
2. A `CardMarketTerminalData` folder next to the script, if it exists (portable mode).
3. `~/CardMarketTerminalData` (on Windows, `%USERPROFILE%\CardMarketTerminalData`).

Settings > **Open storage folder** opens it; the Settings tab also shows the exact paths.

| File | Contents |
|---|---|
| `market.sqlite3` (+ `-wal`, `-shm`) | Main database (WAL mode) |
| `rankings_cache.json.gz` | Precomputed rankings |
| `forecast_model_7d.json`, `forecast_model_14d.json`, `forecast_model_30d.json` | Forecast models |
| `strategy_backtest.json` | Last backtest result |
| `release_curves.json` | Release-cycle curves |
| `pricing_cache.pickle` | Cached per-row pricing results |
| `pricecharting_cache.json` | PriceCharting responses (7-day cache) |
| `mtgjson_cardIdentifiers.csv.xz` | MTGJSON identifier file (refreshed weekly) |
| `daily_brief.html` | Daily brief |
| `daily-sync.log`, `daily-sync-error.log` | Background sync logs |
| `tcgcsv_sync.lock` | Prevents two syncs running at once (ignored after 6 hours) |
| `tcgcsv_request_budget.json` | Daily TCGCSV request count and the 10-minute cooldown after HTTP 429 |
| `backups/essentials.sqlite3` | Weekly rolling backup of settings, portfolio, trades, printings, daily history, set info, market events, MTG oracle data |

Scryfall bulk files and the MTGJSON 90-day price file are downloaded to a temporary folder and deleted after import;
they are not kept in the data folder.

### Database tables

| Table | Purpose |
|---|---|
| `cards` | Catalog (game, name, set, number, rarity, finish, item type, details JSON) |
| `prices` | Raw TCGCSV price rows; pruned after the retention window |
| `daily` | Compact daily history per card and printing (market, low, buylist, EU), kept permanently |
| `printings` | Printing/price-type names |
| `tcgcsv_groups` | Synced TCGCSV groups (sets) |
| `set_info` | Set names and release dates (Scryfall, TCGCSV) |
| `portfolio` | Holdings and watchlist, cost, price alerts |
| `trades` | Trade log with predicted vs actual results |
| `settings` | Key/value settings and sync state |
| `jobs` | Collector run history |
| `mtg_oracle` | MTG legality, bans, EDHREC rank |
| `market_events` | Dated events (bans, legality changes) |
| `pc_sets`, `pc_series` | PriceCharting long-run samples |
| `watchlist`, `signals`, `paper_trades` | Legacy tables from earlier versions (the old watchlist is migrated into `portfolio`) |

Raw rows older than the retention window are deleted weekly; their market and lowest-listing prices remain in
`daily`. The schema is created and upgraded automatically on start.

## Moving to another computer (portable copy)

There is no installer or build script. To carry the app with its data:

1. Settings > **Make a portable copy…** and pick an empty folder (e.g. on a USB drive).
2. The folder gets `Card Market Terminal.py`, a `CardMarketTerminalData` folder (a compact database without the
   raw `prices` rows, plus the cached files) and `READ ME - portable copy.txt`.
3. Run the script from that folder; it uses the data folder next to it.

Use one computer at a time, and do not run it from a live cloud-sync folder on two machines at once. A FAT32 drive
cannot hold files over 4 GB; use exFAT or NTFS for a large database.

## Troubleshooting

| Symptom | Cause / fix |
|---|---|
| "Tkinter GUI could not start" or `No module named 'tkinter'` | Python lacks Tk. On macOS install Python from python.org; on Linux install `python3-tk`. `--sync` and `--self-test` work without Tk. |
| Collectors tab is missing | It is an advanced tab. Type `COL` or tick Settings > Show advanced tabs. |
| App says prices are being saved and will not open | A background sync holds the database. Wait a few minutes and reopen. |
| "A TCGCSV sync already appears to be running" | Another sync (GUI or background) is active. If none is, the lock file `tcgcsv_sync.lock` in the data folder clears itself after 6 hours. |
| "No successful TCGCSV sync for N hours" / "Partial sync?" | Type `SYNC`. A partial warning means far fewer prices than the previous sync (incomplete source build); the next full sync clears it. |
| Sync stops with a throttling message | TCGCSV returned HTTP 429; further requests are blocked for 10 minutes. Wait and retry later. |
| Backfill fails or says to install 7-Zip | Install 7-Zip and make `7z`/`7zz` available on PATH. The TCGCSV archive may also be offline. |
| "First download today's prices once" on the MTGJSON import | Run a TCGCSV sync first; MTGJSON history is matched to that catalog. |
| Background sync stopped after moving the script | The scheduled task / LaunchAgent stores the old path. Disable and re-enable it in Settings. |
| Empty rankings or forecasts | Not enough history yet. Rankings need about 30 days of daily prices per printing; the MTGJSON import fills MTG history faster. |
| Background run failed | Check `daily-sync-error.log` in the data folder. |

## Code layout

Everything is in `Card Market Terminal.py`, in roughly this order:

| Area | Main names |
|---|---|
| Constants and paths | `APP`, `SUPPORTED_GAMES`, `_data_root`, `ROOT`, `DB`, `TCGCSV_*`, `MTGJSON_*`, `RANK_*`, `SPIKE_*` |
| Metrics | `daily_series`, `calculate_market_metrics`, `benjamini_hochberg`, `filter_ranked_rows` |
| Pricing and sizing | `DEFAULT_PRICING`, `selling_costs`, `suggested_quantity`, `pricing_targets`, `best_list_price` |
| Forecasting and backtest | `build_forecast_models`, calibration helpers, `run_strategy_backtest` |
| Trades | `record_trade`, `trade_ledger`, `learn_from_trades` |
| Side feeds | `sync_mtgjson_today`, `refresh_scryfall_oracle`, `refresh_longrun`, `pricecharting_history`, `refresh_catalysts`, `fetch_risk_free_rate`, `refresh_fx` |
| Decisions and views | `decide_buy`, `decide_sell`, `todays_actions`, `build_market_rankings`, `market_movers`, `daily_brief_html` |
| Storage | `Store`, `ReadOnlyStore` (SQLite schema and migrations) |
| TCGCSV collector | `tcgcsv_fetch`, `sync_tcgcsv_daily`, `backfill_tcgcsv_history`, `tcgcsv_sync_lock` |
| MTGJSON history | `backfill_mtgjson_history`, `ingest_mtgjson_prices` |
| Scheduling | `install_windows_sync_task`, `remove_windows_sync_task`; macOS LaunchAgent methods on the GUI class |
| GUI | `Terminal` (tabs, command line), `AutomatedTerminal` (sync controls and in-app scheduler) |
| Upkeep and portability | `run_side_feeds`, `run_maintenance`, `backup_essentials`, `make_portable_copy` |
| Entry points | `run_headless_sync`, `OfflineSelfTests` / `run_self_tests`, `if __name__ == '__main__'` |

