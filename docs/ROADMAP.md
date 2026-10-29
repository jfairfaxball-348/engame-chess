# Mathematical roadmap

This is a **material-class roadmap**, not a session log. [The live work note](../NEXT_SESSION.md) carries the immediate problem; [theorem ledger](../theorems/LEDGER.csv) is authoritative for frozen proof scope. Existing numbered session records are historical only.

## Overall ambition
- **Immediate programme:** reach [Syzygy parity](CHARTER.md#parity-target-hard-boundary-owner-2026-10-29) (WDL50 and DTZ50 for fresh positions) for each material class without using Syzygy or other lookup tables. Nothing beyond parity is required before moving on.
- **Master operational milestone:** parity with seven-piece lookup-table knowledge via general, Lean-formalised mathematics, NOT via replayed tables or enumerations.
- **Distant aspiration, unproved:** ultra-weakly solve standard chess by proving its initial-position value is a draw; no playable engine or move recipe is required.

## Class coverage (not percentages)

| Material class | Verified coverage | Outstanding |
|---|---|---|
| K vs K | Draw/dead-position results frozen | None within proved scope |
| K+B vs K | Draw/dead-position results frozen | None within proved scope |
| K+N vs K | Draw/dead-position results frozen | None within proved scope |
| **K+R vs K (current)** | Dead/live; WDL for every position (EC-T0048); exact distance regions through 12 plies, partial 13/14 (EC-T0049); history/clock results beyond parity | Exact DTZ50 (= distance to mate) for all won positions; fresh-position bridge; parity interface |
| K+Q vs K | Not started | Full class proof + Lean |
| K+P vs K | Not started | Full class proof + Lean |
| Four-piece classes | Not started | All material classes and positions |
| Five-piece classes | Not started | All material classes and positions |
| Six-piece classes | Not started | All material classes and positions |
| Seven-piece classes | Not started | All material classes and positions |

KRK work is **not closed**: 49 frozen bundles are not 49 solved material classes. The class-level programme goes KRK → KQK → KPK → systematically larger material classes, subject to owner selection. Piece count includes both kings.

## What counts as completion
1. **Dead/live:** Whether checkmate remains legally possible, including capture/dead-position boundaries.
2. **Outcome:** Correct WDL50 for every fresh legal position of the class.
3. **Strategic justification:** General mathematical proof accounting for all defences and legal alternatives; never merely an oracle or enumeration.
4. **Distance:** Exact DTZ50 for every decisive fresh position. A loose upper bound is not an exact distance certificate.

A partial KRK family can be frozen while the overall class stays open. Stop after KRK before advancing to KQK without owner direction. For KRK, see [KRK status](KRK_COMPLETION.md).

Only edit this file when coverage or the intended class order materially changes. **No session-by-session appendices, repeated progress tables or administrative milestones.**
