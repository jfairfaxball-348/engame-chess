# Mathematical roadmap

This is a **material-class roadmap**, not a session log. [The live work note](../NEXT_SESSION.md) carries the immediate problem; [theorem ledger](../theorems/LEDGER.csv) is authoritative for frozen proof scope. Existing numbered session records are historical only.

## Overall ambition
- **Immediate programme:** prove the [guaranteed outcome](CHARTER.md#parity-target-hard-boundary-owner-2026-10-29) (WDL50, with a move bound) of every position in each material class, without Syzygy or other lookup tables. Exact distances are optional. Nothing more is required before moving on.
- **Master operational milestone:** parity with seven-piece lookup-table knowledge via general, Lean-formalised mathematics, NOT via replayed tables or enumerations.
- **Distant aspiration, unproved:** ultra-weakly solve standard chess by proving its initial-position value is a draw; no playable engine or move recipe is required.

## Class coverage (not percentages)

| Material class | Verified coverage | Outstanding |
|---|---|---|
| K vs K | Draw/dead-position results frozen | None within proved scope |
| K+B vs K | Draw/dead-position results frozen | None within proved scope |
| K+N vs K | Draw/dead-position results frozen | None within proved scope |
| **K+R vs K** | **Complete (outcome target).** Dead/live; WDL for every position with 97/98-ply bound (EC-T0019, EC-T0048); exact distances through 13/14 plies (EC-T0049) | Optional only: exact distance to mate beyond 14 plies |
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
4. **Distance:** A proved move bound sufficient for the 50-move rule. Exact DTZ50 is optional.

A partial KRK family can be frozen while the overall class stays open. Stop after KRK before advancing to KQK without owner direction. For KRK, see [KRK status](KRK_COMPLETION.md).

Only edit this file when coverage or the intended class order materially changes. **No session-by-session appendices, repeated progress tables or administrative milestones.**
