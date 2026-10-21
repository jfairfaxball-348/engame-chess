# Mathematical roadmap

This is a **material-class roadmap**, not a session log. [The live work note](../NEXT_SESSION.md) carries the immediate problem; [theorem ledger](../theorems/LEDGER.csv) is authoritative for frozen proof scope. Existing numbered session records are historical only.

## Overall ambition
- **Immediate programme:** derive complete proof-based endgame knowledge (dead/live, WDL outcomes, winning/holding criteria where needed, and correct distance/50-move semantics) for each material class without using Syzygy or other lookup tables.
- **Master operational milestone:** parity with seven-piece lookup-table knowledge via general, Lean-formalised mathematics, NOT via replayed tables or enumerations.
- **Distant aspiration, unproved:** ultra-weakly solve standard chess by proving its initial-position value is a draw; no playable engine or move recipe is required.

## Class coverage (not percentages)

| Material class | Verified coverage | Outstanding |
|---|---|---|
| K vs K | Draw/dead-position results frozen | None within proved scope |
| K+B vs K | Draw/dead-position results frozen | None within proved scope |
| K+N vs K | Draw/dead-position results frozen | None within proved scope |
| **K+R vs K (current)** | Clock-free dead/live and forcing; partial history/clock outcomes; EC-T0048 clock0 both-turn criterion and wall93/arrival97/forcing98, frozen | Complete positive-clock and incoming-history outcomes, full FIDE correspondence, exact WDL/DTZ distances |
| K+Q vs K | Not started | Full class proof + Lean |
| K+P vs K | Not started | Full class proof + Lean |
| Four-piece classes | Not started | All material classes and positions |
| Five-piece classes | Not started | All material classes and positions |
| Six-piece classes | Not started | All material classes and positions |
| Seven-piece classes | Not started | All material classes and positions |

KRK work is **not closed**: 48 frozen bundles are not 48 solved material classes. The class-level programme goes KRK → KQK → KPK → systematically larger material classes, subject to owner selection. Piece count includes both kings.

## What counts as completion
1. **Dead/live:** Whether checkmate remains legally possible, including capture/dead-position boundaries.
2. **Outcome:** Correct win/draw/loss on the entire stated domain with the relevant rules and history.
3. **Strategic justification:** General mathematical proof accounting for all defences and legal alternatives; never merely an oracle or enumeration.
4. **Distance:** Exact appropriate DTM/DTZ and the 50-move effects when parity is claimed. A loose upper bound is not an exact distance certificate.

A partial KRK family can be frozen while the overall class stays open. Stop after KRK before advancing to KQK without owner direction. For the KRK direct closure obstacles and current mathematics, see [KRK completion](KRK_COMPLETION.md) and [positive-clock frontier](../research/KRK_POSITIVE_CLOCK_FRONTIER.md).

Only edit this file when coverage or the intended class order materially changes. **No session-by-session appendices, repeated progress tables or administrative milestones.**
