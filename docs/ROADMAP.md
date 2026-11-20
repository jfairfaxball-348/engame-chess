# Mathematical roadmap

This is a **material-class roadmap**, not a session log. [The live work note](../NEXT_SESSION.md) carries the immediate problem; [theorem ledger](../theorems/LEDGER.csv) is authoritative for frozen proof scope. Existing numbered session records are historical only.

## Overall ambition
- **Immediate programme:** prove the [guaranteed outcome](CHARTER.md#parity-target-hard-boundary-owner-2026-10-29) (WDL50, with a sufficient move bound) of every fresh position in each material class, without Syzygy or other lookup tables.
- **Master operational milestone: Endgame Outcome Parity through seven pieces** ([charter](CHARTER.md)): the correct game-theoretic outcome of every legal position in each class, with dead/live, actual strategies, rule-aware draw treatment and sufficient bounds, via general Lean-formalised mathematics, NOT via replayed tables or enumerations. This is outcome parity, not full tablebase feature parity.
- **DTM and DTZ are not objectives** at any stage, including seven pieces. Sufficient bounds (e.g. mate within 98 plies, or a forced reset in time) remain required; optimal distances do not. Frozen exact-distance results are kept.
- **Distant aspiration, unproved:** ultra-weakly solve standard chess by proving its initial-position value is a draw; no playable engine or move recipe is required.

## Ordered sequence (owner, 2026-11-20)
1. **Finish KPK** (fresh-root WDL50, dead/live, sufficient progress bounds) — active now, scope unchanged ([plan](KPK_PLAN.md)).
2. **Verify and freeze** the complete KPK results.
3. **Begin Three-Piece Full Rules Closure** (below).
4. **Complete and freeze** that milestone.
5. **Then four-piece material classes**, subject to owner selection.

Three-Piece Full Rules Closure must not begin until step 2 is done.

## Class coverage (not percentages)

| Material class | Verified coverage | Outstanding |
|---|---|---|
| K vs K | Draw/dead-position results frozen | Full-rules closure (step 3) |
| K+B vs K | Draw/dead-position results frozen | Full-rules closure (step 3) |
| K+N vs K | Draw/dead-position results frozen | Full-rules closure (step 3) |
| **K+R vs K** | **Complete (fresh-root target).** Dead/live; WDL for every position with 97/98-ply bound (EC-T0019, EC-T0048); exact distances through 13/14 plies (EC-T0049, kept, not an objective) | Full-rules closure (step 3) |
| **K+Q vs K** | **Complete (fresh-root target).** Every fresh legal position, both colours/turns; actual winning/holding, dead/live, 97/98-ply bounds (EC-T0050) | Full-rules closure (step 3) |
| K+P vs K | **In progress.** Ranks five to seven classified for every non-rook pawn, both turns; rook-pawn corner fortress; see [partial proof](../proofs/KPK_WDL50.md) | Ranks two to four, rook pawn outside the fortress, general dead/live; then freeze; then full-rules closure |
| Four-piece classes | Not started | All material classes and positions |
| Five-piece classes | Not started | All material classes and positions |
| Six-piece classes | Not started | All material classes and positions |
| Seven-piece classes | Not started | All material classes and positions |

Frozen bundles are not counts of solved material classes. Piece count includes both kings.

## What counts as fresh-root class completion
1. **Dead/live:** Whether checkmate remains legally possible, including capture/dead-position boundaries.
2. **Outcome:** Correct WDL50 for every fresh legal position of the class.
3. **Strategic justification:** General mathematical proof accounting for all defences and legal alternatives; never merely an oracle or enumeration.
4. **Distance:** A proved move bound sufficient for the 50-move rule. Exact DTM/DTZ is not an objective.

## Next milestone: Three-Piece Full Rules Closure

**Scope:** KvK, KBK, KNK, KRK, KQK, KPK; both colours, both sides to move. Strengthen the fresh-root results into outcome theorems over **all admissible, legally reachable game histories** in these classes. Arbitrary legally possible incoming halfmove clocks and repetition histories are **mandatory**. The formal state keeps whatever history the rules genuinely require; the board alone may not determine the result.

**Entry versus within-class history (the crucial distinction).** Entering a new material class resets the clock and isolates earlier epochs from repetition. It does *not* erase history inside the class: a legally reached KRK position may carry clock 80 and earlier repetitions of the current epoch, and must be classified as such, not referred back to a clean first-arrival state. Part A is the foundation, not the milestone; it does not by itself close Part C.

- **A — Material-Class Entry Theorem.** An exact material inventory (colour and piece type) with a monotone material measure. From the actual legal-move kernel (not by definition), prove: an inventory cannot reappear once left; entry into a new class follows a capture or pawn move, so the clock resets; earlier epochs contain no position identical to one in the new epoch. Cover promotion, en passant and other exceptional cases.
- **B — History and repetition.** A reusable epoch-history interface. Exclude earlier epochs from repetition counts where Part A justifies it; within the current epoch retain every relevant repetition. Cover threefold and 50-move claims (including intended-move claims), automatic fivefold and 75-move draws, clocks inherited within the epoch, checkmate precedence, stalemate, dead positions, and position identity (side to move, castling rights, en-passant availability). Resetting the clock is not erasing history.
- **C — History-aware classification.** For each class, a necessary-and-sufficient criterion `Outcome(position, clock, relevant history)` over the stated domain, separating (1) forced wins still available, (2) states where a valid claim or holding strategy prevents the win, (3) terminal or dead states. Keep the fresh-root cursed-win/blessed-loss distinction separate from the outcome of a specific history-aware state. A bound that no longer fits the remaining clock does **not** by itself prove a draw: the converse needs a holding argument or another complete criterion. Never assume a fresh-root winning strategy still wins at a positive clock. No recursive minimax definition, finite-state search or position catalogue in place of an explicit characterisation. Reuse KRK/KQK geometric results and 97/98-ply bounds, decreasing strategy ranks, frozen raw-history and clock-banded results, and KPK pawn-progress/promotion continuation.
- **D — All classes below four pieces.** For KPK, treat pawn advance, promotion, resetting moves, histories across promotion, captures into KK and transitions into proved classes. Resolve the KRK distinction between legal-arrival histories and arbitrary locally legal boards insofar as it affects the domain. Reuse frozen results; do not rewrite frozen mathematics for uniformity.
- **E — Rules fidelity.** State the exact rules domain. Audit the FIDE-to-Lean bridge for these mechanisms; extend it with new modules and proved compatibility lemmas rather than redefining frozen results. Account for surviving castling rights in genuine histories. Separate proved rules-model results from unverified correspondence with the external FIDE text.

**Completion requires:** Lean-verified Parts A and B; complete history-aware classifications for every covered class over the stated legally reachable domain; proved progress guarantees for wins; genuine holding or rule-based justification for draws; every legal opponent response, including draw claims, handled; passing Lean builds and permitted-axiom checks; freeze under the existing [proof protocol](PROOF_PROTOCOL.md). If a clock/history boundary remains unresolved, keep that theorem open and name the exact obstacle.

Partial families can be frozen without closing a class. Do not begin a new class or milestone without owner selection. See [KRK status](KRK_COMPLETION.md) and [KQK status](KQK_COMPLETION.md).

Only edit this file when coverage or the intended class order materially changes. **No session-by-session appendices, repeated progress tables or administrative milestones.**
