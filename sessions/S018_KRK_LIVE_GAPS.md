# S018 — EC-C008 remedial: route v2, gap G-P2 closed (Gate L not yet passed)

**Date:** 2026-10-18
**Type:** Theorem session (local mathematics; no Lean).
**Base revision:** `5b34a82` (`main`, S017).
**Result:** the S018 commit on `main` (not self-cited).

## Changes
- `scripts/krk_route.py` → **route v2**:
  - P1 relocates the rook to exactly h8 (routes: direct / HV / VH / detour);
  - P2 settles the lone king by four cases and walks with one of two tempo pairs (`G`: h8↔g8, `H`: h8↔h7) inside a region;
  - the Lemma S case split and the Lemma W connectivity are **hard checks**;
  - the escort and mate use the same pair.
- `proofs/EC-C008_KRK_LIVE.md`: route v2 written up. New **Lemma C** (region connectivity: a rectangle minus a smaller sub-rectangle is connected) and **Lemma S** (settling after P1, four exhaustive cases). Lemma W is generalised to both pairs, and Lemma E adapted. Gap list reduced to G-P1.
- `audits/EC-C008_KRK_LIVE.md`: updated (13 attacks; G-P2 closed).
- `NEXT_SESSION.md`: S019 (prove G-P1) installed.

## Findings, separated
- **Proved (paper):** EC-C008 reduces to the rook-relocation lemma G-P1. Everything after the rook reaches h8 is proved (Lemmas S, C, W, E, M), including the 10,752 states where route v1 failed its invariant.
- **Computationally tested (supplement):** route v2 reaches mate from all 175,168 strong-to-move states, with hard invariant checks; the longest route is 31 plies. Counts are in the audit.
- **Conjectured:** EC-C008 (pending G-P1).
- **Gap:** G-P1 (relocation: legality of the routes, and the lone king's non-capturing replies).

## Checks actually run
- `python scripts/krk_route.py` (route v2): mate in 175,168/175,168 (5 min 25 s; output verbatim in the audit).
- `python -m unittest tests.test_krk_route`: OK.
- Full test suite and ledger validation: see the session ledger row.
- Lean: not run (`formal/` unchanged).

## Status and ledger effect
EC-C008 stays `PROPOSED` (one gap). Ledger unchanged; 6 frozen theorems.

## Installed next session
See `NEXT_SESSION.md` at this commit (S019: hand proof of the relocation lemma G-P1 by class of rook position, via a reply lemma on the lone king's free neighbours; Gate L for EC-C008 if no gap remains).
