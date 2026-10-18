# S017 — EC-C008 cooperative mating route (Gate L attempt; not passed) + objective documentation

**Date:** 2026-10-18
**Type:** Theorem session (local mathematics; no Lean).
**Base revision:** `eda2484` (`main`, S016).
**Result:** the S017 commit on `main` (not self-cited).

## Changes
- `scripts/krk_route.py`, `tests/test_krk_route.py` (new): a deterministic strategy simulator for the explicit route. Every move is checked against the independent generator.
- `proofs/EC-C008_KRK_LIVE.md`, `audits/EC-C008_KRK_LIVE.md` (new): the partial proof and its audit.
- **Owner request (mid-session):** the overarching objective is now explicit as *proof-based tablebase equivalence*. The aim is to know what Syzygy knows, by general theorems formalised in Lean, never by lookup. Changes:
  - `docs/CHARTER.md`: mission and hard boundaries;
  - `README.md`: introduction;
  - `docs/ROADMAP.md`: a new "North star" section. It defines layers L1 (dead/live), L2 (outcome, i.e. WDL), L3 (strategy) and L4 (distance, i.e. DTM/DTZ), and gives a coverage table for the 3-piece classes.
- `research/CANDIDATES.md` (EC-C008 row), `README.md` status.
- `NEXT_SESSION.md`: S018 (remedial: close G-P1 and G-P2) installed.

## Findings, separated
- **Proved (paper):**
  - EC-C008(a) ⇒ (b);
  - normalisation by reflections;
  - Lemma M (the mate pattern);
  - Lemma E (escort, parity and mate from `L = S − (0,2)`, with the rook on rank 8, files f–h);
  - Lemma W (the walk to `T` when `L` is in `T`'s component of `F`).
- **Computationally tested (supplement):** the explicit route reaches checkmate from all 175,168 strong-to-move states; the longest route is 31 plies. The Lemma W hypothesis after P1 fails in 10,752 states.
- **Conjectured:** EC-C008 (unchanged).
- **Gaps:**
  - G-P1: the rook-relocation lemma has no hand proof;
  - G-P2: the route as specified does not always leave the lone king connected to `T`, so the route needs repair.

## Checks actually run
- `python scripts/krk_route.py`: the route reaches mate in 175,168/175,168 states (7 min 15 s; output verbatim in the audit).
- `python -m unittest tests.test_krk_route`: 4 tests OK.
- `python -m unittest discover -s tests` and `python scripts/validate_ledger.py`: results in the session ledger row.
- Lean: not run (`formal/` unchanged).

## Status and ledger effect
EC-C008 stays `PROPOSED`. Ledger unchanged; 6 frozen theorems.

## Installed next session
See `NEXT_SESSION.md` at this commit (S018, remedial EC-C008: repair the route so that Lemma W's hypothesis always holds after P1; hand-prove the rook-relocation lemma by class; hostile audit; Gate L only if no gap remains).
