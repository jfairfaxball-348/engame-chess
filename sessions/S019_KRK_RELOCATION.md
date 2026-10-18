# S019 — EC-C008 relocation lemma (G-P1) proved; EC-C008 LOCAL_VERIFIED (Gate L)

**Date:** 2026-10-18
**Type:** Theorem session (local mathematics; no Lean).
**Base revision:** `38dc979` (`main`, S018).
**Result:** the S019 commit on `main` (not self-cited).

## Changes
- `scripts/krk_route.py` → **route v3**. P1 is now an explicit rule:
  - home;
  - direct (from the h-file, or from rank 8 when not blocked);
  - HV, unless the path is blocked or the single exception applies;
  - otherwise file-shift (FS), with `y′` = rank 1 if `L` is on rank 3 or higher, else rank 8, or rank 5 if the rook is on rank 8.

  Every state is classified into one branch, and unclassified states raise an error.
- `proofs/EC-C008_KRK_LIVE.md` §4b (new):
  - **Lemma RL-h**: with the rook on the h-file, the lone king always has a non-capturing reply or is mated, except the stalemate `(c8, h7, a8)`;
  - **Lemma RL-f**: the reply after a file-shift move, when `rx < sx`;
  - **Lemma P1**: relocation, branch by branch;
  - the theorem.

  Status set to `LOCAL_VERIFIED`. The route description and evidence are updated to v3.
- `audits/EC-C008_KRK_LIVE.md`: rewritten (18 attacks; verdict: Gate L passes, same-agent caveat).
- `research/CANDIDATES.md`, `README.md`, `docs/ROADMAP.md` (L1 for K+R vs K: proved on paper).
- `NEXT_SESSION.md`: S020 (Lean formalisation, part 1) installed.

## Findings, separated
- **Proved (paper, Gate L):** EC-C008. A K+R vs K position produced by a legal move with the strong side to move is never dead. Hence, together with EC-T0006, a legal K+R vs K position is dead **iff** the lone king is to move, it is not checkmate, and every legal move captures the rook (or it is stalemate). This completes layer L1 for K+R vs K on paper.
- **Computationally tested (supplement):**
  - route v3 mates from all 175,168 strong-to-move states (longest route 31 plies); branch counts are in the audit;
  - RL-h: 1 exception, as stated;
  - RL-f: 9,279 instances, 0 exceptions.
- **Conjectured:** none new.
- **Not done:** the Lean formalisation (S020+); an independent reader.

## Checks actually run
- `python scripts/krk_route.py` (v3): 175,168/175,168 (4 min 14 s).
- RL-h and RL-f brute force: as above.
- `python -m unittest tests.test_krk_route`: OK. Full suite and ledger validation: see the session ledger row.
- Lean: not run (`formal/` unchanged).

## Status and ledger effect
EC-C008: `PROPOSED → LOCAL_VERIFIED`. Ledger unchanged; 6 frozen theorems.

## Installed next session
See `NEXT_SESSION.md` at this commit (S020: Lean infrastructure for K+R vs K over the kernel, plus the end-game half: Lemmas M, E, C, W and S; multi-session plan, no freeze).
