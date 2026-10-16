# Audit — EC-C001 (K vs K dead position)

**Audited artefact:** [proofs/EC-C001_KK.md](../proofs/EC-C001_KK.md), together with the repaired model [docs/FOUNDATIONS.md](../docs/FOUNDATIONS.md).
**Session:** S001, 2026-10-16. Base revision before S001 edits: `848524bd7f9fe575eaf3e4f165d0dba176bf4210`.
**Auditor stance:** adversarial; the goal was to break the proof, not to confirm it. Same-session audit (not an independent human reviewer) — recorded as a limitation in §5.
**Outcome:** no surviving gap. Gate L passed. EC-C001 → `LOCAL_VERIFIED`.

## 1. Rule-source check
- FIDE handbook page `E012023` fetched 2026-10-16 (WebFetch returned HTTP 503; `curl` succeeded, 186 411 bytes, SHA-256 `c5b1692a0614d4bd93fe9238287b9ab7d1f47320934d5df3be113523906c476f`). Page header: "Approved by the FIDE General Assembly on 07/08/2022 / Applied from 01/01/2023". All quoted articles in the proof were copied from that text.
- **Finding (repaired):** the S000 model implicitly took "a king may not move to an attacked square" as part of 3.8. The 2023 text of 3.8.1 contains no such clause. The prohibition is now derived from 3.9.2 + 3.1.2/3.1.3 (proof L3a). Conclusion unchanged; derivation corrected.

## 2. Attempted falsifications

| # | Attack | How checked | Outcome |
|---|---|---|---|
| 1 | Corners: king on a1 has only 3 neighbours; could attack/move sets differ at the boundary? | L1 defines `N` on-board only; script compares offset-generated attacks with `d∞=1` for all 64×64 square pairs; unit test `test_corner_cases` (Ka1 vs Kc1, White to move: only Ka2 legal) | 0 mismatches; no gap |
| 2 | Edges (non-corner) | Same exhaustive pair comparison and closure check | 0 mismatches |
| 3 | Both sides to move | S000 `StepKK` never tied the moving king to `t` — **gap found and repaired** (FOUNDATIONS, `LegalKK` condition uses `K_t`). Script checks the moved king is always the side to move's and the turn flips | 0 violations in 44 352 legal moves |
| 4 | Zero-length path | L4 base case `n=0` stated explicitly; requires `Admissible(p)` itself, supplied by L0 for arisen positions | Covered |
| 5 | King capture | Excluded twice: 1.4.1 (condition ii) and `d∞(s,K_t̄) ≥ 2` (condition iii). Also unreachable: capture needs adjacency, which admissibility forbids | No gap |
| 6 | Adjacent kings as a starting state | Not admissible; L0 shows it cannot have arisen (it would leave the last mover in check). Script: all 840 adjacent configurations have **both** kings in check | Confirms L0/L2′ |
| 7 | Castling | Requires a rook (3.8.2); none present. Even if mis-modelled, castling never captures, so L1 unaffected | No gap |
| 8 | Mate quantifier: ∃ vs ∀; forced vs possible | `Dead` is defined as ¬∃ path to mate; L6 proves the universal statement over all paths, including cooperative play. The weaker "no forced mate" is never used | No gap |
| 9 | Attack relation vs movement relation mismatch | Attack = capture-capable move (3.1.2) ignoring self-check (3.1.3); kings' capture-capable moves = 3.8.1 moves = `N`. L1 proves equality; script confirms exhaustively | No gap |
| 10 | Circularity with dead-position stopping rule | `Reach` uses no stopping rule; legality (3.10.1) depends only on Articles 3.1–3.9, so the counterfactual graph is well defined after the game ended | No gap; explanation added to proof §4 and FOUNDATIONS |
| 11 | Arisen vs Admissible conflated | Now separate predicates; only `Arisen ⇒ Admissible` (L0) is claimed; the converse is neither claimed nor needed | No gap |
| 12 | L0 relies on history beyond the last move? | Proof uses only that the last move was legal (3.9.2) and symmetry of L2′. Works for the first KK position after the capture of the last other piece | No gap |
| 13 | Checkmate needs "no legal move" — must we prove moves exist? | No: check is necessary for checkmate; L5 refutes check. R1 additionally proves a legal move always exists (script: 0 configurations without a move, 0 stalemates) | No gap |
| 14 | Competing terminations by the producing move (5.1.1 mate, 5.2.1 stalemate) | Mate impossible (L2); stalemate impossible (R1). 5.2.2 applies cleanly | No gap |
| 15 | Material invariance | No capture is possible in a KK legal move; material stays {K_W, K_B} along every path (L3) | No gap |
| 16 | Misreading "adjoining" (e.g. orthogonal only) | Recorded as assumption A1. Note: under any *smaller* neighbourhood the argument is unchanged in structure (L1 would use that neighbourhood for both attack and move) | Residual assumption, standard reading |
| 17 | Hidden use of tablebases/engines | None. Script is a self-contained generator using only king offsets and bounds | Compliant |

## 3. Diagnostic run (supplementary, not proof)
Command: `python3 scripts/kk_diagnostic.py` (Python 3, at base revision plus S001 working-tree files). Output:

```
states_total: 8192
admissible_states: 7224
admissible_placements: 3612
attack_eq_dinf1_violations: 0
admissible_in_check: 0
legal_moves_total: 44352
step_closure_violations: 0
turn_flip_violations: 0
wrong_king_or_distance_violations: 0
admissible_states_without_legal_move: 0
checkmates: 0
stalemates: 0
bfs_reached_states: 7224
bfs_bad_states: 0
adjacent_states: 840
adjacent_states_not_double_check: 0
DIAGNOSTIC CONSISTENT with EC-C001 lemmas (supplementary evidence, not a proof)
```

Sanity of counts by hand: ordered distinct placements 64·63 = 4032; ordered adjacent pairs = 2·(2·7·8 + 2·7·7) = 420; 4032 − 420 = 3612 admissible placements, ×2 sides = 7224; adjacent configurations 420×2 = 840. ✔

Also run: `python3 -m unittest discover -s tests -v` → 9 tests OK (3 new KK diagnostic tests, 6 existing ledger tests); `python3 scripts/validate_ledger.py` → `LEDGER VALID: 0 frozen theorem(s)`.

## 4. Repairs made during audit
1. Side-to-move bound into the step relation (row 3).
2. Non-adjacency derived from 3.9.2 instead of an absent 3.8.1 clause (§1).
3. Explicit `Arisen`, `Checkmate`, `Stalemate`, counterfactual graph in FOUNDATIONS.

## 5. Remaining assumptions and limitations
- A1 (meaning of "adjoining").
- Rule edition: FIDE 2023 as retrieved 2026-10-16.
- Scope: positions reached from the initial position by legal moves; set-up positions covered only via the admissible-form statement.
- Audit performed in the same session as the proof by the same agent; an independent second read is recommended before or during S002. Lean formalisation (Gate F) is the planned independent check.
- No Lean code exists; no formal check has been run.
