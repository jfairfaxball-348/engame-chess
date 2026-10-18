# Audit — EC-C003 K+N vs K local proof (S011)

**Subject:** [proofs/EC-C003_KNK.md](../proofs/EC-C003_KNK.md).
**Auditor:** same session as the proof (S011). No independent second reader yet.
**Method:** each claim was attacked by hand, then cross-checked against an independently coded exhaustive enumeration, `scripts/knk_diagnostic.py`. The enumeration lists the eight knight offsets explicitly and does **not** use the colour argument. A separate routine, `check_geometry()`, tests every geometric claim of N1/N2 over the whole board. Supplementary only: no tablebase, no external data.

## 1. Attempted falsifications

| # | Attack | Outcome |
|---|---|---|
| 1 | **The prompt's colour claim** ("diagonal neighbours of a checked king are never attacked; orthogonal ones may be"). | **False, and reversed.** Counterexample: Nc4 checks Kb2 and attacks a3, a diagonal neighbour. Diagnostic: 288 diagonal incidences, 0 orthogonal. Test `test_checking_knight_can_cover_a_diagonal_neighbour`. The proof uses the corrected N1(c); see proof §0. |
| 2 | **Corners.** Lone K a8 (or any corner). The strong king can cover the one diagonal neighbour (Kb6 covers b7) without being adjacent. Can king + knight cover a7 and b8? The knight checking a8 (on b6 or c7) attacks neither orthogonal neighbour (N1(c)); covering both by the king forces `d∞(K,a8) ≤ 1` (N2 step 6). | Holds. Test `test_corner_check_has_orthogonal_escapes` (Ka8, Nb6+, Kc6: escapes exactly a7, b8). |
| 3 | **Edges.** `k` on an edge but not a corner: `ε` or `δ` points inward, `h`/`v` on board. Checked for all 64 squares. | `h_or_v_off_board = 0`. |
| 4 | **King covering both `h` and `v` from distance ≥ 2.** | Impossible by step 6; exhaustively `king_covers_both_h_and_v = 0` (all `k`, `K`). |
| 5 | **Knight on the edge / in the corner** (fewer targets). Fewer targets only remove attacks; N1 is about the targets that exist. | No gap. Exhaustive run covers all knight squares. |
| 6 | **Both orientations.** The proof is for abstract `σ`; the kernel `IsKNK` takes `σ` as a parameter. | 999,936 placements across both orientations, 0 mates. |
| 7 | **Both sides to move.** N4 handles `σ` to move (N0(c)) and `ω` to move (N2) separately. | `strong_side_in_check = 0`. |
| 8 | **Capture branch.** The `ω` king takes an unprotected knight; the result is K vs K produced by a legal move, so EC-T0003 applies directly (no admissibility re-derivation needed). A protected knight cannot be taken (3.9.2). | 44,352 captures, all into kings-apart K vs K. Test `test_unprotected_knight_capture_gives_kk`. |
| 9 | **Escape by capturing the checker.** Impossible: a checking knight is at `d∞ = 2` (N1(b)). | `lone_king_escapes_by_capture = 0`; `checking_knight_adjacent = 0`. |
| 10 | **Double check.** Impossible: the strong king never attacks `k` (N0(b)), so the knight is the only possible checker. | `double_checks = 0`. |
| 11 | **Discovered effects of the king's step.** Knight and king attacks ignore occupancy (`attacksFrom` has no `pathClear` for them), so vacating `k` cannot open a line. | No gap. |
| 12 | **Zero-length path.** `ReachK q q`: `q` itself must not be mate. N4 applies to `C(q)`. | Holds. |
| 13 | **Arisen form.** `initial` is not K+N vs K, so the path has a last legal move. | Mirrors `Rules.initial_not_KBK`; to be proved in S012. |
| 14 | **Flags** (castling rights / en-passant target left over from the predecessor). Neither castling (rook required) nor en passant (pawn required) is possible; the argument never reads flags. | No gap; `deadK_normFlags_iff` is available. |
| 15 | **Illegal predecessors / illegal states** (side not to move in check). Excluded by the hypothesis `Legal p q` (N0(a)); the diagnostic filters them and checks closure (`closure_violations = 0`). | Holds. |
| 16 | **Quantifier error** (forced vs possible mate). `DeadK` is ¬∃ path to mate, over cooperative play; N4 is a universal closure statement. | Correct. |
| 17 | **Stalemate confusion.** 80 stalemates exist (e.g. Ka8 / Kb6 + Nc6). Not checkmate. | Test `test_known_stalemate`. |
| 18 | **Art. 3.6 encoding.** Is `knightGeom` exactly "nearest squares not on the same rank, file or diagonal"? Checked square by square (Euclidean nearest among off-line squares). | `knight_targets_not_8_offsets = 0`. |
| 19 | **Symmetries.** N2 uses none (uniform `ε, δ` construction). Only the unused remark N1(d) uses the 8 symmetries of the square, which preserve both offset sets; N1(d) is also checked exhaustively (`knight_attacks_two_neighbours_of_checked_king = 0`). | No gap. |
| 20 | **Diagnostic sensitivity (mutation).** Give the knight an extra king step (one orientation). | **172 checkmates** detected (e.g. Ka8, "knight" on b7 protected by Kb6). Test `test_mutant_mate_detected`. The zero count is meaningful. |

## 2. Diagnostic output (verbatim, `python scripts/knk_diagnostic.py`)
```
== geometry (N1/N2 claims) ==
knight_move_same_colour: 0
knight_targets_not_8_offsets: 0
knight_attacks_orth_neighbour_of_checked_king: 0
knight_attacks_two_neighbours_of_checked_king: 0
checking_knight_adjacent: 0
two_knight_targets_orth_adjacent: 0
king_covers_both_h_and_v: 0
h_or_v_off_board: 0
knight_attacks_diag_neighbour_of_checked_king: 288
two_knight_targets_diag_adjacent: 144
== exhaustive K+N vs K ==
placements: 999936
legal_states: 858880
checks_of_lone_king: 36896
checkmates: 0
stalemates: 80
legal_moves: 7086864
captures_to_kk: 44352
closure_violations: 0
lone_king_in_check_without_move: 0
strong_side_in_check: 0
checked_king_without_orthogonal_escape: 0
double_checks: 0
lone_king_escapes_by_capture: 0
seconds: 44.1
== mutation: knight with an extra king step, one orientation ==
checkmates: 172
lone_king_in_check_without_move: 172
KNK DIAGNOSTIC PASSED (supplementary evidence, not a proof)
```

## 3. Residual assumptions
A1; the kernel's encoding of Article 3 (human review of `docs/RULES_KERNEL.md` still open); the FIDE 2023 text as retrieved; dependence on the frozen EC-T0003 for the capture branch. **No gap found.** Verdict: Gate L passes, subject to the same-session caveat.
