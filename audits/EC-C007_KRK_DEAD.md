# Audit — EC-C007 dead K+R vs K positions (S014)

**Subject:** [proofs/EC-C007_KRK_DEAD.md](../proofs/EC-C007_KRK_DEAD.md). **Auditor:** same session (S014); no independent second reader yet.
**Method:** each claim was attacked by hand and cross-checked with `scripts/krk_diagnostic.py`. That script walks rook rays square by square and computes cooperative reachability over its own move graph. It is supplementary, not a tablebase.

| # | Attack | Outcome |
|---|---|---|
| 1 | **Zero-length path:** `q` itself could be checkmate. | Excluded by the hypothesis `¬MatedK q`. The 216 checkmates are not dead, and the diagnostic agrees. |
| 2 | **"Every legal move captures" read vacuously** (no legal move at all). | Intended: a stalemate is dead (no reachable mate). 68 stalemates per orientation, all counted dead by the fixpoint. |
| 3 | **Can a lone-king move do something other than move or capture the rook?** Castling (needs a `σ̄` rook), en passant and promotion (need pawns) are impossible; capturing the strong king is forbidden (1.4.1, `targetOK`). | No gap. |
| 4 | **After the capture, is K vs K really dead?** It is produced by a legal move from `q`, so EC-T0003 (`dead_of_legal_into_KK`) applies with no admissibility re-derivation. | No gap. |
| 5 | **Head decomposition of `ReachK`.** `ReachK` is tail-inductive; D1 needs "first move, then the rest". Proved by induction on the path (`reachK_head`, planned). | Standard. |
| 6 | **Flags.** Castling rights or an en-passant target left on `q`: neither enables a lone-king move. On successors they are irrelevant to EC-T0003, which allows any flags. | No gap. |
| 7 | **Both orientations.** The statement is parametric in `σ`. The diagnostic gives identical counts for White and for Black as the strong side. | Holds. |
| 8 | **Strong side to move.** Not covered by EC-C007 (`q.turn = σ̄` is a hypothesis). The diagnostic finds no dead strong-to-move state, which is evidence for EC-C008(a) only. | Out of scope; recorded as EC-C008. |
| 9 | **Protected rook.** A protected rook cannot be taken (3.9.2). If the lone king has no other move, it is stalemate (covered) or checkmate (excluded). | Test `test_protected_rook_is_not_capturable`. |
| 10 | **X-ray along the rook's line after the king steps.** Relevant to which moves are legal, not to the proof. The diagnostic's independent generator handles it (test `test_xray_after_king_step`). | n/a to the logic. |
| 11 | **Non-vacuity.** Ka1/Rb2/Kh8 with Black to move: the only legal move is Kxb2 (test `test_forced_rook_capture`); a predecessor is Rb3–b2. | Satisfiable. |
| 12 | **Is the characterisation sharp?** Compared state by state with the fixpoint: 0 mismatches, both orientations. | Evidence for EC-C008; not used by EC-C007. |
| 13 | **Mutation.** Bishop in place of the rook: 417,068 mismatches. The comparison has teeth. | Detected. |

## Diagnostic output (verbatim, `python scripts/krk_diagnostic.py`)
```
== K+R vs K, strong side W ==
legal_krk_states: 399112
kk_states: 7224
checkmates: 216
stalemates: 68
checks_of_lone_king: 48776
forced_rook_captures: 412
dead_states: 480
dead_strong_to_move: 0
dead_weak_to_move: 480
mismatches: 0
kk_live: 0
seconds: 45.9
== K+R vs K, strong side B ==
legal_krk_states: 399112
kk_states: 7224
checkmates: 216
stalemates: 68
checks_of_lone_king: 48776
forced_rook_captures: 412
dead_states: 480
dead_strong_to_move: 0
dead_weak_to_move: 480
mismatches: 0
kk_live: 0
seconds: 51.7
== mutation: rook replaced by a bishop (strong side W) ==
mismatches: 417068  dead_states: 417228  checkmates: 0
KRK DIAGNOSTIC PASSED (supplementary evidence, not a proof)
```

**Verdict:** EC-C007 passes Gate L (same-session caveat). EC-C008 stays `PROPOSED`. Its gap is the explicit cooperative mating route of proof §6.
