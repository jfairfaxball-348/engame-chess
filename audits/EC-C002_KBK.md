# Audit — EC-C002 K+B vs K local proof (S004)

**Subject:** [proofs/EC-C002_KBK.md](../proofs/EC-C002_KBK.md).
**Auditor:** same session as the proof (S004). No independent second reader yet.
**Method:** each claim was attacked by hand, then cross-checked against an independently coded exhaustive enumeration, `scripts/kbk_diagnostic.py`. The enumeration walks bishop rays square by square and does **not** use the colour argument. It is supplementary only; it is not a tablebase and reads no external data.

## 1. Attempted falsifications

| # | Attack | Outcome |
|---|---|---|
| 1 | **Corner.** The `ω` king on a1, checked along the long diagonal (Bh8 … b2 clear). Candidates `h = b1`, `v = a2`. To cover both, the `σ` king must be within distance 1 of both, which forces it into {a1, a2, b1, b2}: all adjacent to a1, or a1 itself. | B2 holds. The diagnostic agrees (0 checked positions without a move). |
| 2 | **Other corners and edges.** The choice of `ε, δ` (toward the board interior) must give on-board squares. `F = {0..7}` has 8 elements, so `a+ε` and `b+δ` are always in `F`. | Holds. |
| 3 | **The checking bishop is adjacent** (e.g. Bb2 checking Ka1). Capturing it is one possible escape, but B2 does not rely on capture. | B2's orthogonal escape still exists. The capture branch is handled by B3. |
| 4 | **King obstruction of bishop rays.** Could the `σ` king block a ray so that B1(a) fails? No: obstruction only *removes* attacked squares, never adds off-colour ones. | B1(a) holds for every occupancy. Test `test_bishop_ray_blocked_by_king`. |
| 5 | **X-ray after the king steps.** When the `ω` king leaves `k`, the bishop's ray continues past `k`. Could that hit `h` or `v`? Those squares have the opposite colour, so no. | Covered by B1(a) applied to the resulting position. |
| 6 | **Discovered check by a `σ` king move.** Allowed, and it is just a check by the bishop. B2 covers every check, however it arose. | No gap. |
| 7 | **Can the `σ` king check?** Only via adjacency, which is excluded by B0′. Double check is therefore impossible. | No gap. |
| 8 | **Illegal positions** (side not to move in check, e.g. both kings adjacent, or `σ` to move with `ω` in check). These are excluded from LKBK and never arise (B0) or follow a legal move (B3). The diagnostic filters them and confirms that `σ` is never in check in an LKBK state. | 0 violations. |
| 9 | **Capture branch.** The `ω` king takes an unprotected bishop, giving a KK position with `d∞ ≥ 2` that is admissible, after which EC-T0001 lemmas apply. A protected bishop cannot be taken (3.9.2). | The diagnostic saw 44,352 capture moves, all landing in admissible KK. Test `test_unprotected_bishop_capture_gives_kk`. |
| 10 | **Zero-length path.** The starting position itself must not be checkmate. B5 applies to `p ∈ LKBK`. | Holds. |
| 11 | **Both sides to move.** B5 handles `σ` to move and `ω` to move separately. | Holds. |
| 12 | **Orientation.** The proof is written for an abstract strong side `σ`. The diagnostic enumerates both colours as the strong side. | 999,936 placements, 0 mates. |
| 13 | **Quantifier error** (forced vs possible mate). `Dead` is ∀-paths (¬∃ path to a mate), over cooperative play too. B4 is a universal closure statement. | Correct. |
| 14 | **Stalemate confusion.** Stalemates exist (272 configurations; e.g. Ka8 / Kb6 + Bc7, the lone king to move). The theorem does not claim otherwise, and stalemate is not checkmate. | Not a counterexample. Test `test_known_stalemate`. |
| 15 | **Rule citation.** The S004 prompt cited "3.5 bishop". In fact 3.2 defines the bishop's diagonal move and 3.5 forbids moving over intervening pieces. | Both are quoted and cited correctly in the proof. |
| 16 | **Promotion / castling / en passant.** Impossible without pawns and rooks. | Stated in B3. |
| 17 | **Diagnostic sensitivity (mutation test).** The bishop was replaced by a rook-moving piece (K+R vs K, where mates exist), one orientation. | The diagnostic reported **216 checkmates** and 216 checked positions without a move. So the zero count for the bishop is meaningful. |

## 2. Diagnostic output (verbatim, `python3 scripts/kbk_diagnostic.py`)
```
placements: 999936
legal_states: 834456
checks_of_lone_king: 61320
checkmates: 0
stalemates: 272
legal_moves: 7938336
captures_to_kk: 44352
closure_violations: 0
lone_king_in_check_without_move: 0
strong_side_in_check: 0
seconds: 74.4
KBK DIAGNOSTIC PASSED (supplementary evidence, not a proof)
```

## 3. Residual assumptions
A1; the reading of the bishop attack from 3.1.2, 3.2 and 3.5; the FIDE 2023 text as retrieved; and dependence on EC-T0001's prose lemmas L2, L3 and L3a for the KK branch. **No gap found.** Verdict: Gate L passes, subject to the same-session caveat.
