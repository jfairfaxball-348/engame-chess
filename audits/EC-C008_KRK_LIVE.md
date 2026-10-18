# Audit — EC-C008 local proof (S017–S019)

**Subject:** [proofs/EC-C008_KRK_LIVE.md](../proofs/EC-C008_KRK_LIVE.md). **Auditor:** same sessions (S017–S019); no independent reader.
**Verdict: Gate L passes (S019), subject to the same-agent caveat.** G-P2 was closed in S018 and G-P1 in S019. EC-C008 → `LOCAL_VERIFIED`.

| # | Attack | Outcome |
|---|---|---|
| 1 | (a) ⇒ (b): a non-capturing lone-king move produces a position by a legal move. | Sound. |
| 2 | Reflections alone reach `sx ≤ 3, sy ≥ 2`, and they preserve rook and king geometry. | Sound. |
| 3 | Lemma M at `a = 0`: the missing `(a−1, ·)` squares only remove escapes. In Lemma E, `a ≤ 3` and `r ≥ 6`. | Sound. |
| 4 | Lemma M x-ray: check is evaluated after the move, when `(a,0)` is empty. | Sound. |
| 5 | Lemma E with the pair `H`: the escort keeps `L` on ranks 1–6, so the rook on h7 (attacking rank 7) never hits it. | Sound. |
| 6 | Lemma C on clipped boxes: the box is at most 3 × 3, inside a 6 × 7 or 7 × 6 rectangle. | Sound. |
| 7 | Lemma W: blocking only removes attacked squares. | Sound. |
| 8 | Lemma S exhaustiveness: `L` is never on the h-file below h8, and never on g8. | Sound. |
| 9 | Lemma S case 3, `Rg8+` then Kf6: f6 is attacked by neither g8 nor `S`. | Sound. |
| 10 | **RL-h**, `L` on rank 1 or 8 with `L_y = ρ` and shielded: then `(L_x, L_y ∓ 1)` is free, since `|sx − L_x| ≥ 2`. Unshielded and fully covered means `S = (L_x, L_y ∓ 2)`, which is not on rank `ρ`, so `L` is in check and it is checkmate, not stalemate. | Sound. |
| 11 | **RL-h**, corner a8 with `ρ` = rank 7: `S` = c7 blocks the rook's ray, freeing a7 and b7; `S` = c8 gives the stated exception. Brute force over all `S`, `ρ` and `L` finds exactly this one exception. | Sound. |
| 12 | **RL-h**, corner a1: normalisation (`sy ≥ 2`, i.e. rank 3 or higher) stops `S` covering b1. Without normalisation the claim would fail: c1/c2 versions exist. | Sound; normalisation is essential and is stated. |
| 13 | **RL-f** needs `rx < sx`. All three FS classes provide it: in F1/F3, `S` is between the rook and the h-file. F2 is handled separately. Brute force: 9,279 instances, 0 exceptions. | Sound. |
| 14 | **Lemma P1**, FS leg 1: is `(rx, y′)` ever the rook's own square (`y′ = ry`)? No. F1 uses rank 1 or rank 8 with the rook off rank 8; F3 uses rank 1 or rank 5 with the rook on rank 8; F2 uses rank 1 with the rook on rank 7. | Sound. |
| 15 | **Lemma P1**: does a lone reply ever step onto the rook's next path? No. By (iii) it is never on an unshielded rook line, and only `S` can shield; the branch facts show that `S` is not on the next path. | Sound. |
| 16 | Is the reply "any non-capturing move", or one chosen move? The proof covers **any** non-capturing reply. The simulator exercised one particular reply; the proof does not depend on that choice. | Sound. |
| 17 | Flags and castling: never used, and they only add moves. | Sound. |
| 18 | Are the RL-h and RL-f brute-force checks the proof? No. They are supplementary; the case analyses in §4b are the proof. | Correct status. |

## Simulator output (verbatim, `python scripts/krk_route.py`, route v3, S019)
```
strong_to_move_states: 175168
route_reaches_mate: 175168
longest_route_plies: 31
phase1_rule_counts: {'FS-F1': 3432, 'FS-F2': 24, 'FS-F3': 1204, 'HV': 130856, 'P2-G': 171560, 'P2-H': 3240, 'P2-g7': 64, 'P2-rank8': 12, 'direct-hfile': 18996, 'direct-rank8': 17904, 'home': 2752}
```
Reply-lemma brute force (S019): RL-h has a single exception, `(c8, h7, a8)`; RL-f has 9,279 instances and 0 exceptions.
