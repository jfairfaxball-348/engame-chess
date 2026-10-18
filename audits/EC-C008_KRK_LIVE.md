# Audit — EC-C008 partial proof (S017, updated S018)

**Subject:** [proofs/EC-C008_KRK_LIVE.md](../proofs/EC-C008_KRK_LIVE.md). **Auditor:** same sessions (S017, S018); no independent reader.
**Verdict: Gate L NOT passed.** EC-C008 stays `PROPOSED`. One gap remains: G-P1. G-P2 is closed (S018).

| # | Attack | Outcome |
|---|---|---|
| 1 | Does (a) ⇒ (b) hold? A non-capturing lone-king move produces the next position by a legal move, so (a) applies to it. | Sound. |
| 2 | Do the reflections alone reach `sx ≤ 3, sy ≥ 2`? Yes: one reflection per axis, and both preserve rook and king geometry. | Sound. |
| 3 | Lemma M with `a = 0`: the `(a−1, ·)` squares do not exist, which only removes escapes. Lemma E has `a ≤ 3` and `r ≥ 6`. | Sound. |
| 4 | Lemma M x-ray: the escape to `(a−1, 0)` behind `L`. The kernel evaluates check after the move, so `(a,0)` is then empty and the rook sees through it. | Sound. |
| 5 | Lemma E with pair `H` (rook on h7, attacking rank 7): could the lone king's escort squares lie on rank 7? No: the escort keeps `L` on ranks 1–6 (`j ≤ 5`). | Sound. |
| 6 | Lemma E shuttle square `(a+1, 0)`: it is on file e at most, so it is attacked from neither pair square. | Sound. |
| 7 | Lemma C: do clipped boxes at the rectangle's edge break the free-row / free-column argument? No: `N1[S]` is at most 3 wide and 3 high, and the regions are 6 × 7 or 7 × 6. | Sound. |
| 8 | Lemma W: can king blocking ever open a square to the rook? No: blocking only removes attacked squares, and the regions are defined without blocking. | Sound. |
| 9 | Lemma S exhaustiveness: is `L` really never on the h-file below the rook? Only a king could block the h-file. `S` is on files a–d, and `L` itself would then be attacked. | Sound. |
| 10 | Lemma S case 4: is g8 really impossible for `L`? The rook on h8 attacks g8, so `L` would be in check, which is illegal for the side not to move. | Sound. |
| 11 | Lemma S case 3: is `Rg8+` with `Kf6` legal? Kf6 must not be attacked by the rook on g8, which covers rank 8 and the g-file only, and must not be adjacent to `S` (file f vs files a–d). | Sound. |
| 12 | P1: after each relocation move, does the lone king have a non-capturing reply? | Verified exhaustively only. **Gap G-P1.** |
| 13 | Flags: the route never castles, and flags only add moves. | Sound. |

## Simulator output (verbatim, `python scripts/krk_route.py`, route v2, S018)
```
strong_to_move_states: 175168
route_reaches_mate: 175168
longest_route_plies: 31
phase1_rule_counts: {'P1-HV': 130856, 'P1-VH': 3438, 'P1-detour': 1222, 'P1-direct': 36900, 'P1-home': 2752, 'P2-G': 171554, 'P2-H': 3240, 'P2-g7': 64, 'P2-rank8': 12}
```
(S017, route v1: mate in 175,168 states, but the Lemma W invariant failed in 10,752 of them. Route v2 enforces it as a hard check.)
