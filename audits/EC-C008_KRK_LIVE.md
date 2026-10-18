# Audit — EC-C008 partial proof (S017)

**Subject:** [proofs/EC-C008_KRK_LIVE.md](../proofs/EC-C008_KRK_LIVE.md). **Auditor:** same session (S017). **Verdict: Gate L NOT passed.** EC-C008 stays `PROPOSED`.

| # | Attack | Outcome |
|---|---|---|
| 1 | (a) ⇒ (b): could a non-capturing lone-king move produce a strong-to-move position that is not "produced by a legal move"? No: it is produced by that very move. | Sound. |
| 2 | Reflections only (no transposition): do they reach `sx ≤ 3, sy ≥ 2` for every `S`? Yes: one reflection per axis. They preserve rook and king geometry. | Sound. |
| 3 | Lemma M on the a-file (`a = 0`): `(a−1, ·)` squares do not exist, and the rest is unchanged. With `a = 4`, `r ≥ 6` is needed. In Lemma E, `a ≤ 3` and `r ≥ 5`. | Sound. |
| 4 | Lemma M x-ray: escape to `(a−1,0)` behind `L` on rank 1. The kernel evaluates check after the move, when `(a,0)` is empty. | Sound. |
| 5 | Lemma E: is the tempo partner square ever occupied? `S` is on file ≤ d; `L` is on ranks ≤ 6 during the escort. | Sound. |
| 6 | Lemma E: the shuttle square `(a+1,0)` with `a = 3` is e1, which is not on files f–h. | Sound. |
| 7 | Lemma W: blocking by kings could *open* a square? No: blocking only removes attacked squares. `F` is defined conservatively, without blocking. | Sound. |
| 8 | Lemma W: the lone king must be in `F`'s component of `T`. **Fails in 10,752 states after P1 as specified** (simulator). | **Gap G-P2.** |
| 9 | P1: a lone-king non-capturing reply after every relocation move. Verified exhaustively, not by hand. | **Gap G-P1.** |
| 10 | Flags and castling: never used by the route; they only add moves (F3). | Sound. |
| 11 | Stalemate or forced capture en route: excluded in P1 by construction (checked per state by the simulator); in P2–P5 by Lemmas W/E (non-capturing moves exhibited explicitly). | P2–P5 sound; P1 = G-P1. |

## Simulator output (verbatim, `python scripts/krk_route.py`)
```
strong_to_move_states: 175168
route_reaches_mate: 175168
longest_route_plies: 31
phase1_rule_counts: {'INV-not-connected': 10752, 'P1-1': 69374, 'P1-2': 96302, 'P1a': 8256, 'P1e': 1236}
```
