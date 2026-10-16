# Mathematical foundations (model specification)

The **chess laws** and our **mathematical abstraction** are different layers. First specify legal game states and transitions, then deduce consequences. Working normative reference: FIDE Laws of Chess, approved 07/08/2022, applied from 1 January 2023, https://handbook.fide.com/chapter/E012023. Articles used for the two-king layer: 1.2, 1.4, 1.4.1, 1.5, 3.1–3.1.3, 3.8–3.8.2, 3.9.1–3.9.2, 3.10.1–3.10.3, 5.1.1, 5.2.1, 5.2.2 (verbatim quotations in [proofs/EC-C001_KK.md](../proofs/EC-C001_KK.md)). Record any later version change explicitly.

*Revision S001:* repaired the two-king layer (side-to-move in the step relation, derivation of the move set from Articles 3.1–3.9 instead of stipulation, explicit `Arisen` vs `Admissible`, explicit checkmate/stalemate predicates, counterfactual move graph).

## Board and metric
`F = {0,…,7}`; squares `S = F × F` (file, rank; `(0,0)` = a1). For `p=(x,y)`, `q=(u,v)`:

`d∞(p,q) = max(|x-u|, |y-v|)` (Chebyshev distance; a metric on `S`).

`N(p) = { q ∈ S : d∞(p,q) = 1 }` — the on-board *adjoining squares* of `p` (3 at a corner, 5 on a non-corner edge, 8 inside). Modelling assumption **A1**: FIDE 3.8.1 "adjoining square" means exactly `N(p)` (orthogonal and diagonal neighbours), as the Article 3.8 diagrams show.

## Two-king core state
A *KK configuration* is `p = (w,b,t)` with White king on `w ∈ S`, Black king on `b ∈ S`, side to move `t ∈ {W,B}`, and no other pieces. Castling rights and en-passant rights are irrelevant (no rooks, no pawns).

- **`Admissible(p)`** :⇔ `d∞(w,b) ≥ 2`. A purely local condition.
- **`Arisen(p)`** :⇔ `p` (as a position with only two kings) is reached from the standard initial position by a finite series of FIDE-legal moves. `Arisen ⇒ Admissible` is a lemma (L0 of the proof), not a definition; `Admissible ⇏ Arisen` is not claimed either way and is not needed.

Write `K_c(p)` for the square of the colour-`c` king and `c̄` for the opposite colour.

## Attack, check, legal move (derived from FIDE 3.1–3.9)
- **Attack.** By 3.1.2–3.1.3 a king on `s` attacks square `q` iff it could capture on `q` by Article 3.8, ignoring self-check. Castling (3.8.2) never captures, so a king on `s` attacks `q` iff `q ∈ N(s)`, i.e. iff `d∞(s,q) = 1`.
- **`InCheck(c,p)`** :⇔ the colour-`c` king is attacked by an opposing piece (3.9.1). In a KK configuration the only opposing piece is the other king, so `InCheck(c,p) ⇔ d∞(w,b) = 1`.
- **`LegalKK(p,q)`**, for `p=(w,b,t)`: the side-to-move `t` (1.2) moves its king to `s ∈ N(K_t(p))` (3.8.1; castling 3.8.2 is impossible without a rook) with `s ≠ K_t̄(p)` (capturing the king is forbidden, 1.4.1) and such that afterwards the colour-`t` king is not attacked (3.9.2), i.e. `d∞(s, K_t̄(p)) ≥ 2`; `q` is `p` with `K_t` replaced by `s` and the turn set to `t̄`. By 3.10.1 these are *all* legal moves in a KK configuration.
- **`Checkmate(c,p)`** :⇔ `t = c`, `InCheck(c,p)`, and there is no `q` with `LegalKK(p,q)` (1.4, 5.1.1). A player *checkmates the opponent* by reaching such a `p` with `c` the opponent.
- **`Stalemate(p)`** :⇔ `¬InCheck(t,p)` and no legal move (5.2.1). Not a checkmate.
- **`Reach(p,q)`**: the reflexive–transitive closure of `LegalKK` — a finite sequence `p = p₀, p₁, …, pₙ = q` (`n ≥ 0`) with `LegalKK(pᵢ, pᵢ₊₁)`. Both players' moves are chosen arbitrarily (cooperation allowed); no 'eventually', no strategy.

## Counterfactual move graph
FIDE 5.2.2 ends the game the moment a dead position arises, so the series of moves it quantifies over is never actually played. Article 3.10.1 defines legality purely by Articles 3.1–3.9 (position-local conditions), so the move relation is well defined at a position whether or not the game has terminated. `Reach` is built from `LegalKK` **without** any stopping rule (no termination at checkmate, stalemate, dead position, repetition or move counts). This is the graph over which 5.2.2's "any series of legal moves" is read.

## Dead position and draw
- **`Dead(p)`** :⇔ there is **no** `q` with `Reach(p,q)` and `Checkmate(W,q) ∨ Checkmate(B,q)`. The quantifier is ∀ over every finite path (equivalently ¬∃ path to mate). This is strictly stronger than "neither side can *force* mate".
- **`RuleDraw(p)`**: if `Arisen(p)` and `Dead(p)`, the game ends drawn immediately by Article 5.2.2 (see also 1.5).

Distinct predicates, never conflated: *no possible mate* (`Dead`), *no forced mate*, *drawn by rule*. Repetition, the 50/75-move rules, agreement, resignation (5.1.2) and flag-fall (6.9) are separate rule layers not used in the KK theorem.

## K vs K derivation (proved in S001)
See [proofs/EC-C001_KK.md](../proofs/EC-C001_KK.md) for the full proof (L0–L6) and [audits/EC-C001_KK.md](../audits/EC-C001_KK.md) for the hostile audit. Superseded draft: [research/KK_DRAFT.md](../research/KK_DRAFT.md).

## K+B vs K layer (S004)
Used by [proofs/EC-C002_KBK.md](../proofs/EC-C002_KBK.md). This section adds to the two-king layer and leaves its meaning unchanged.
- **Configuration** `(K, X, k, t)`: the strong side `σ` has a king on `K` and a bishop on `X`; the weak side `ω` has a king on `k`; `t` is the side to move. The squares are pairwise distinct.
- **Bishop attack** (3.1.2, 3.2, 3.5): the squares on a diagonal of `X`, up to and including the first occupied square. The kings are the only possible blockers.
- **Square colour** `col(x,y) = (x+y) mod 2`. A bishop attacks only squares of its own colour. Orthogonal neighbours have opposite colours.
- **`LKBK(p)`**: the side not to move is not in check. Arisen ⇒ LKBK, by 3.9.2 applied to the last move.
- **Material class closed under legal moves**: `LKBK ∪ AdmKK`. The weak king may capture the bishop, giving K vs K, which reduces to EC-T0001.

## Planned extension points
For bishops, knights, rooks and queens, define separate attack relations with obstruction for sliding pieces. Add full position typing, material invariants, side-to-move, piece captures, king safety and terminal states. For pawns, add directional movement, promotions, en passant, move-history fields and time-based drawing rules only as required by specific claims. Note for EC-C002/3: with a third piece present, captures change material, so the invariant must be stated over a material *class* that is closed under legal moves, not assumed fixed.
