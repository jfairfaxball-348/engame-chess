# EC-C008 — K+R vs K with the strong side to move is never dead (partial proof, S017)

**Status:** `PROPOSED`. **Gate L not passed.** Two gaps remain (G-P1, G-P2, §6). Audit: [audits/EC-C008_KRK_LIVE.md](../audits/EC-C008_KRK_LIVE.md).
**Rules:** the kernel encoding of FIDE 2023 (`docs/RULES_KERNEL.md`). **Companion:** [EC-T0006](../theorems/frozen/EC-T0006/v1.md).
**Attribution:** that K+R vs K is a win for the strong side is classical. The *cooperative* (possible-mate) statement proved here is weaker and also classical in spirit. Nothing is claimed as novel.

## 1. Statement
Let `q` be produced by a legal move, with `IsKRK q σ sk rs wk`.
- **(a)** If `q.turn = σ`, then `¬DeadK q`: some series of legal moves reaches checkmate.
- **(b)** If `q.turn = σ̄`, then `DeadK q` iff `q` is not checkmate and every legal move captures the rook.

**(a) ⇒ (b).**
- "⇐" is EC-T0006.
- "⇒", by contraposition:
  - if `q` is checkmate, it is not dead (the length-0 path);
  - if the lone king has a non-capturing legal move `q → q′`, then `q′` is K+R vs K with the strong side to move, produced by a legal move, so `¬DeadK q′` by (a), hence `¬DeadK q`. ∎

## 2. Standing facts (strong side to move, `q` produced by a legal move)
- F1. The side not to move (the lone king) is not in check, so the kings are not adjacent (as N0 in EC-C003).
- F2. The strong king is never in check (only adjacency could check it), so no strong piece is pinned.
- F3. Castling flags can only *add* strong-side moves. The route below never castles, so it is a legal series whatever the flags. En passant and promotion need pawns.
- F4. The reflections `x ↦ 7−x` and `y ↦ 7−y` preserve rook and king geometry, legality, check and mate. Apply them so that the strong king `S = (sx, sy)` has **`sx ≤ 3` and `sy ≥ 2`**: reflect in x if `sx ≥ 4`, and in y if `sy ≤ 1`. Colour symmetry gives both orientations.

## 3. The route
Notation: rook `R`, lone king `L`. The **zone** is `Z = {f8, g8, h8} = {(5,7), (6,7), (7,7)}`. The **tempo partner** of a zone square is h8 ↔ g8, with f8 → g8. Target `T = (sx, sy − 2)`.

1. **P1, rook home.** The rook reaches `Z` by the first of these explicit routes for which every rook move is legal and leaves the lone king a non-capturing reply (or mates):
   - (P1b) along rank 8;
   - (P1c) up its file, if on files f–h;
   - (P1d) across its rank to the h/g/f-file and then up, or up and then across;
   - (P1e) the detour `(rx, y₀) → (7, y₀) → h8`, with `y₀` = rank 1, or rank 2 if the rook stands on rank 1.

   The lone king's replies step towards `T`.
2. **P2, walk.** The rook makes tempo moves (zone square ↔ partner). The lone king walks to `T`.
3. **P3, escort.** With `L = (a, j)` and `S = (a, j+2)`, `a = sx ≤ 3`, they march down the a-column file together, until `L = (a,0)` and `S = (a,2)`.
4. **P4, parity.** The lone king steps to `(a+1, 0)`, the rook makes a tempo move, and the lone king steps back.
5. **P5, mate.** The rook moves from rank 8 straight down its file to rank 1.

## 4. Proved lemmas

**Lemma M (mate pattern).** Suppose:
- `L = (a,0)` and `S = (a,2)`, with `a ≤ 4`;
- the rook is on `(r, y)` with `r ≥ a+2` and `y ≥ 1`;
- the strong side is to move.

Then `R → (r,0)` is legal and checkmate.

*Proof.*
- **The move is legal.** The path `(r, 1..y−1)` is empty, because both kings stand on file `a ≠ r`. The target square is empty. The strong king is not in check (F2).
- **Check.** The squares `(a+1..r−1, 0)` are empty, so the rook attacks `L` along rank 1.
- **No escape.**
  - `(a−1,1)`, `(a,1)` and `(a+1,1)` are adjacent to `S`.
  - `(a+1, 0)` lies between the rook and `L` on rank 1.
  - `(a−1, 0)` lies on rank 1 beyond `L`. After `L` moves there, `(a,0)` is empty, so the rook attacks it. The kernel evaluates check on the board *after* the move.
- **No capture.** The rook is at distance `r − a ≥ 2` from `L`, so the lone king cannot take it. ∎

**Lemma E (escort, P3–P5).** Suppose:
- the rook is on `ρ ∈ Z`;
- `L = (a, j)` and `S = (a, j+2)`, with `a ≤ 3` and `0 ≤ j ≤ 5`;
- either side is to move.

Then checkmate is reachable.

*Proof.*
- **Setup.** If `j = 0` and the strong side is to move, apply Lemma M with `r = ρₓ ≥ 5 ≥ a+2`. Otherwise, if the strong side is to move, it first makes a rook tempo move `ρ → ρ′`. The partner square is empty: `S` is on file `a ≤ 3` and `L` is on a rank ≤ 6.
- **March.** From "lone king to move, `S − L = (0,2)`", repeat while `j > 0`:
  - **lone king `(a,j) → (a,j−1)`.** The target is empty. It is not adjacent to `S`, since `d∞ = 3`. It is not attacked by the rook: the rook is on rank 8 and on a file ≥ f, neither of which the target lies on. Blocking only removes attacked squares.
  - **strong king `(a, j+2) → (a, j+1)`.** The target is empty. It is not adjacent to `L`, since `d∞ = 2`. It is not the rook's square.
  - Both kings stay on file `a`, so they never block the rook's file.
- **Shuttle and mate.** At `j = 0`, with the lone king to move, play:
  1. `L → (a+1, 0)`. The square is empty. It is not adjacent to `(a,2)` (`d∞ = 2`). It is not attacked, because `a+1 ≤ 4 < 5` keeps it off the rook's file and it is not on rank 8.
  2. A rook tempo move, as before.
  3. `L → (a,0)`. The same checks apply.

  Now the strong side is to move: apply Lemma M. ∎

**Lemma W (walk, P2).** Let the rook stand on `ρ ∈ Z` with partner `ρ′`. Let `F` be the set of squares that:
- lie on ranks 1–7;
- are not on the files of `ρ` or `ρ′`;
- are at `d∞ ≥ 2` from `S`.

If `L` and `T` lie in the same king-move component of `F`, and the strong side is to move, then a position satisfying the hypotheses of Lemma E is reachable.

*Proof.*
- **`T ∈ F`.** Its rank is `sy − 2 ≤ 5`, its file is `sx ≤ 3`, and it is at `d∞ = 2` from `S`.
- **The strong move.** It is a rook tempo move `ρ ↔ ρ′`. The target is empty, because `S` is on file ≤ d and `L` is on a rank ≤ 7.
- **The lone king's step.** Take a king path `L = p₀, …, p_k = T` inside `F`. Each step is legal:
  - the target is empty, as neither king is on it, and it is not the rook's square (rank 8);
  - it is not adjacent to `S`, by the definition of `F`;
  - the rook does not attack it from `ρ` or `ρ′`. It is not on rank 8 or on either rook file. The rook's attacks are a subset of its rank and file, with blocking only removing squares.
- **Conclusion.** On arrival the strong side is to move, with `L = T = S − (0,2)` and `j = sy − 2 ≤ 5`. That is Lemma E's setting. ∎

**Corollary.** For any normalised state in which P1 succeeds and leaves `L` in the component of `F` containing `T`, mate is reachable.

## 5. Computational evidence (supplementary; `scripts/krk_route.py`)
The route was played from **every one of the 175,168** legal strong-to-move states (White strong; colour symmetry covers Black). Every move was checked against the independent generator of `krk_diagnostic.py`.
- **The route ends in checkmate in all 175,168 states.** The longest route is 31 plies.
- P1 rule usage:
  - rook already home: 8,256;
  - one-move route: 69,374;
  - two-move route: 96,302;
  - detour (P1e): 1,236.
- The Lemma W hypothesis (L in `T`'s component of `F` after P1) holds in 164,416 states and **fails in 10,752**. In those states the simulator's tempo cycling still led the lone king through, but that is not covered by Lemma W.

## 6. Gaps (why EC-C008 stays `PROPOSED`)
- **G-P1 (rook relocation).** No hand proof yet that, for every normalised state, one of the P1 routes is legal and leaves the lone king a non-capturing reply (or mates). It is verified exhaustively only.
- **G-P2 (connectivity after P1).** No hand proof that `L` ends P1 in `T`'s component of `F`. This is false for the route as specified in 10,752 states. **The route must be repaired:** the lone king may stand beyond the rook's file(s), e.g. on files g–h below the rook. Candidate repairs:
  - choose the zone on the side of `S` away from `L` (rank 8, left or right);
  - choose tempo moves along the file instead of the rank when `L` is on files f–h;
  - first walk the lone king across while the rook is still low.

Closing G-P1 and G-P2 completes (a), hence (b).

## 7. Planned Lean shape (after Gate L)
Lemmas M, E and W are schema-level: each is a move schema with a legality lemma over the kernel, and they generalise directly. P1 is the hard part to formalise. It needs a uniform argument, not a per-position certificate (charter: no lookup).
