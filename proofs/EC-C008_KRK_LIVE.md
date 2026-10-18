# EC-C008 — K+R vs K with the strong side to move is never dead (partial proof, S017–S018)

**Status:** `PROPOSED`. **Gate L not passed.** One gap remains (G-P1, §6). G-P2 was closed in S018 by route v2 (§3, Lemmas C and S). Audit: [audits/EC-C008_KRK_LIVE.md](../audits/EC-C008_KRK_LIVE.md).
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

## 3. The route (v2, S018)
Notation: rook `R`, lone king `L`, target `T = (sx, sy − 2)`, `N1[S]` = the squares at `d∞ ≤ 1` from `S`. There are two **tempo pairs**, each with a **region**:
- `G` (h8 ↔ g8): region files a–f × ranks 1–7, minus `N1[S]`.
- `H` (h8 ↔ h7): region files a–g × ranks 1–6, minus `N1[S]`.

Since `sx ≤ 3`, `N1[S]` lies within files a–e. **No square on files f–h is adjacent to `S`.**

1. **P1, rook to h8.** Use the first of these explicit routes for which every rook move is legal and leaves the lone king a non-capturing reply (or mates):
   - (direct) one move, if the rook is on rank 8 or on the h-file;
   - (HV) `(rx, ry) → (h, ry) → h8`;
   - (VH) `(rx, ry) → (rx, 8) → h8`;
   - (detour) `(rx, y₀) → (h, y₀) → h8`, with `y₀` = rank 1, or rank 2 if the rook is on rank 1.

   The lone king replies with a non-capturing move, preferring the region `G`.
2. **P2, settle and walk.** Lemma S, then Lemma W with the pair that Lemma S chooses.
3. **P3–P5, escort, parity, mate.** Lemma E with the same pair, then Lemma M.

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
- the rook is on a square `ρ` of a tempo pair `P ∈ {G, H}`, and all tempo moves stay in `P`;
- `L = (a, j)` and `S = (a, j+2)`, with `a ≤ 3` and `0 ≤ j ≤ 5`;
- either side is to move.

Then checkmate is reachable.

*Proof.*
- **Setup.** If `j = 0` and the strong side is to move, apply Lemma M with `r = ρₓ ≥ 6 ≥ a+2` and `y ≥ 6`. Otherwise, if the strong side is to move, it first makes a rook tempo move `ρ → ρ′` inside `P`. The partner square (h8, g8 or h7) is empty: `S` is on file `a ≤ 3`, and `L` is on file `a` and on a rank ≤ 6.
- **March.** From "lone king to move, `S − L = (0,2)`", repeat while `j > 0`:
  - **lone king `(a,j) → (a,j−1)`.** The target is empty. It is not adjacent to `S`, since `d∞ = 3`. It is not attacked by the rook. On h8, g8 or h7 the rook attacks only ranks 7–8 and files g–h, while the target is on rank ≤ 6 and file `a ≤ d`. Blocking only removes attacked squares.
  - **strong king `(a, j+2) → (a, j+1)`.** The target is empty. It is not adjacent to `L`, since `d∞ = 2`. It is not the rook's square.
  - Both kings stay on file `a`, so they never block the rook's file.
- **Shuttle and mate.** At `j = 0`, with the lone king to move, play:
  1. `L → (a+1, 0)`. The square is empty. It is not adjacent to `(a,2)` (`d∞ = 2`). It is not attacked: it is on rank 1 and file `a+1 ≤ e`.
  2. A rook tempo move, as before.
  3. `L → (a,0)`. The same checks apply.

  Now the strong side is to move: apply Lemma M. ∎

**Lemma C (region connectivity).** Let `A` be a rectangle of squares and `B` a sub-rectangle that spans neither the full width nor the full height of `A`. Then `A \ B` is connected under rook steps, and hence under king moves.

*Proof.*
- Some column `c` of `A` misses `B`, and some row `ρ` of `A` misses `B`. Their union is connected, since they cross, and it lies in `A \ B`.
- Take `q ∈ A \ B`.
  - If `q`'s row misses `B`, walk along that row to column `c`.
  - Otherwise `q`'s row meets `B`. Since `q ∉ B`, `q`'s column is not one of `B`'s columns, so it misses `B`. Walk along that column to row `ρ`. ∎

Lemma C applies to the 6 × 7 and 7 × 6 rectangles, each with `B = N1[S] ∩ A` (at most 3 × 3). So both regions `G` and `H` are connected. Both contain `T`:
- its file is `sx ≤ d`;
- its rank is `sy − 2 ≤ 6`;
- it is at `d∞ = 2` from `S`.

**Lemma W (walk, P2).** Suppose:
- the rook stands on a square of a fixed tempo pair `P ∈ {G, H}`;
- `L` lies in `P`'s region;
- the strong side is to move.

Then a position satisfying Lemma E's hypotheses (with the pair `P`) is reachable.

*Proof.* By Lemma C, there is a king path from `L` to `T` inside the region. Each round is a rook tempo move inside `P`, then the lone king's next step along the path.
- **The tempo move is legal.** Its target is empty:
  - `S` is on files a–d;
  - in `G`, `L` is on files a–f, so it is not on g8;
  - in `H`, `L` is on ranks 1–6, so it is not on h7.
- **The step is legal.**
  - The target is not `S`'s square, not adjacent to `S`, and not the rook's square.
  - It is not attacked from either square of the pair. In `G` the rook attacks only rank 8 and files g–h; in `H` only ranks 7–8 and file h. The region avoids both sets, and blocking only shrinks the attacked set.
- **On arrival.** The strong side is to move with `L = T`, so `j = sy − 2 ≤ 5`. That is Lemma E's setting. ∎

**Lemma S (settling after P1).** Suppose the rook is on h8, the strong side is to move, the position is legal, and `S` is normalised. Exactly one of four cases holds, and each reaches Lemma W's hypothesis.
1. **`L` in region `G`.** Use the pair `G`.
2. **`L` on the g-file, ranks 1–6.** The g-file is never adjacent to `S`, so `L` lies in region `H`. Use the pair `H`.
3. **`L = g7`.**
   - Play `Rh8–g8+`. g8 is empty, and the rook checks along the g-file.
   - The lone king replies `Kf6`. f6 is empty, it is not adjacent to `S` (file f), and the rook on g8 attacks only rank 8 and the g-file.
   - Now `L = f6`, in region `G`, with the rook on g8 inside the pair `G` and the strong side to move. Continue as in Lemma W.
4. **`L` on rank 8.**
   - Since the position is legal, `L` is not in check. g8 and h8 are excluded: h8 is the rook's square, and g8 is attacked by it. So `L` is on files a–f, shielded by `S` standing between `L` and h8 on rank 8. Hence `S` is on rank 8 and `Lₓ ≤ sx − 2`.
   - Play `Rh8–g8`. `S` still shields rank 8, and `L` is not on the g-file, so this is no check.
   - Reply `L → (Lₓ, 7)`. The square is empty. It is not attacked, being off rank 8 and off files g–h. It is not adjacent to `S`, because `|Lₓ − sx| ≥ 2`. It lies in region `G`; continue with the pair `G`.

**Exhaustiveness.**
- `L` is not on the h-file below h8: those squares are attacked along the h-file, and `S` (files a–d) cannot block that line.
- `L` is not in `N1[S]`, because the kings are not adjacent.
- So, outside region `G`, `L` stands on the g-file or on rank 8. Those squares are covered by cases 2–4, with g8 impossible. ∎

**Corollary.** From every normalised strong-to-move state in which P1 succeeds, mate is reachable. Success means the rook reaches h8 (or mates), with every move legal and only non-capturing lone-king replies. So **EC-C008 reduces to the relocation lemma (G-P1).**

## 5. Computational evidence (supplementary; `scripts/krk_route.py`, route v2)
The route was played from **every one of the 175,168** legal strong-to-move states (White strong; colour symmetry covers Black). Every move was checked against the independent generator of `krk_diagnostic.py`. Lemma S's case split and the connectivity of Lemma W are enforced as **hard checks**.
- **The route ends in checkmate in all 175,168 states.** The longest route is 31 plies.
- P1 routes used:
  - rook already on h8: 2,752;
  - direct: 36,900;
  - HV: 130,856;
  - VH: 3,438;
  - detour: 1,222.
  - P1 itself mates in 298 states.
- Lemma S cases: `G` 171,554; g-file 3,240; g7 64; rank 8 12.

## 6. Gap (why EC-C008 stays `PROPOSED`)
- **G-P1 (rook relocation to h8).** No hand proof yet that, for every normalised strong-to-move state, one of the P1 routes is legal and leaves the lone king a non-capturing reply after each rook move (or mates). It is verified exhaustively only. Everything after P1 is proved (Lemmas S, C, W, E, M).
- **G-P2: closed in S018** by route v2 and Lemmas C and S.

## 7. Planned Lean shape (after Gate L)
Lemmas M, E, W, C and S are schema-level: each is a move schema with a legality lemma over the kernel, and they generalise directly. P1 is the hard part to formalise. It needs a uniform argument, not a per-position certificate (charter: no lookup).
