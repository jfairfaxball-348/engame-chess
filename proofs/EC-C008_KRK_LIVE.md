# EC-C008 — K+R vs K with the strong side to move is never dead (local proof, S017–S019)

**Status:** `LOCAL_VERIFIED` (Gate L, S019). Not formally verified; not frozen. G-P2 was closed in S018 (Lemmas C and S); G-P1 was closed in S019 (Lemmas RL-h, RL-f and P1, §4b). Audit: [audits/EC-C008_KRK_LIVE.md](../audits/EC-C008_KRK_LIVE.md). **Lean (partial, S021):** infrastructure and Lemmas M, E, C, W, S in `formal/EndgameChess/Rules/KRKLive/`; [Lean audit](../audits/EC-C008_KRK_LIVE_LEAN.md). RL-h, RL-f, P1 and the main theorem are not yet formalised.
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

## 3. The route (v3: P1 rule from S019; P2–P5 from S018)
Notation: rook `R`, lone king `L`, target `T = (sx, sy − 2)`, `N1[S]` = the squares at `d∞ ≤ 1` from `S`. There are two **tempo pairs**, each with a **region**:
- `G` (h8 ↔ g8): region files a–f × ranks 1–7, minus `N1[S]`.
- `H` (h8 ↔ h7): region files a–g × ranks 1–6, minus `N1[S]`.

Since `sx ≤ 3`, `N1[S]` lies within files a–e. **No square on files f–h is adjacent to `S`.**

1. **P1, rook to h8** (v3, S019). Apply the first rule that fits:
   - **home:** the rook is already on h8;
   - **direct:** the rook is on the h-file; or it is on rank 8 with `S` not on rank 8 between it and h8. The rook moves to h8;
   - **HV:** the rook is off rank 8 and the h-file, the squares `(rx+1 … h, ry)` are empty, and the position is not the exception `(S, L, ry) = (c8, a8, rank 7)`. The route is `(rx, ry) → (h, ry) → h8`;
   - **file-shift FS:** otherwise. Let `y′` be rank 1 if `L` is on rank 3 or higher; otherwise rank 8, unless the rook is on rank 8, in which case rank 5. The route is `(rx, ry) → (rx, y′) → (h, y′) → h8`, where the middle move is omitted if `y′` is rank 8.

   After each rook move the lone king plays **any** non-capturing legal move (one exists, by §4b), unless it is mated.
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

## 4b. Rook relocation (closes G-P1, S019)

**Lemma RL-h (reply to a rook on the h-file).** Let `S` be normalised, let the rook stand on `(h, ρ)`, and let `L` be on any other square not adjacent to `S`, with the lone king to move. Then the lone king has a non-capturing legal move, or it is checkmated. The single exception is `(S, R, L) = (c8, h7, a8)`, which is a stalemate.

*Proof.* Recall that squares on files f–h are never adjacent to `S`. Split on `L`'s file.
1. **`L` on the h-file.** The square `(g, L_y)` is:
   - empty, since `S` is on files a–d;
   - not adjacent to `S`;
   - not on the h-file;
   - not on rank `ρ`, because `L_y ≠ ρ`.

   So it is not attacked, and the move to it is legal and non-capturing.
2. **`L` on files f–g.**
   - If one of `(L_x, L_y ± 1)` is on the board and not on rank `ρ`, it is a legal non-capturing destination: it is on files f–g, off the h-file and off rank `ρ`.
   - Otherwise `L` is on rank 1 or 8 and its single vertical neighbour is on rank `ρ`. Then `L_y ≠ ρ`, and `(x′, L_y)` with `{L_x, x′} = {f, g}` is a legal destination.
3. **`L` on files a–e.** The rook is at file distance ≥ 3, so no move captures. Among `L`'s neighbours, the rook can attack only those on rank `ρ`. **Opposite-neighbour fact:** a king at `d∞ ≥ 2` from `L` cannot be adjacent to two neighbours `q` and `2L − q` of `L` on opposite sides, since that would force `d∞(S, L) ≤ 1`. In particular `S` covers at most one of each opposite pair.
   - **`|L_y − ρ| ≥ 2`.** Only `S` covers neighbours. Some opposite pair is on the board unless `L` is in a corner. In the corners a1 and a8, `S` cannot cover all three neighbours: covering both orthogonal neighbours would force adjacency to `L`. So a move exists.
   - **`|L_y − ρ| = 1`.**
     - If `L` is not on the a-file, the pair `(L_x ± 1, L_y)` is on the board and off rank `ρ`, so one of them is free.
     - On the a-file, but not in a corner: covering `(b, L_y)` and both far-row squares forces adjacency, so some neighbour is free.
     - In the corner a1 with `ρ` = rank 2: the remaining neighbour is b1, and `S` (rank ≥ 3) cannot cover it.
     - In the corner a8 with `ρ` = rank 7: the remaining neighbour b8 is covered only by `S` ∈ {c7, c8}.
       - `S` = c7 stands on rank 7 between the rook and a7/b7, so it blocks the rook's ray and they are free.
       - `S` = c8 gives the stalemate `(c8, h7, a8)`: **the exception**.
   - **`L_y = ρ`.** The vertical pair `(L_x, L_y ± 1)` is off rank `ρ`, so if both are on the board one is free. If `L` is on rank 1 or 8, no move exists only if `S` covers all three squares of the adjacent row. Then `S = (L_x, L_y ∓ 2)` is not on rank `ρ`, so `L` is in check, and this is checkmate. ∎

**Lemma RL-f (reply after a file-shift move).** Let `S` be normalised, and let the rook stand on `(rx, y′)` with `rx < sx`. Suppose `L` is not on file `rx`, `|L_y − y′| ≥ 2`, `L` is not adjacent to `S`, and the lone king is to move. Then the lone king has a non-capturing legal move.

*Proof.*
- **Setting.** The rook is not adjacent to `L`, because the ranks differ by ≥ 2. So no move captures. `L` is not in check: it is off file `rx`, off rank `y′`, and not adjacent to `S`. The rook's rank does not meet `L`'s neighbours. It attacks at most the neighbours on file `rx`, and only if `|L_x − rx| = 1`.
- **`|L_x − rx| ≥ 2`.** Only `S` covers neighbours. Use the opposite-neighbour fact. The corners a1 and a8 have `L_x = a`, which would force `rx < a`: impossible. In the corners h1 and h8, no neighbour is adjacent to `S`.
- **`L_x = rx + 1`.**
  - If `L` is not on rank 1 or 8, the vertical pair `(L_x, L_y ± 1)` is free of the rook, and one member is free of `S`.
  - On rank 1, `S` (rank ≥ 3) can cover only rank-2 squares, so `(L_x + 1, 1)` is free. It is on the board, because `L_x = rx + 1 ≤ c`.
  - On rank 8, covering `(L_x, 7)`, `(L_x + 1, 8)` and `(L_x + 1, 7)` together forces `S` adjacent to `L`.
- **`L_x = rx − 1`.** Then `sx > rx = L_x + 1`, so `S` is at file distance ≥ 2 from `L`'s column. So `S` is adjacent to none of `(L_x, L_y ± 1)`. Those squares are off file `rx` and off rank `y′`, and one of them is on the board. ∎

**Lemma P1 (relocation).** Take every normalised legal strong-to-move K+R vs K position. Rule P1 (§3) consists of legal rook moves. After each of them, the lone king has a non-capturing legal move or is mated. P1 ends with the rook on h8 and the strong side to move, or in checkmate.

*Proof.* Facts used throughout:
- (i) The strong king is never in check and no strong piece is pinned (F2), so every geometrically valid rook move is legal.
- (ii) When the strong side is to move, `L` is not attacked. So `L` is never on an unshielded rook line, and only `S` can shield.
- (iii) After any legal lone-king reply, (ii) holds again.

The branches:
- **direct, from the h-file.** The h-file is clear, because `L` is not on it (ii) and `S` is on files a–d. h8 is empty. The reply exists by RL-h; the exception needs the rook on h7, not h8.
- **direct, from rank 8.** The rank-8 squares between the rook and h8 are empty:
  - `S` is not there, by the branch condition;
  - an `L` there would be unshielded, contradicting (ii).

  The reply exists by RL-h.
- **HV.**
  - **Leg 1** is legal by the branch condition. The reply exists by RL-h, since the exception is excluded.
  - **Leg 2**, `(h, ry) → h8`. After the reply, `L` is not on the h-file by (iii), and `S` is not there either, so the path and h8 are empty. The reply exists by RL-h.
- **FS.** Classify why HV and direct do not apply.
  - F1, F3: a king is on the rook's rank between it and the h-file. By (ii), `S` stands there (between the rook and `L` if `L` is there too), so `sx > rx` and the rook is on rank `sy`.
  - F2: the exception, `S` = c8, `L` = a8, rook on rank 7.
- **Leg 1**, `(rx, ry) → (rx, y′)`.
  - `y′ ≠ ry`:
    - in F1, `ry = sy ≥ 3` (rank 3 or higher) and `y′` ∈ {rank 1, rank 8}, with rank 8 used only when `ry` is not rank 8;
    - in F3, `ry` is rank 8 and `y′` ∈ {rank 1, rank 5};
    - in F2, `y′` is rank 1.
  - The file `rx` is clear between `ry` and `y′`:
    - `S` is not on it: in F1/F3 `sx > rx`; in F2 `S` = c8 is above the rook's rank;
    - `L` is not on it, by (ii), since no shield is available.
  - `(rx, y′)` is empty:
    - `L` is off rank `y′`, because `|L_y − y′| ≥ 2` by the choice of `y′`;
    - `S` is off rank `y′`, because `y′ ≠ sy` in F1/F3, and `S` is on rank 8 in F2 while `y′` is rank 1.
  - **Reply:**
    - in F1 and F3, by RL-f, since `rx < sx`, `L` is off file `rx` and `|L_y − y′| ≥ 2`;
    - in F2 (`L` = a8, rook on `(rx, 1)` with `rx ≠ a`, since an a-file rook would have attacked a8), a7 is free: it is not on the rook's file, and at `d∞ = 2` from c8.
- **Leg 2**, `(rx, y′) → (h, y′)`, when `y′` is not rank 8.
  - The rank is clear: `S` is not on it, and `L` is not on it unshielded by (iii).
  - `(h, y′)` is empty.
  - The reply exists by RL-h. The exception needs `y′` = rank 7, but `y′` ∈ {rank 1, rank 5}.
  - When `y′` is rank 8, leg 2 is `(rx, 8) → h8` along rank 8. It is clear, because `S` is not on rank 8 in F1 and `L` is not there by (iii). The reply exists by RL-h.
- **Leg 3**, `(h, y′) → h8`, along the h-file. It is clear by (iii). The reply exists by RL-h.

If the lone king is mated at any point, the route has succeeded. ∎

**Theorem (EC-C008(a)).** Take every legal strong-to-move K+R vs K position. Normalise it (F4); P1 then succeeds (Lemma P1), and Lemmas S, W, E and M finish the mate. Hence `¬DeadK`. Part (b) follows (§1). ∎

## 5. Computational evidence (supplementary; `scripts/krk_route.py`, route v3)
The route was played from **every one of the 175,168** legal strong-to-move states (White strong; colour symmetry covers Black). Every move was checked against the independent generator of `krk_diagnostic.py`. Lemma S's case split and the connectivity of Lemma W are enforced as **hard checks**.
- **The route ends in checkmate in all 175,168 states.** The longest route is 31 plies.
- P1 branches (v3, every state classified; none unclassified):
  - home: 2,752;
  - direct (h-file): 18,996;
  - direct (rank 8): 17,904;
  - HV: 130,856;
  - FS-F1: 3,432;
  - FS-F2: 24;
  - FS-F3: 1,204.
- **Lemma statements checked exhaustively:**
  - RL-h: 1 exception, the stated stalemate;
  - RL-f: 9,279 instances, 0 exceptions.
- Lemma S cases: `G` 171,560; g-file 3,240; g7 64; rank 8 12. The remaining states mate during P1.

## 6. Gaps
- **G-P1: closed in S019** (Lemmas RL-h, RL-f and P1).
- **G-P2: closed in S018** (Lemmas C and S).

**No gap remains.** Residual assumptions: A1; the kernel encoding (human review of `docs/RULES_KERNEL.md` still open); same-agent audits.

## 7. Planned Lean shape (after Gate L)
Lemmas M, E, W, C and S are schema-level: each is a move schema with a legality lemma over the kernel, and they generalise directly. P1 is the hard part to formalise. It needs a uniform argument, not a per-position certificate (charter: no lookup).
