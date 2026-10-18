# EC-C003 — King and knight versus king is a dead position (local proof, over the rules kernel)

**Status:** `LOCAL_VERIFIED` (Gate L, session S011). **Not** formally verified; **not** frozen. Separate audit: [audits/EC-C003_KNK.md](../audits/EC-C003_KNK.md).
**Rules:** FIDE Laws of Chess, effective 1 January 2023, as encoded in the rules kernel `formal/EndgameChess/Rules/` (bridge: [docs/RULES_KERNEL.md](../docs/RULES_KERNEL.md)).
**Depends on:** [EC-T0003](../theorems/frozen/EC-T0003/v1.md) (K vs K over the kernel, `Rules.dead_of_legal_into_KK`), frozen, for the branch where the knight has been captured.
**Attribution:** classical. K+N vs K is a standard example of insufficient mating material. Nothing here is novel.

---

## 0. Correction to the S011 prompt
The S011 prompt listed, as a fact "to be checked against the diagnostic before use": *if the knight checks the lone king `k`, then `k`'s diagonal neighbours are never attacked by the knight; its orthogonal neighbours may be.* **This is backwards.** A checking knight stands on the colour opposite to `k` and attacks only squares of the colour opposite to its own, i.e. squares of `k`'s colour. Diagonal neighbours of `k` share `k`'s colour, orthogonal neighbours do not. So a checking knight **never** attacks an orthogonal neighbour of `k`, and **can** attack a diagonal one (Nc4 checks Kb2 and also covers a3). The diagnostic confirms this: 0 orthogonal and 288 diagonal (knight, checked-king, neighbour) incidences on the 8×8 board. The proof below uses the corrected fact. With it, the argument is exactly the K+B vs K argument (EC-C002, lemma B2), and the corner worry in the prompt disappears: the strong king can cover the one diagonal neighbour of a corner, but not both orthogonal ones.

## 1. Rule text used (verbatim, FIDE 2023)

> **3.6** The knight may move to one of the squares nearest to that on which it stands but not on the same rank, file or diagonal.

Also used, as encoded in the kernel (`docs/RULES_KERNEL.md`): 1.2, 1.4.1, 3.1, 3.1.1, 3.1.2, 3.1.3, 3.8.1 (assumption A1: "adjoining" = Chebyshev distance 1), 3.8.2, 3.9.1, 3.9.2, 3.10.1, 3.10.3, 5.2.2.

## 2. Definitions (all in kernel terms)

- **Squares** `Fin 8 × Fin 8`, `(file, rank)`, a1 = (0,0). `d∞(s,t) = max(|Δx|,|Δy|)`. `col(x,y) = (x+y) mod 2`.
- **`knightGeom s t`** (Art. 3.6): `(|Δx|,|Δy|) ∈ {(1,2),(2,1)}`. The diagnostic checks, square by square, that these are exactly the nearest squares off the rank, file and diagonal.
- **`kingGeom s t`** (3.8.1): `d∞(s,t) = 1`.
- **Attack** (`attacksFrom`): a king attacks `t` iff `kingGeom`; a knight attacks `t` iff `knightGeom`. **Neither depends on the board** (no `pathClear`), so the attack sets of kings and knights are independent of occupancy.
- **`inCheck q c`**: some square holds the colour-`c` king and is attacked by a piece of colour `c̄`.
- **`Legal p q`** (3.10.1): `q = play p m` for some `m` with `isPseudo p m` and `¬inCheck (play p m) p.turn`.
- **`ReachK`, `MatedK`, `DeadK`** (kernel, `Rules/Lemmas.lean`): `ReachK` is the reflexive–transitive closure of `Legal` (length 0 included); `MatedK q` iff `inCheck q q.turn` and `q` has no legal successor; `DeadK p` iff no `q` with `ReachK p q` is `MatedK`.
- **`Arisen q`** (3.10.3): `ReachK initial q`.
- **`IsKNK q σ sk ns wk`** (new, analogous to `Rules.IsKBK`): `sk, ns, wk` pairwise distinct and `q.board = knkBoard σ sk ns wk`, the board with the colour-`σ` king on `sk`, the colour-`σ` knight on `ns`, the colour-`σ̄` king on `wk`, and nothing else. Castling rights, en-passant target and turn are **arbitrary**.
- **`IsKK q w b`** (existing): `w ≠ b`, board = White king on `w`, Black king on `b`, nothing else.
- Write `ω = σ̄` (the weak side), `K = sk`, `N = ns`, `k = wk`.

## 3. Lemmas

**N0 (last move legal ⇒ kings apart; strong side never in check).** If `Legal p q` and `IsKNK q σ K N k`, then
(a) `¬inCheck q p.turn`, and `p.turn = q.turn̄` (the side not to move in `q`);
(b) `d∞(K,k) ≥ 2`;
(c) `¬inCheck q σ`.

*Proof.*
(a) `legal_mover_safe` and `play_turn` (3.9.2, 1.2).
(b) `K ≠ k`, so `d∞ ≥ 1`. If `d∞(K,k) = 1`, each king attacks the other (`kingGeom` is symmetric), so **both** colours are in check in `q`, in particular the side not to move, contradicting (a).
(c) The only `ω` piece is the `ω` king. It attacks `K` iff `d∞(K,k) = 1`, excluded by (b). ∎

**N1 (knight geometry).** For all squares `s, t`:
(a) `knightGeom s t ⇒ col(t) ≠ col(s)`, since `|Δx|+|Δy| = 3` is odd.
(b) `knightGeom s t ⇒ d∞(s,t) = 2`; in particular a checking knight is never on, or adjacent to, the king it checks.
(c) If `knightGeom N k`, then the knight attacks no orthogonal neighbour of `k`. Let `|tx − kx| + |ty − ky| = 1`. Then `col(k) ≠ col(N)` by (a) and `col(t) ≠ col(k)` (the coordinate sum changes by 1). There are two colours, so `col(t) = col(N)`, and `¬knightGeom N t` by (a). (Directly: `|Δx|+|Δy|` from `N` to `t` is `3 ± 1`, even.)
(d) *(Not used; recorded because the prompt claimed otherwise.)* A checking knight may attack one diagonal neighbour of `k`; it attacks at most one neighbour of `k`. With `N − k = (1,2)`, the knight's targets inside `k + {−1,0,1}²` are `k` itself and `k + (−1,1)` only; the other seven offsets follow by the symmetries of §5.
(e) *(Not used.)* Two knight targets of one square are never orthogonally adjacent (they have the same colour), but can be diagonally adjacent (from a1: b3, c2). ∎

**N2 (key: a checked lone king always has a legal move).** Suppose `IsKNK q σ K N k`, `d∞(K,k) ≥ 2`, `q.turn = ω` and `inCheck q ω`. Then `q` has a legal successor; in particular `¬MatedK q`.

*Proof.*
1. **The checker is the knight.** The `σ` king does not attack `k` (`d∞ ≥ 2`). The only other `σ` piece is the knight, so `knightGeom N k`. (There is exactly one checker, so double check is impossible.)
2. **Two candidate squares.** Let `k = (a,b)`. Put `ε = +1` if `a = 0`, else `ε = −1`; `δ = +1` if `b = 0`, else `δ = −1`. Let `h = (a+ε, b)` and `v = (a, b+δ)`. Since the board has 8 > 1 files and ranks, `h` and `v` are on the board; both are orthogonal neighbours of `k`.
3. **The move `k → s`, `s ∈ {h,v}`, is pseudo-legal unless `s = K`.** The mover is the `ω` king on `k` with `q.turn = ω`; `kingGeom k s` holds; `targetOK q s` holds because `s ≠ K` is assumed below, `s ≠ N` (`d∞(N,k) = 2` by N1(b) but `d∞(s,k) = 1`) and `s ≠ k`, so `s` is empty. No promotion is involved.
4. **The resulting position.** `play q (k→s)` has the `ω` king on `s`, the `σ` king on `K`, the knight on `N`, nothing else. (No capture: `s` was empty. Castling and en passant are not triggered: castling needs the king to move two files and a rook; en passant needs a pawn.) In it, the `ω` king is in check iff `kingGeom K s` or `knightGeom N s` — attacks of kings and knights are board-independent, so vacating `k` changes nothing.
5. **The knight does not attack `s`**, by N1(c).
6. **The `σ` king cannot spoil both moves.** The move to `s` fails only if `s = K` or `kingGeom K s`, i.e. `d∞(K,s) ≤ 1`. If `d∞(K,h) ≤ 1` and `d∞(K,v) ≤ 1`, then `|Ky − b| ≤ 1` (from `h`, whose rank is `b`) and `|Kx − a| ≤ 1` (from `v`, whose file is `a`), so `d∞(K,k) ≤ 1`, contradicting the hypothesis.
7. Hence at least one of `k → h`, `k → v` is legal. ∎

*Remarks.*
- N2 does not use the knight's capture: the checking knight is never adjacent to `k` (N1(b)), so it cannot be taken by the escaping king. The diagnostic confirms that no checked lone king escapes by capture.
- N2 needs the check. Without it, stalemates occur (80 configurations across both orientations; e.g. `ω` Ka8, `σ` Kb6 + Nc6, `ω` to move). Stalemate is not checkmate.

**N3 (closure).** Let `C(r)` be: `∃ p, Legal p r`, and (`∃ σ K N k, IsKNK r σ K N k`) or (`∃ w b, IsKK r w b`). If `C(r)` and `Legal r r′`, then `C(r′)`.

*Proof.* The first conjunct holds for `r′` by the step itself. For material:
- **`r` is K vs K.** A legal move moves a king to an empty square (the only other piece is the enemy king, which `targetOK` forbids capturing); castling is impossible (no rook). So `r′` is K vs K, with the kings on distinct squares.
- **`r` is K+N vs K, the mover is `σ`.** The only `ω` piece is the king, which cannot be captured (1.4.1, `targetOK`). A king move or knight move to an empty square keeps the material; castling needs a rook; no pawns, so no promotion and no en passant. So `r′` is K+N vs K with three distinct squares (`play` overwrites only `dst` and clears `src`).
- **`r` is K+N vs K, the mover is `ω`.** The `ω` king moves to an empty square (material unchanged) or onto the knight's square, capturing it (3.1.1): then `r′` is K vs K. It cannot move onto `K`. No castling, promotion or en passant.
In each case the side colours are unchanged, so `r′` is K+N vs K of the same orientation `σ`, or K vs K. ∎

Flags. `IsKNK` and `IsKK` constrain only the board. A position with arbitrary castling rights and en-passant target but no rooks and no pawns behaves exactly as the flag-normalised one (`Rules.NRP`, `Rules.legal_normFlags_iff`, `Rules.deadK_normFlags_iff`, frozen with EC-T0003/4): castling needs a rook on its corner, en passant a pawn. The argument above never reads the flags, so it holds verbatim; in Lean the normalisation lemmas are available if convenient.

**N4 (no reachable checkmate).** If `C(q)` and `ReachK q r`, then `C(r)` (induction on the length of the path; length 0 is the hypothesis, the step is N3). And no `r` with `C(r)` is `MatedK`:
- **K vs K branch.** `r` was produced by a legal move and `IsKK r w b`, so `DeadK r` by **EC-T0003** (`Rules.dead_of_legal_into_KK`). Since `ReachK r r`, `¬MatedK r`.
- **K+N vs K branch, `σ` to move.** `σ` is not in check (N0(c)), so not `MatedK`.
- **K+N vs K branch, `ω` to move.** If `ω` is not in check, not `MatedK`. If it is, N0(b) gives `d∞(K,k) ≥ 2` and N2 gives a legal move. ∎

## 4. Theorem and rule corollary

**Theorem EC-C003 (kernel form).** If `Legal p q` and `IsKNK q σ K N k` (any `p`, any material in `p`, any flags, either `σ`), then `DeadK q`. Consequently every **arisen** K+N vs K position is dead.

*Proof.* `C(q)` holds. By N4, every `r` with `ReachK q r` satisfies `C(r)` and is not `MatedK`. So `DeadK q`.
For the arisen form: `initial` is not K+N vs K (it has 32 pieces, e.g. a pawn on a2), so a path from `initial` to `q` has positive length and its last step is a legal move into `q`. ∎

**Corollary (immediate draw).** Under the rule encoding `Rules.Rule5_2_2` (FIDE 5.2.2), every arisen K+N vs K position is an immediate draw: `Rule5_2_2 q .draw`.

**What this is not.** Not "no forced mate" (weaker). Not a stalemate claim: stalemates are reachable in the move graph (80 configurations), but by 5.2.2 the game has already ended when the K+N vs K position arose. Not a 50/75-move or repetition draw.

## 5. Symmetries
The proof of N2 is uniform in `k` (the choice of `ε, δ` handles corners and edges), so it needs **no** symmetry reduction. Symmetry is used only in the unused remark N1(d), to transfer the computation for `N − k = (1,2)` to the other seven knight offsets. The eight symmetries of the square (reflections in the files, ranks and the main diagonal, and their compositions) map `{(±1,±2),(±2,±1)}` to itself and `{−1,0,1}²` to itself, so they preserve both knight and king geometry. N1(d) is in any case verified exhaustively by the diagnostic.

## 6. Planned Lean statement (S012, Gate F)
New module `formal/EndgameChess/Rules/KNK.lean` (namespace `EndgameChess.Rules`), importing `Rules.Reach` (hence `Flags`, `AgreeKK`, `AgreeKBK`). No new bespoke move model.

```lean
def knkBoard (σ : Colour) (sk ns wk : Square) : Board := fun s =>
  if s = sk then some ⟨σ, .king⟩ else if s = ns then some ⟨σ, .knight⟩
  else if s = wk then some ⟨σ.opp, .king⟩ else none

def IsKNK (q : Position) (σ : Colour) (sk ns wk : Square) : Prop :=
  sk ≠ ns ∧ sk ≠ wk ∧ ns ≠ wk ∧ q.board = knkBoard σ sk ns wk

theorem dead_of_legal_into_KNK {p q : Position} {σ : Colour} {sk ns wk : Square}
    (hl : Legal p q) (hk : IsKNK q σ sk ns wk) : DeadK q

theorem arisen_KNK_dead {q : Position} {σ : Colour} {sk ns wk : Square}
    (ha : Arisen q) (hk : IsKNK q σ sk ns wk) : DeadK q

theorem knk_drawn_by_rule {q : Position} {σ : Colour} {sk ns wk : Square}
    (ha : Arisen q) (hk : IsKNK q σ sk ns wk) : Rule5_2_2 q .draw
```
Proof plan: N1 as `knightGeom` lemmas on `Int` offsets (`omega`); N2 by the `h`/`v` construction (not by enumeration); N3 by case analysis of `isPseudo` on a K+N vs K / K vs K board; N4 by induction on `ReachK`, discharging the K vs K branch with the frozen `dead_of_legal_into_KK`. `Rule5_2_2` lives in `Rules/Outcome.lean`; `knk_drawn_by_rule` goes in `KNK.lean` (which then imports `Outcome`), so no frozen module is edited.

## 7. Residual assumptions
1. A1 ("adjoining" = Chebyshev distance 1), as for EC-T0001–0004.
2. The kernel's encoding of 3.6 (`knightGeom`) and the rest of Article 3, subject to the still-open human review of `docs/RULES_KERNEL.md`.
3. The FIDE 2023 text as retrieved on 2026-10-16.
4. Prose dependence on the frozen EC-T0003 (`dead_of_legal_into_KK`) for the capture branch.
