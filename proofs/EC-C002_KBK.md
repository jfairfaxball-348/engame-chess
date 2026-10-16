# EC-C002 — King and bishop versus king is a dead position (local proof)

**Status:** `LOCAL_VERIFIED` (Gate L, session S004). **Not** formally verified; **not** frozen. Separate audit: [audits/EC-C002_KBK.md](../audits/EC-C002_KBK.md).
**Rules:** FIDE Laws of Chess, effective 1 January 2023, https://handbook.fide.com/chapter/E012023 (retrieved 2026-10-16).
**Depends on:** [EC-T0001](../theorems/frozen/EC-T0001/v1.md) (K vs K), frozen. Its lemmas L2, L3 and L3a are used for the branch where the bishop has been captured.
**Attribution:** classical. K+B vs K is a standard example of insufficient mating material. Nothing here is novel.

---

## 1. Rule text used (verbatim, in addition to those quoted in `proofs/EC-C001_KK.md` §1)

> **3.2** The bishop may move to any square along a diagonal on which it stands.
>
> **3.5** When making these moves, the bishop, rook or queen may not move over any intervening pieces.

Also used, quoted in EC-C001 §1: 1.2 (alternate moves), 1.4 / 1.4.1 (checkmate; capturing the king is not allowed), 3.1 / 3.1.1 / 3.1.2 / 3.1.3 (occupancy, capture, attack), 3.8 / 3.8.1 / 3.8.2 (king moves, castling), 3.9.1 / 3.9.2 (check), 3.10.1 (legal move), 5.2.2 (dead position).

## 2. Definitions

The board, `d∞` and `N(p)` are as in EC-C001. Assumption **A1** carries over: "adjoining square" means `N(p)`.

**Colours of the players.** One colour, `σ` (the *strong* side), has a king on `K` and a bishop on `X`. The other colour, `ω = σ̄` (the *weak* side), has only a king, on `k`. Either `σ = W` or `σ = B`. The argument never uses which, so it covers both orientations.

**KBK configuration.** `p = (K, X, k, t)` with `K, X, k` pairwise distinct and `t ∈ {σ, ω}` the side to move. The only pieces are these three. Castling and en-passant rights are vacuous: there are no rooks or pawns.

**Square colour.** `col(x,y) = (x + y) mod 2`. This is the light/dark colouring of Article 2.1.

**Diagonal and bishop attack.** `q` is on a diagonal of `X` iff `q ≠ X` and `|qx − Xx| = |qy − Xy|`. By 3.1.2–3.1.3, 3.2 and 3.5, the bishop on `X` attacks `q` iff `q` is on a diagonal of `X` and every square strictly between `X` and `q` on that diagonal is empty.

**King attack.** Unchanged (EC-C001 L1): a king on `s` attacks `q` iff `d∞(s,q) = 1`.

**InCheck(c, p)** (3.9.1): the colour-`c` king is attacked by some opposing piece.

**Legal move** (3.10.1): any move of the side to move that satisfies 3.1–3.9 and 1.4.1. `Legal(p)` is the set of resulting positions.

**LKBK(p)** (locally legal KBK configuration): `p` is a KBK configuration and `¬InCheck(t̄, p)`, i.e. the side *not* to move is not in check.

**AdmKK(q):** `q` is a two-king configuration with `d∞ ≥ 2` (EC-C001 "Admissible").

**Arisen(p):** `p` is reached from the standard initial position by a finite series of legal moves.

**Checkmate(c, p), Reach, Dead:** as in EC-C001, over the FIDE-legal move relation, with no stopping rule. `Reach` includes the length-0 path. `Dead(p)` means no `q` with `Reach(p,q)` is a checkmate of either colour.

## 3. Lemmas and proofs

**B0 (arisen ⇒ LKBK).** If `p` is a KBK configuration with `Arisen(p)`, then `LKBK(p)`.

*Proof.*
- Pieces occupy distinct squares (3.1, 3.1.1).
- The initial position has 32 pieces, so `p` was produced by a legal move made by the colour `t̄` (1.2).
- By 3.9.2, after that move the `t̄` king is not in check.
- Only the last move is used. The predecessor may have had more material, and the move may have been a capture or a promotion. ∎

**B0′ (kings never adjacent; the strong side is never in check).** If `LKBK(p)`, then `d∞(K,k) ≥ 2` and `¬InCheck(σ, p)`.

*Proof.*
- If `d∞(K,k) = 1`, each king attacks the other (L1, symmetry), so the side not to move is in check, contradicting LKBK. Since `K ≠ k`, we get `d∞(K,k) ≥ 2`.
- The only `ω` piece is the `ω` king. By L1 it attacks `K` iff `d∞(K,k) = 1`, which we just excluded. ∎

**B1 (colour complex).**
(a) The bishop on `X` attacks only squares `q` with `col(q) = col(X)`.
(b) If `q` and `q′` are orthogonal neighbours (they differ by exactly 1 in exactly one coordinate), then `col(q) ≠ col(q′)`.

*Proof.*
(a) On a diagonal `|qx − Xx| = |qy − Xy| = m`, so `qx + qy − (Xx + Xy) ∈ {0, ±2m}`, which is even. Obstruction (3.5) only removes squares from the attacked set.
(b) The coordinate sum changes by exactly 1. ∎

**B2 (the lone king always escapes a check).** If `LKBK(p)`, `t = ω` and `InCheck(ω, p)`, then `Legal(p) ≠ ∅`. In particular `¬Checkmate(ω, p)`.

*Proof.*
1. **The checker is the bishop.** By B0′ the `σ` king does not attack `k`, so the bishop does. By B1(a), `col(k) = col(X)`.
2. **Two candidate squares.** Let `k = (a, b)`. Set `ε = +1` if `a = 0` and `ε = −1` otherwise; set `δ = +1` if `b = 0` and `δ = −1` otherwise. Let `h = (a + ε, b)` and `v = (a, b + δ)`. Both are on the board (`F` has more than one element) and both lie in `N(k)`.
3. **When the move to `s ∈ {h, v}` is legal.** By 3.8.1, 3.1, 1.4.1 and 3.9.2, the `ω` king may move to `s` iff:
   - `s ≠ K` (no king capture);
   - `s` is not occupied by an own piece (vacuous);
   - after the move, `s` is attacked neither by the `σ` king nor by the bishop.
4. **The bishop is not a problem on `s`.**
   - By B1(b), `col(s) ≠ col(k) = col(X)`.
   - So `s ≠ X`, and the move is not a capture: the bishop stays on `X`.
   - By B1(a), the bishop does not attack `s` in the resulting position. B1(a) holds for every occupancy, so the vacated square `k` and any new line of sight are irrelevant.
5. **The only remaining obstruction is the `σ` king.** The move to `s` is illegal iff `d∞(K, s) ≤ 1`, where `d∞ = 0` covers `s = K` and `d∞ = 1` covers an attacked square.
6. **The `σ` king cannot cover both squares.** Suppose `d∞(K,h) ≤ 1` and `d∞(K,v) ≤ 1`.
   - From `h`: `|Ky − b| ≤ 1`.
   - From `v`: `|Kx − a| ≤ 1`.
   - Hence `d∞(K, k) ≤ 1`, contradicting B0′.
7. So at least one of the moves `k → h`, `k → v` is legal. ∎

*Remark.* B2 needs the check. Without it the bishop may stand on `k`'s opposite colour and cover `h` or `v`, and stalemates do occur. Example: `ω` king a8, `σ` king b6, bishop c7, `ω` to move. The diagnostic counts 272 stalemated configurations across both orientations. Stalemate is not checkmate and is irrelevant to `Dead`.

**B3 (step closure).** If `q ∈ Legal(p)` and `p ∈ LKBK ∪ AdmKK`, then `q ∈ LKBK ∪ AdmKK`.

*Proof.*
- **Case `p ∈ AdmKK`.** By EC-C001 L3a and L3 (frozen as EC-T0001), `q ∈ AdmKK`.
- **Case `p ∈ LKBK`, material.**
  - The `σ` pieces cannot capture: the only enemy piece is the `ω` king (1.4.1).
  - The `ω` king can capture only the bishop.
  - No other material change is possible: no castling (3.8.2 needs a rook), no promotion or en passant (no pawns).
  - So `q` is a KBK configuration (no capture) or a two-king configuration (the bishop was captured).
- **Case `p ∈ LKBK`, legality of `q`.**
  - By 3.9.2, the mover `t` is not in check in `q`, and `t` is the side not to move in `q`.
  - If `q` is KBK, this is exactly `LKBK(q)`.
  - If `q` is a two-king configuration, then `d∞ ≠ 1` (otherwise `t` would be in check) and `d∞ ≠ 0` (distinct squares), so `AdmKK(q)`. ∎

**B4 (path closure).** If `p ∈ LKBK ∪ AdmKK` and `Reach(p, q)`, then `q ∈ LKBK ∪ AdmKK`.

*Proof.* Induction on the path length. Length 0 holds by hypothesis; the step is B3. ∎

**B5 (no member of the class is checkmate).** If `q ∈ LKBK ∪ AdmKK`, then `q` is a checkmate of neither colour.

*Proof.*
- **`AdmKK`:** neither king is in check (EC-C001 L2), and checkmate requires check.
- **`LKBK`, `σ` to move:** `σ` is not in check (B0′). Also `ω` is not to move, so `Checkmate(ω, q)` fails by definition.
- **`LKBK`, `ω` to move:** if `ω` is not in check, it is not checkmate. If `ω` is in check, B2 gives a legal move. `Checkmate(σ, q)` fails because `σ` is not to move. ∎

## 4. Theorem and rule corollary

**Theorem EC-C002.** Every KBK configuration with `LKBK(p)` is `Dead`. In particular, every game-arisen KBK configuration is dead, in both orientations (White K+B vs Black K, and Black K+B vs White K).

*Proof.* B4 and B5 cover every `q` with `Reach(p, q)`, over all move choices of both players. Then apply B0. ∎

**Corollary (immediate draw).** If a game under FIDE 2023 reaches a KBK configuration by a move made in accordance with Article 3 and Articles 4.2–4.7, the game is drawn immediately by Article 5.2.2 (cf. 1.5).

As in EC-C001 §4, the series of moves quantified over in 5.2.2 is the counterfactual legal-move graph, with no stopping rule.

**What this is not.**
- It is not "no forced mate", which is weaker.
- It is not a stalemate result. Stalemates are reachable in this graph, but the game has already ended by 5.2.2 when the KBK position arises.
- It is not a repetition or 50/75-move draw.

## 5. Residual assumptions
1. A1, as for EC-C001.
2. The bishop-attack reading of 3.1.2 + 3.2 + 3.5: "along a diagonal", with obstruction by the first occupied square, which may itself be captured if it is an enemy piece. The kings are the only possible obstructions.
3. The FIDE 2023 text as retrieved on 2026-10-16.
4. `Arisen` means reached by legal moves from the standard initial position. Set-up positions are covered whenever `LKBK` holds.
