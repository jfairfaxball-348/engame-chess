# EC-C001 — King versus king is a dead position (local proof)

**Status:** `LOCAL_VERIFIED` (Gate L, session S001). **Not** formally verified; **not** frozen. See the separate audit [audits/EC-C001_KK.md](../audits/EC-C001_KK.md).
**Rules:** FIDE Laws of Chess, approved 07/08/2022, applied from 1 January 2023, https://handbook.fide.com/chapter/E012023 (page retrieved 2026-10-16; quotations below are verbatim from that retrieval).
**Attribution:** This is a classical, folklore fact of chess (K vs K is the textbook example of insufficient mating material). Nothing here is novel; the contribution is an explicit, quantifier-correct derivation from stated definitions.

---

## 1. Rule text used (verbatim)

> **1.2** The player with the light-coloured pieces (White) makes the first move, then the players move alternately, with the player with the dark-coloured pieces (Black) making the next move.
>
> **1.4** The objective of each player is to place the opponent's king 'under attack' in such a way that the opponent has no legal move.
> **1.4.1** The player who achieves this goal is said to have 'checkmated' the opponent's king and to have won the game. Leaving one's own king under attack, exposing one's own king to attack and also 'capturing' the opponent's king is not allowed.
>
> **1.5** If the position is such that neither player can possibly checkmate the opponent's king, the game is drawn (see Article 5.2.2).
>
> **3.1** It is not permitted to move a piece to a square occupied by a piece of the same colour.
> **3.1.1** If a piece moves to a square occupied by an opponent's piece the latter is captured and removed from the chessboard as part of the same move.
> **3.1.2** A piece is said to attack an opponent's piece if the piece could make a capture on that square according to Articles 3.2 to 3.8.
> **3.1.3** A piece is considered to attack a square even if this piece is constrained from moving to that square because it would then leave or place the king of its own colour under attack.
>
> **3.8** There are two different ways of moving the king:
> **3.8.1** by moving to an adjoining square
> **3.8.2** by 'castling'. This is a move of the king and either rook of the same colour along the player's first rank, […]
>
> **3.9.1** The king is said to be 'in check' if it is attacked by one or more of the opponent's pieces, even if such pieces are constrained from moving to the square occupied by the king because they would then leave or place their own king in check.
> **3.9.2** No piece can be moved that will either expose the king of the same colour to check or leave that king in check.
>
> **3.10.1** A move is legal when all the relevant requirements of Articles 3.1 – 3.9 have been fulfilled.
> **3.10.3** A position is illegal when it cannot have been reached by any series of legal moves.
>
> **5.1.1** The game is won by the player who has checkmated his/her opponent's king. This immediately ends the game, provided that the move producing the checkmate position was in accordance with Article 3 and Articles 4.2 – 4.7.
> **5.2.1** The game is drawn when the player to move has no legal move and his/her king is not in check. The game is said to end in 'stalemate'. […]
> **5.2.2** The game is drawn when a position has arisen in which neither player can checkmate the opponent's king with any series of legal moves. The game is said to end in a 'dead position'. This immediately ends the game, provided that the move producing the position was in accordance with Article 3 and Articles 4.2 – 4.7.

Note on the 2023 text: Article 3.8.1 does **not** itself say "not attacked". The prohibition on a king stepping next to the other king therefore comes from 3.9.2 together with the attack definition 3.1.2–3.1.3, and is derived below rather than stipulated.

## 2. Definitions

**Board.** `F = {0,…,7}`, `S = F×F`. `d∞((x,y),(u,v)) = max(|x−u|,|y−v|)`. `N(p) = {q ∈ S : d∞(p,q)=1}`.

**Assumption A1 (reading of "adjoining").** The adjoining squares of `p` in 3.8.1 are exactly `N(p)`: the up to eight orthogonal/diagonal neighbours that lie on the board.

**KK configuration.** `p = (w,b,t)`, `w,b ∈ S`, `t ∈ {W,B}`, kings only. `K_W(p)=w`, `K_B(p)=b`; `c̄` is the colour opposite to `c`.

**Admissible(p)** :⇔ `d∞(w,b) ≥ 2`.

**Arisen(p)** :⇔ the position is reached from the standard initial position by a finite series of moves each legal by 3.10.1 (and, for the rule corollary only, made in accordance with 4.2–4.7).

**Attack (kings).** `KAtt(s,q)` :⇔ a king on `s` attacks square `q`.

**InCheck(c,p)** :⇔ the colour-`c` king is attacked by some piece of colour `c̄` in `p`.

**LegalKK(p,q)** for `p=(w,b,t)`: there is `s` with (i) `s ∈ N(K_t(p))`, (ii) `s ≠ K_t̄(p)`, (iii) `d∞(s, K_t̄(p)) ≥ 2`, and `q` equals `p` with `K_t` set to `s` and turn `t̄`. (Lemma L3a shows this is exactly the FIDE-legal move relation on KK configurations.)

**Checkmate(c,p)** :⇔ `t = c` ∧ `InCheck(c,p)` ∧ `¬∃q. LegalKK(p,q)`.

**Reach(p,q)** :⇔ ∃ `n ≥ 0` and `p₀,…,pₙ` with `p₀ = p`, `pₙ = q`, `LegalKK(pᵢ,pᵢ₊₁)` for all `i < n`. No stopping rule is applied (§4).

**Dead(p)** :⇔ `¬∃q. Reach(p,q) ∧ (Checkmate(W,q) ∨ Checkmate(B,q))`.

## 3. Lemmas and proofs

**L1 (king attack is Chebyshev adjacency).** For all `s,q ∈ S`: `KAtt(s,q) ⇔ d∞(s,q) = 1`.

*Proof.* By 3.1.2–3.1.3 a king on `s` attacks `q` iff it could capture on `q` by some move of Article 3.8, ignoring whether that move would expose its own king. Castling (3.8.2) moves the king two squares onto a square that must be empty (3.8.2.2 (4) requires no pieces between king and rook, and the king's target lies between them), so castling never captures; in any case it requires a rook, absent here. A 3.8.1 move goes to an adjoining square, i.e. (A1) to `q ∈ N(s)`, and is a capture exactly when `q` holds an opposing piece. Hence the attacked squares are exactly `N(s)`, i.e. `d∞(s,q)=1`. The board edge is handled by the definition of `N` (only on-board squares). ∎

**L2 (no check in admissible configurations).** If `Admissible(p)` then `¬InCheck(W,p)` and `¬InCheck(B,p)`.

*Proof.* The only piece of colour `c̄` is the `c̄` king. By L1 it attacks the `c` king iff `d∞(w,b) = 1`. Admissibility gives `d∞(w,b) ≥ 2 ≠ 1`. ∎

*Corollary L2′.* For any KK configuration, `InCheck(W,p) ⇔ InCheck(B,p) ⇔ d∞(w,b)=1` (symmetry of `d∞`).

**L0 (arisen ⇒ admissible).** If `Arisen(p)` for a KK configuration `p`, then `Admissible(p)`.

*Proof.* `w ≠ b` since two pieces never share a square (3.1, 3.1.1: a move onto an occupied square removes the occupant), so `d∞(w,b) ≥ 1`. The initial position has 32 pieces, so `p` is not it; hence `p` was produced by a legal move `m` made by some colour `X` (by 1.2, `X = t̄`). By 3.9.2, after `m` the `X` king is not in check. The only opposing piece in `p` is the other king, so by L2′ `d∞(w,b) ≠ 1`. Hence `d∞(w,b) ≥ 2`. ∎

*Remark.* L0 uses only the last move, not the history; it holds for every position (not just the first KK position) of a legally played game.

**L3a (the legal moves of a KK configuration are exactly `LegalKK`).** For a KK configuration `p`, a move is FIDE-legal (3.10.1, with 1.2 and 1.4.1) iff it is described by `LegalKK(p,·)`.

*Proof.* By 1.2 only the side to move `t` moves. Its only piece is its king. Articles 3.2–3.7 concern other piece types and are vacuous. By 3.8 the king either castles — impossible, no rook (3.8.2) — or moves to `s ∈ N(K_t)` (3.8.1, A1): condition (i). 3.1 forbids `s` occupied by an own piece: vacuous (no other own piece). If `s = K_t̄` the move would capture the king, forbidden by 1.4.1: condition (ii). (Independently, (iii) also excludes it, since `d∞(K_t̄,K_t̄)=0`.) By 3.9.2 the resulting position must not have the `t` king in check; in the resulting position the only opposing piece is the `t̄` king on `K_t̄` (no capture occurred), so by L1 this is `d∞(s,K_t̄) ≠ 1`, which given (ii) is `d∞(s,K_t̄) ≥ 2`: condition (iii). The resulting position has `K_t = s`, the other king unmoved, turn `t̄` (1.2). Conversely any `s` with (i)–(iii) satisfies all of 3.1–3.9 that apply. ∎

**L3 (one-step closure).** If `LegalKK(p,q)` then `q` is a KK configuration (exactly two kings, one of each colour), `Admissible(q)`, and the turn of `q` is the opposite of that of `p`.

*Proof.* No capture occurs (condition (ii); there is no other piece), so the material is still exactly the two kings. Exactly one king moved; in `q`, `d∞(K_W(q),K_B(q)) = d∞(s,K_t̄(p)) ≥ 2` by (iii). The turn flips by definition. ∎

Note that L3 does **not** need `Admissible(p)`: closure is unconditional. Admissibility of the start is needed only for the zero-length path.

**L4 (finite-path closure).** If `Admissible(p)` and `Reach(p,q)`, then `Admissible(q)`.

*Proof.* Induction on the path length `n`. `n = 0`: `q = p`, admissible by hypothesis. `n → n+1`: `pₙ` is admissible by the induction hypothesis (in fact any KK configuration suffices) and `LegalKK(pₙ,pₙ₊₁)`, so `pₙ₊₁` is admissible by L3. ∎

**L5 (no reachable checkmate).** If `Admissible(p)` and `Reach(p,q)`, then `¬Checkmate(W,q)` and `¬Checkmate(B,q)`.

*Proof.* By L4, `Admissible(q)`; by L2, neither king is in check in `q`. `Checkmate(c,q)` requires `InCheck(c,q)`. ∎

This needs no information about whether legal moves exist in `q`; stalemates (if any) are irrelevant to `Dead`. (Remark R1 shows none exist anyway.)

**L6 (quantifier step).** If `Admissible(p)` then `Dead(p)`.

*Proof.* `Dead(p)` asserts that for **every** `q` and **every** finite path from `p` to `q`, `q` is not a checkmate of either colour. L5 proves exactly this universal statement; it ranges over all move choices of both players, including cooperative play. ∎

## 4. Main theorem and rule corollary

**Theorem EC-C001.** Every KK configuration with `Admissible(p)` satisfies `Dead(p)`. In particular every KK configuration with `Arisen(p)` satisfies `Dead(p)`.

*Proof.* L6, and L0 for the second sentence. ∎

**Interpretation of 5.2.2.** "Neither player can checkmate the opponent's king with any series of legal moves" is read as: there is no finite series of legal moves (3.10.1), made alternately (1.2) from the given position, after which some player's opponent is checkmated (1.4, 1.4.1). Formally that is `Dead(p)` over the relation `LegalKK`, using L3a for the identification of legal moves.

**Why a counterfactual graph.** By 5.2.2 the game already ended when `p` arose, so the "series of legal moves" is never played. It is nevertheless well defined: legality (3.10.1) is a condition on a position and a move given by Articles 3.1–3.9 only, independent of whether Article 5 has terminated the game. `Reach` therefore uses `LegalKK` with *no* stopping rule. Using a stopping rule would be circular (we would need to know which positions are dead to define the paths that decide deadness); we avoid that.

**Corollary (immediate draw).** Suppose a game played under FIDE 2023 reaches a KK configuration `p` by a move made in accordance with Article 3 and Articles 4.2–4.7. Then the game is drawn, and ends immediately, by Article 5.2.2 (cf. 1.5).

*Proof.* `Arisen(p)`, so `Dead(p)` by the theorem, so the 5.2.2 condition holds at the moment `p` arises. Competing terminations by the same move: 5.1.1 would need `p` to be checkmate, impossible by L2/L0; 5.2.1 (stalemate) also gives a draw and is in any case excluded by R1. ∎

**What this is not.** It is not a repetition, 50-move or 75-move draw, not a draw by agreement, and not "nobody can *force* mate" (which is weaker: `Dead` excludes even cooperative mates). Flag-fall (6.9) and resignation (5.1.2) also yield a draw in such a position, by their own clauses, but those are separate layers not used here.

## 5. Remarks (proved, not needed for the theorem)

**R1 (no stalemate; every admissible configuration has a legal move).** Let `p` be admissible, mover's king on `(x,y)`, other king on `(u,v)`. Since `d∞ ≥ 2`, either `|x−u| ≥ 2` or `|y−v| ≥ 2`. If `|x−u| ≥ 2`, pick `y' ∈ {y−1, y+1} ∩ F` (non-empty, as `F` has 8 elements); `s = (x,y')` is in `N((x,y))`, and `d∞(s,(u,v)) ≥ |x−u| ≥ 2`, so `s ≠ (u,v)` and (i)–(iii) hold. The case `|y−v| ≥ 2` is symmetric (vary `x`). ∎

**R2.** The diagnostic enumeration (audit §3) agrees: 7224 admissible configurations, 0 checks, 0 checkmates, 0 stalemates, 0 configurations without a legal move. This is supplementary evidence only.

## 6. Residual assumptions (explicit)
1. **A1**: "adjoining square" = Chebyshev neighbour on the board.
2. The FIDE text quoted is the 2023 edition as retrieved on 2026-10-16; later editions must be re-checked.
3. "Arisen" means reached from the standard initial position by legal moves; arbiter corrections of illegal moves (Art. 7) and composed/set-up positions are outside scope (for those, the theorem's admissible-form statement still applies whenever `d∞ ≥ 2`).
4. Articles 4.2–4.7 compliance of the producing move is a hypothesis of the rule corollary only, not of the mathematical theorem.
