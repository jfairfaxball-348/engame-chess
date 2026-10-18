# EC-C007 — Dead K+R vs K positions: forced rook capture or stalemate (local proof, over the rules kernel)

**Status:** `LOCAL_VERIFIED` (Gate L, session S014). Not formally verified; not frozen. Audit: [audits/EC-C007_KRK_DEAD.md](../audits/EC-C007_KRK_DEAD.md).
**Rules:** FIDE Laws of Chess 2023 as encoded in the rules kernel `formal/EndgameChess/Rules/` (bridge [docs/RULES_KERNEL.md](../docs/RULES_KERNEL.md)).
**Depends on:** [EC-T0003](../theorems/frozen/EC-T0003/v1.md) (`Rules.dead_of_legal_into_KK`).
**Attribution:** classical in spirit. That a position with a rook on the board can be dead (for example when the lone king's only legal move takes the rook) is folklore among arbiters and problemists. Nothing here is claimed as novel.
**Companion:** the converse is the separate candidate **EC-C008** (`PROPOSED`; see §6).

---

## 1. Why this rung starts here
Roadmap rung 4 asks whether the strong side can **force** mate with K+R vs K. The charter separates "no possible mate", "no forced mate" and "draw under the rules". The first question is therefore **possible** mate (`¬DeadK`), and it is not trivially "always". Some K+R vs K positions are dead, so under Art. 5.2.2 they are drawn on the spot although a rook is on the board.

## 2. Definitions (kernel terms)
`Legal`, `ReachK` (reflexive–transitive closure, length 0 included), `MatedK q` (the side to move is in check and has no legal move), `DeadK q` (no `r` with `ReachK q r` is `MatedK`), `Arisen`, `IsKK`, `Rule5_2_2`: as in `Rules/` and [proofs/EC-C003_KNK.md](EC-C003_KNK.md) §2.
**`IsKRK q σ sk rs wk`** (new, analogous to `IsKNK`): `sk, rs, wk` pairwise distinct and `q.board` holds exactly the colour-`σ` king on `sk`, the colour-`σ` rook on `rs` and the colour-`σ̄` king on `wk`. Turn, castling rights and en-passant target are arbitrary.

## 3. A material-agnostic lemma

**D1 (one-step deadness).** If `¬MatedK q` and every `r` with `Legal q r` satisfies `DeadK r`, then `DeadK q`.

*Proof.* Let `ReachK q t` with `MatedK t`. A `ReachK` path either has length 0, so `t = q`, which contradicts `¬MatedK q`; or it starts with a legal move `q → r` followed by a path `ReachK r t` (head decomposition of the tail-inductive `ReachK`, by induction on the path). Then `DeadK r` is contradicted by `t`. ∎

**D2 (all moves lead to K vs K).** If `¬MatedK q` and every legal successor of `q` is a two-king position (`∃ w b, IsKK r w b`), then `DeadK q`.

*Proof.* Each such `r` was produced by a legal move (from `q`), so `DeadK r` by EC-T0003 (`dead_of_legal_into_KK`). Apply D1. ∎

D1 and D2 hold whatever the material of `q`, its flags or how it arose. If `q` has no legal move at all, the hypothesis on successors is vacuous: a position with no legal move that is not checkmate (a stalemate) is dead. That is consistent with `DeadK`, which only asks whether a mate is reachable.

## 4. Theorem EC-C007

**Theorem.** Let `IsKRK q σ sk rs wk` with `q.turn = σ̄` (the lone king to move). Suppose `q` is not checkmate and every legal move of `q` captures the rook, i.e. every legal successor is a two-king position; this includes the case of no legal move at all. Then `DeadK q`. If moreover `q` has arisen, then `Rule5_2_2 q draw`: the game is drawn immediately.

*Proof.*
- Every legal move of `q` is a move of the lone king, the only `σ̄` piece. Castling needs a `σ̄` rook; en passant and promotion need pawns. So a legal move either goes to an empty square (material unchanged, K+R vs K) or captures the rook (`IsKK`). The hypothesis says only the second kind occurs.
- Apply D2. The corollary is the definition of `Rule5_2_2`. ∎

**Remarks.**
- No legality of the last move is needed for `DeadK`. The rook-capture hypothesis and `¬MatedK q` suffice. For a position produced by a legal move, `¬MatedK q` fails exactly when `q` is checkmate.
- **The hypothesis is satisfiable** (checked by the diagnostic and, in S015, by `decide`):
  - *forced capture:* Black Ka1, White Rb2, White Kh8, Black to move. Black is not in check; a2 and b1 are covered by the rook; b2 is unprotected. The only legal move is Kxb2. This position is produced by a legal move, e.g. Rb3–b2 with White to move.
  - *forced capture with check:* the diagnostic counts 412 forced-capture states per orientation, some of them in check.
  - *stalemate:* Black Ka1, White Rb2, White Kc3, Black to move. No legal move, no check.
- **The theorem is not vacuous in the other direction either.** Positions with a rook capture available but also another legal move are not covered, and EC-C008 conjectures they are live.

## 5. Computational evidence (supplementary; `scripts/krk_diagnostic.py`)
Each orientation has 399,112 legal K+R vs K states (side not to move not in check). Of these, 216 are checkmates and 68 stalemates. There are 412 forced rook captures (weak side to move, ≥ 1 legal move, all of them capturing the rook). A cooperative-reachability fixpoint over the script's own move graph finds exactly **480 dead states, all with the weak side to move**. These are precisely the 68 + 412 states of the EC-C007 hypothesis: **0 mismatches** against the full characterisation (EC-C007 together with EC-C008). The figures are identical for both orientations. Mutation: with a bishop in place of the rook, 417,068 mismatches. Supplementary only.

## 6. The converse (candidate EC-C008, `PROPOSED`)
**EC-C008.** Let `q` be produced by a legal move, with `IsKRK q σ sk rs wk`.
- (a) If `q.turn = σ` (the strong side to move), then `¬DeadK q`.
- (b) If `q.turn = σ̄`, then `DeadK q` iff `q` is not checkmate and every legal move captures the rook.

(b) "⇐" is EC-C007. (b) "⇒" follows from (a): a non-capturing legal move of the lone king leads to a K+R vs K position with the strong side to move, produced by a legal move; and a checkmate is not dead. So everything rests on (a), and the diagnostic finds it true for every strong-to-move state in both orientations (`dead_strong_to_move = 0`).
**What a proof of (a) needs:** an explicit cooperative mating route from every strong-to-move K+R vs K position, in which both sides cooperate and every move is legal. The route must never pass through a stalemate or forced capture, and must handle the rook being shielded by its own king, castling flags (which only add strong-side moves and can be ignored) and all symmetries. A candidate route:
1. the rook goes to the corner farthest from the lone king (≤ 2 rook moves, never giving check);
2. the lone king walks to the near corner;
3. the strong king takes the opposition two squares away;
4. a rook tempo fixes the parity;
5. the rook mates along the edge.

Each phase needs a legality lemma. This is the next research step after EC-C007 is formalised and frozen.

## 7. Planned Lean statement (S015, Gate F)
New module `formal/EndgameChess/Rules/KRK.lean`:
```lean
def krkBoard (σ : Colour) (sk rs wk : Square) : Board := ...   -- as knkBoard, rook for knight
def IsKRK (q : Position) (σ : Colour) (sk rs wk : Square) : Prop := ...

theorem reachK_head {q t : Position} (h : ReachK q t) : t = q ∨ ∃ r, Legal q r ∧ ReachK r t
theorem dead_of_succ_dead {q : Position} (hm : ¬ MatedK q) (h : ∀ r, Legal q r → DeadK r) : DeadK q
theorem dead_of_succ_KK {q : Position} (hm : ¬ MatedK q) (h : ∀ r, Legal q r → ∃ w b, IsKK r w b) : DeadK q
theorem krk_dead_of_forced_capture {q : Position} {σ : Colour} {sk rs wk : Square}
    (hk : IsKRK q σ sk rs wk) (hm : ¬ MatedK q) (h : ∀ r, Legal q r → ∃ w b, IsKK r w b) : DeadK q
theorem krk_forced_capture_drawn_by_rule ... (ha : Arisen q) ... : Rule5_2_2 q .draw
-- non-vacuity by decide: the Ka1/Rb2/Kh8 position (unique legal move Kxb2, produced by Rb3-b2) and the Ka1/Rb2/Kc3 stalemate.
```
`IsKRK` is only needed for the statement's readability. `dead_of_succ_KK` is the real content, and it needs no new move-model facts.

## 8. Residual assumptions
A1; the kernel encoding (human review of `docs/RULES_KERNEL.md` still open); the reading of 5.2.2 in `Rule5_2_2`; dependence on the frozen EC-T0003.
