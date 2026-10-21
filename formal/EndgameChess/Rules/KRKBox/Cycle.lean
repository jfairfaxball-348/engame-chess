import EndgameChess.Rules.KRKBox.Cost

namespace EndgameChess.Rules
open EndgameChess.KK

private def bs (x y : Fin 8) : Square := (x,y)
private def bm (x y u v : Fin 8) : Move := ⟨bs x y, bs u v, none⟩
private def start : Position := krkPos .white (bs 2 2) (bs 3 3) (bs 4 4) .white
private def moves : List Move :=
  [bm 2 2 3 2, bm 4 4 4 5, bm 3 3 4 3, bm 4 5 3 4,
   bm 3 2 4 2, bm 3 4 2 4, bm 4 2 5 2, bm 2 4 3 4,
   bm 5 2 4 2, bm 3 4 3 5, bm 4 3 3 3, bm 3 5 4 4,
   bm 4 2 3 2, bm 4 4 5 4, bm 3 2 2 2, bm 5 4 4 4]
private def cycleAt (n : Nat) : Position := (moves.take n).foldl play start

set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

/-- A sixteen-ply kernel cycle defeats the naive width-four extension only.
Flags and board return exactly; no infinite RAW history is claimed. -/
theorem krk_width_four_escort_cycle :
    (∀ n, n < 16 → ∃ m, moves[n]? = some m ∧ isLegal (cycleAt n) m = true) ∧
    cycleAt 16 = start := by
  constructor
  · have h : ∀ n ∈ List.range 16, ∃ m, moves[n]? = some m ∧ isLegal (cycleAt n) m = true := by decide
    intro n hn
    exact h n (List.mem_range.mpr hn)
  · have eqp (p q : Position) (hb : p.board = q.board) (ht : p.turn = q.turn)
        (hc : p.castling = q.castling) (he : p.ep = q.ep) : p = q := by
      cases p; cases q; cases hb; cases ht; cases hc; cases he; rfl
    apply eqp
    · funext s
      have h : ∀ s ∈ allSquares, (cycleAt 16).board s = start.board s := by decide
      exact h s (mem_allSquares s)
    all_goals decide

end EndgameChess.Rules
