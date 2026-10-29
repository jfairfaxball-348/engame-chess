import EndgameChess.Rules.KPK.RookPawn

/-! Small controls instantiate general proofs; they are not an outcome table. -/
namespace EndgameChess.Rules.KPK
open EndgameChess.KK

theorem white_checking_promotion_example :
    FreshGame.ActualWin .white (FreshGame.fresh (pos .white (4,5) (3,6) (7,7) .white)) := by
  let q := pos .white (4,5) (3,6) (7,7) .white
  have h : IsKPK q .white (4,5) (3,6) (7,7) := ⟨by decide, by decide, by decide, rfl⟩
  have fresh : FreshLegal q (4,5) (3,6) (7,7) :=
    ⟨rfl, rfl, by decide, by decide, by decide, by decide⟩
  apply fresh_checking_queen_actual_win h fresh rfl (t := (3,7))
  · exact ⟨by decide, by decide, Or.inl (by decide)⟩
  · rfl
  · exact Or.inl (by decide)
  · unfold KQK.QueenSees RookLine; decide

theorem black_checking_promotion_example :
    FreshGame.ActualWin .black (FreshGame.fresh (pos .black (4,2) (3,1) (7,0) .black)) := by
  let q := pos .black (4,2) (3,1) (7,0) .black
  have h : IsKPK q .black (4,2) (3,1) (7,0) := ⟨by decide, by decide, by decide, rfl⟩
  have fresh : FreshLegal q (4,2) (3,1) (7,0) :=
    ⟨rfl, rfl, by decide, by decide, by decide, by decide⟩
  apply fresh_checking_queen_actual_win h fresh rfl (t := (3,0))
  · exact ⟨by decide, by decide, Or.inl (by decide)⟩
  · rfl
  · exact Or.inl (by decide)
  · unfold KQK.QueenSees RookLine; decide

theorem double_push_example :
    isLegal (pos .white (7,0) (0,1) (7,7) .white) ⟨(0,1), (0,3), none⟩ = true ∧
      (play (pos .white (7,0) (0,1) (7,7) .white) ⟨(0,1), (0,3), none⟩).ep = some (0,2) := by
  constructor <;> decide

theorem blocked_double_push_example :
    isLegal (pos .white (0,2) (0,1) (7,7) .white) ⟨(0,1), (0,3), none⟩ = false := by decide

theorem unsafe_pawn_draw_example :
    let q := pos .white (7,0) (4,3) (4,4) .black
    FreshGame.Hold .white (FreshGame.fresh q) ∧ FreshGame.Hold .black (FreshGame.fresh q) := by
  let q := pos .white (7,0) (4,3) (4,4) .black
  have h : IsKPK q .white (7,0) (4,3) (4,4) := ⟨by decide, by decide, by decide, rfl⟩
  have fresh : FreshLegal q (7,0) (4,3) (4,4) :=
    ⟨rfl, rfl, by decide, by decide, by decide, by decide⟩
  exact fresh_unsafe_draw h fresh rfl (by unfold LoneKing.Safe; decide)

theorem rook_corner_both_turns_example (turn : Colour) :
    let q := pos .white (2,4) (0,2) (0,7) turn
    FreshGame.Hold .white (FreshGame.fresh q) ∧ FreshGame.Hold .black (FreshGame.fresh q) := by
  let q := pos .white (2,4) (0,2) (0,7) turn
  have h : IsKPK q .white (2,4) (0,2) (0,7) := ⟨by decide, by decide, by decide, rfl⟩
  have fresh : FreshLegal q (2,4) (0,2) (0,7) :=
    ⟨rfl, rfl, by decide, by decide, by decide, by cases turn <;> decide⟩
  exact fresh_rook_corner_draw h fresh (Or.inl rfl) rfl

theorem black_rook_corner_both_turns_example (turn : Colour) :
    let q := pos .black (5,3) (7,5) (7,0) turn
    FreshGame.Hold .black (FreshGame.fresh q) ∧ FreshGame.Hold .white (FreshGame.fresh q) := by
  let q := pos .black (5,3) (7,5) (7,0) turn
  have h : IsKPK q .black (5,3) (7,5) (7,0) := ⟨by decide, by decide, by decide, rfl⟩
  have fresh : FreshLegal q (5,3) (7,5) (7,0) :=
    ⟨rfl, rfl, by decide, by decide, by decide, by cases turn <;> decide⟩
  exact fresh_rook_corner_draw h fresh (Or.inr rfl) rfl

theorem protected_corner_stalemate_example :
    ¬ MatedK (pos .white (1,5) (0,6) (0,7) .black) ∧
      ¬ ∃ r, Legal (pos .white (1,5) (0,6) (0,7) .black) r := by
  let q := pos .white (1,5) (0,6) (0,7) .black
  have h : IsKPK q .white (1,5) (0,6) (0,7) := ⟨by decide, by decide, by decide, rfl⟩
  exact ⟨not_mated h (by decide), corner_protected_no_moves h rfl (by decide)
    ⟨rfl, Or.inl rfl, rfl, rfl⟩ (by decide)⟩

theorem minor_promotion_dead_example :
    let q := pos .white (4,5) (3,6) (7,7) .white
    DeadK (play q (promote (3,6) (3,7) .bishop)) ∧
      DeadK (play q (promote (3,6) (3,7) .knight)) := by
  let q := pos .white (4,5) (3,6) (7,7) .white
  have h : IsKPK q .white (4,5) (3,6) (7,7) := ⟨by decide, by decide, by decide, rfl⟩
  exact minor_promotion_dead h rfl (by decide)
    ⟨by decide, by decide, Or.inl (by decide)⟩ rfl

end EndgameChess.Rules.KPK
