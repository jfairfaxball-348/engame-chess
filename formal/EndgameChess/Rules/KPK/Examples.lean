import EndgameChess.Rules.KPK.RookPawn
import EndgameChess.Rules.KPK.SeventhKingOutcome
import EndgameChess.Rules.KPK.KeySquares

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

theorem supported_white_both_turns_example (turn : Colour) :
    FreshGame.ActualWin .white (FreshGame.fresh (pos .white (4,6) (3,6) (0,0) turn)) := by
  let q := pos .white (4,6) (3,6) (0,0) turn
  have h : IsKPK q .white (4,6) (3,6) (0,0) := ⟨by decide, by decide, by decide, rfl⟩
  have fresh : FreshLegal q (4,6) (3,6) (0,0) :=
    ⟨rfl, rfl, by decide, by decide, by decide, by cases turn <;> decide⟩
  exact fresh_supported_win h fresh ⟨rfl, rfl, by decide⟩

theorem supported_black_both_turns_example (turn : Colour) :
    FreshGame.ActualWin .black (FreshGame.fresh (pos .black (4,1) (3,1) (0,7) turn)) := by
  let q := pos .black (4,1) (3,1) (0,7) turn
  have h : IsKPK q .black (4,1) (3,1) (0,7) := ⟨by decide, by decide, by decide, rfl⟩
  have fresh : FreshLegal q (4,1) (3,1) (0,7) :=
    ⟨rfl, rfl, by decide, by decide, by decide, by cases turn <;> decide⟩
  exact fresh_supported_win h fresh ⟨rfl, rfl, by decide⟩

/-- The same board wins with the pawn side to move and is dead with the defender to move. -/
theorem sixth_pawn_tempo_example :
    FreshGame.ActualWin .white (FreshGame.fresh (pos .white (2,6) (1,5) (0,7) .white)) ∧
      DeadK (pos .white (2,6) (1,5) (0,7) .black) ∧
      FreshGame.Hold .black (FreshGame.fresh (pos .white (2,6) (1,5) (0,7) .black)) := by
  have h (turn : Colour) : IsKPK (pos .white (2,6) (1,5) (0,7) turn) .white (2,6) (1,5) (0,7) :=
    ⟨by decide, by decide, by decide, rfl⟩
  have fresh (turn : Colour) : FreshLegal (pos .white (2,6) (1,5) (0,7) turn) (2,6) (1,5) (0,7) :=
    ⟨rfl, rfl, by decide, by decide, by decide, by cases turn <;> decide⟩
  have band : SeventhKing .white (2,6) (1,5) := ⟨rfl, rfl, by decide⟩
  have losing : ¬ SeventhKingWins .white (pos .white (2,6) (1,5) (0,7) .black) (1,5) (0,7) := by
    rintro (wrong | notCorner)
    · cases wrong
    · exact notCorner ⟨rfl, Or.inl rfl, by decide⟩
  have classification := fresh_seventh_king_wdl50 (h .black) (fresh .black) band
  exact ⟨(fresh_seventh_king_wdl50 (h .white) (fresh .white) band).1.mpr (Or.inl rfl),
    classification.2.2.2.mpr losing, (classification.2.2.1.mpr losing).2⟩

theorem black_sixth_pawn_stalemate_example :
    DeadK (pos .black (5,1) (6,2) (7,0) .white) ∧
      FreshGame.Hold .white (FreshGame.fresh (pos .black (5,1) (6,2) (7,0) .white)) := by
  let q := pos .black (5,1) (6,2) (7,0) .white
  have h : IsKPK q .black (5,1) (6,2) (7,0) := ⟨by decide, by decide, by decide, rfl⟩
  have fresh : FreshLegal q (5,1) (6,2) (7,0) :=
    ⟨rfl, rfl, by decide, by decide, by decide, by decide⟩
  have band : SeventhKing .black (5,1) (6,2) := ⟨rfl, rfl, by decide⟩
  have losing : ¬ SeventhKingWins .black q (6,2) (7,0) := by
    rintro (wrong | notCorner)
    · cases wrong
    · exact notCorner ⟨rfl, Or.inr rfl, by decide⟩
  have classification := fresh_seventh_king_wdl50 h fresh band
  exact ⟨classification.2.2.2.mpr losing, (classification.2.2.1.mpr losing).2⟩

/-- Total bound exceeds 100 plies; pawn resets, rather than a sub100 shortcut, justify it. -/
theorem sixth_pawn_weak_102_example :
    FreshGame.Within .white 102 (FreshGame.fresh (pos .white (4,6) (3,5) (7,7) .black)) := by
  let q := pos .white (4,6) (3,5) (7,7) .black
  have h : IsKPK q .white (4,6) (3,5) (7,7) := ⟨by decide, by decide, by decide, rfl⟩
  have fresh : FreshLegal q (4,6) (3,5) (7,7) :=
    ⟨rfl, rfl, by decide, by decide, by decide, by decide⟩
  apply fresh_seventh_king_weak h fresh rfl ⟨rfl, rfl, by decide⟩
  intro corner
  have impossible := corner.2.2
  exact (by decide : absDiff 3 7 ≠ 1) impossible

theorem sixth_rank_white_entry_example :
    FreshGame.Within .white 103 (FreshGame.fresh (pos .white (2,5) (1,5) (7,7) .white)) := by
  let q := pos .white (2,5) (1,5) (7,7) .white
  have h : IsKPK q .white (2,5) (1,5) (7,7) := ⟨by decide, by decide, by decide, rfl⟩
  have fresh : FreshLegal q (2,5) (1,5) (7,7) :=
    ⟨rfl, rfl, by decide, by decide, by decide, by decide⟩
  apply fresh_seventh_king_entry h fresh rfl (t := (2,6))
    (by decide) (by decide) (by decide) ⟨rfl, rfl, by decide⟩
  intro corner
  exact (by decide : absDiff 1 7 ≠ 1) corner.2.2

theorem sixth_rank_black_entry_example :
    FreshGame.Within .black 103 (FreshGame.fresh (pos .black (5,2) (6,2) (0,0) .black)) := by
  let q := pos .black (5,2) (6,2) (0,0) .black
  have h : IsKPK q .black (5,2) (6,2) (0,0) := ⟨by decide, by decide, by decide, rfl⟩
  have fresh : FreshLegal q (5,2) (6,2) (0,0) :=
    ⟨rfl, rfl, by decide, by decide, by decide, by decide⟩
  apply fresh_seventh_king_entry h fresh rfl (t := (5,1))
    (by decide) (by decide) (by decide) ⟨rfl, rfl, by decide⟩
  intro corner
  exact (by decide : absDiff 6 0 ≠ 1) corner.2.2

theorem seventh_pawn_king_entry_example :
    FreshGame.Within .white 101 (FreshGame.fresh (pos .white (4,5) (3,6) (0,0) .white)) := by
  let q := pos .white (4,5) (3,6) (0,0) .white
  have h : IsKPK q .white (4,5) (3,6) (0,0) := ⟨by decide, by decide, by decide, rfl⟩
  have fresh : FreshLegal q (4,5) (3,6) (0,0) :=
    ⟨rfl, rfl, by decide, by decide, by decide, by decide⟩
  exact fresh_supported_king_entry h fresh rfl (t := (4,6))
    (by decide) (by decide) (by decide) ⟨rfl, rfl, by decide⟩

/-- A legal entry that would immediately stalemate is excluded by the certificate. -/
theorem stalemate_excludes_entry_example : ¬ KingEntry .white (2,5) (1,5) (0,7) := by
  rintro ⟨t, _, _, _, supported | ⟨_, notCorner⟩⟩
  · have impossible := supported.2.1
    change 5 = 6 at impossible
    cases impossible
  · exact notCorner ⟨rfl, Or.inl rfl, by decide⟩

theorem centered_white_both_turns_example (turn : Colour) :
    FreshGame.ActualWin .white (FreshGame.fresh (pos .white (3,6) (3,5) (7,7) turn)) := by
  let q := pos .white (3,6) (3,5) (7,7) turn
  have h : IsKPK q .white (3,6) (3,5) (7,7) := ⟨by decide, by decide, by decide, rfl⟩
  have fresh : FreshLegal q (3,6) (3,5) (7,7) :=
    ⟨rfl, rfl, by decide, by decide, by decide, by cases turn <;> decide⟩
  exact fresh_centered_win h fresh ⟨rfl, rfl, rfl, by decide, by decide⟩

theorem centered_black_both_turns_example (turn : Colour) :
    FreshGame.ActualWin .black (FreshGame.fresh (pos .black (3,1) (3,2) (7,0) turn)) := by
  let q := pos .black (3,1) (3,2) (7,0) turn
  have h : IsKPK q .black (3,1) (3,2) (7,0) := ⟨by decide, by decide, by decide, rfl⟩
  have fresh : FreshLegal q (3,1) (3,2) (7,0) :=
    ⟨rfl, rfl, by decide, by decide, by decide, by cases turn <;> decide⟩
  exact fresh_centered_win h fresh ⟨rfl, rfl, rfl, by decide, by decide⟩

/-- This control exercises the two-quiet-ply history before pawn advancement. -/
theorem centered_weak_104_example :
    FreshGame.Within .white 104 (FreshGame.fresh (pos .white (3,6) (3,5) (7,7) .black)) := by
  let q := pos .white (3,6) (3,5) (7,7) .black
  have h : IsKPK q .white (3,6) (3,5) (7,7) := ⟨by decide, by decide, by decide, rfl⟩
  have fresh : FreshLegal q (3,6) (3,5) (7,7) :=
    ⟨rfl, rfl, by decide, by decide, by decide, by decide⟩
  exact fresh_centered_weak h fresh rfl ⟨rfl, rfl, rfl, by decide, by decide⟩

end EndgameChess.Rules.KPK
