import EndgameChess.Rules.KPK.CenteredKing

namespace EndgameChess.Rules.KPK
open EndgameChess.KK

/-- All three seventh-rank support squares of a sixth-rank non-rook pawn. -/
def SixthPawnKeyBand (σ : Colour) (sk ps : Square) : Prop :=
  height σ sk = 6 ∧ height σ ps = 5 ∧
    (1 ≤ ps.1.val ∧ ps.1.val ≤ 6) ∧ absDiff sk.1.val ps.1.val ≤ 1

theorem key_band_split {σ : Colour} {sk ps : Square} (band : SixthPawnKeyBand σ sk ps) :
    CenteredSeventh σ sk ps ∨ SeventhKing σ sk ps := by
  obtain ⟨kingRank, pawnRank, interior, files⟩ := band
  by_cases zero : absDiff sk.1.val ps.1.val = 0
  · left
    refine ⟨kingRank, pawnRank, ?_, interior⟩
    apply Fin.ext
    simp only [absDiff] at zero
    omega
  · exact Or.inr ⟨kingRank, pawnRank, by omega⟩

/-- Complete outcome and dead/live criterion on the three-square band.
The outside-corner stalemate exception is explicit; this is not KPK class closure. -/
theorem fresh_key_band_wdl50 {q : Position} {σ : Colour} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk) (band : SixthPawnKeyBand σ sk ps) :
    (FreshGame.ActualWin σ (FreshGame.fresh q) ↔ SeventhKingWins σ q ps wk) ∧
    ¬ FreshGame.ActualWin σ.opp (FreshGame.fresh q) ∧
    ((FreshGame.Hold σ (FreshGame.fresh q) ∧ FreshGame.Hold σ.opp (FreshGame.fresh q)) ↔
      ¬ SeventhKingWins σ q ps wk) ∧
    (DeadK q ↔ ¬ SeventhKingWins σ q ps wk) := by
  rcases key_band_split band with center | side
  · have criterion : SeventhKingWins σ q ps wk := Or.inr (centered_not_corner center fresh.kings)
    have win := fresh_centered_win h fresh center
    have live := forceMate_not_dead (FreshGame.win_project (FreshGame.actual_win_iff_rule.mp win))
    have noWeakHold : ¬ FreshGame.Hold σ.opp (FreshGame.fresh q) := by
      intro holding
      have noWin := FreshGame.hold_not_win holding
      rw [opp_opp] at noWin
      exact noWin (FreshGame.actual_win_iff_rule.mp win)
    refine ⟨⟨fun _ => criterion, fun _ => win⟩, fresh_no_weak_actual_win h fresh, ?_, ?_⟩
    · exact ⟨fun both => False.elim (noWeakHold both.2), fun notCriterion => False.elim (notCriterion criterion)⟩
    · exact ⟨fun dead => False.elim (live dead), fun notCriterion => False.elim (notCriterion criterion)⟩
  · exact fresh_seventh_king_wdl50 h fresh side

theorem key_band_force_iff_fresh {q : Position} {σ : Colour} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk) (band : SixthPawnKeyBand σ sk ps) :
    ForceMate σ q ↔ FreshGame.ActualWin σ (FreshGame.fresh q) := by
  constructor
  · intro force
    apply (fresh_key_band_wdl50 h fresh band).1.mpr
    apply Classical.byContradiction
    intro losing
    exact forceMate_not_dead force ((fresh_key_band_wdl50 h fresh band).2.2.2.mpr losing)
  · exact fun actual => FreshGame.win_project (FreshGame.actual_win_iff_rule.mp actual)

end EndgameChess.Rules.KPK
