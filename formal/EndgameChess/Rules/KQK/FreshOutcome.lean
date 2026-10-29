import EndgameChess.Rules.KQK.BoardOutcome
import EndgameChess.Rules.FreshGame.Winning

/-! Complete fresh KQK outcome. Roots have no incoming history, clock zero,
no castling rights or en-passant target, and explicit local legality. -/
namespace EndgameChess.Rules.KQK
open EndgameChess.KK

structure FreshLegal (q : Position) (sk wk : Square) : Prop where
  rights : q.castling = noRights
  ep : q.ep = none
  kings : 2 ≤ dInf sk wk
  previousSafe : inCheck q q.turn.opp = false

def WinningCriterion (σ : Colour) (q : Position) (sk qs wk : Square) : Prop :=
  q.turn = σ ∨ MatedK q ∨ (SafeQueen sk qs wk ∧ ∃ r, Legal q r)

theorem fresh_strong97 {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (legal : FreshLegal q sk wk) (ht : q.turn = σ) :
    FreshGame.Within σ 97 (FreshGame.fresh q) := by
  have hc : inCheck q σ.opp = false := by simpa only [ht] using legal.previousSafe
  exact FreshGame.fresh_sub100 (strong_entry_bound hq ht hc) (by decide)

theorem fresh_weak98 {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ.opp)
    (safe : SafeQueen sk qs wk) (moves : ∃ r, Legal q r) :
    FreshGame.Within σ 98 (FreshGame.fresh q) :=
  FreshGame.fresh_sub100 (safe_weak_entry_bound hq ht safe moves) (by decide)

theorem fresh_outcome_iff {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (legal : FreshLegal q sk wk) :
    FreshGame.Win σ (FreshGame.fresh q) ↔ WinningCriterion σ q sk qs wk := by
  constructor
  · intro win
    exact (board_outcome_iff hq (fun ht => by simpa only [ht] using legal.previousSafe)).mp
      (FreshGame.win_project win)
  · intro criterion
    rcases colour_cases σ q.turn with strong | weak
    · exact ⟨97,fresh_strong97 hq legal strong⟩
    · rcases criterion with wrong | mate | ⟨safe,moves⟩
      · exact False.elim (opp_ne σ (wrong.symm.trans weak))
      · exact ⟨0,weak,mate⟩
      · exact ⟨98,fresh_weak98 hq weak safe moves⟩

theorem fresh_no_weak_win {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (legal : FreshLegal q sk wk) :
    ¬ FreshGame.Win σ.opp (FreshGame.fresh q) :=
  fun win => no_weak_force hq legal.kings legal.rights (FreshGame.win_project win)

/-- The queen side never needs to concede: every legal continuation in
the KQK/KK material region excludes a mate of its king. -/
theorem fresh_strong_hold {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (legal : FreshLegal q sk wk) :
    FreshGame.Hold σ (FreshGame.fresh q) := by
  apply FreshGame.hold_of_safe_reach
  intro r reach
  exact no_weak_reachable_mate hq legal.kings legal.rights reach

/-- Every nonwinning case has an explicit weak holding argument: the
root is stopped, or the exposed queen is captured into dead KK. -/
theorem fresh_weak_hold {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (notWinning : ¬ WinningCriterion σ q sk qs wk) :
    FreshGame.Hold σ.opp (FreshGame.fresh q) := by
  have turn : q.turn = σ.opp := by
    rcases colour_cases σ q.turn with strong | weak
    · exact False.elim (notWinning (Or.inl strong))
    · exact weak
  have notMate : ¬ MatedK q := fun mate => notWinning (Or.inr (Or.inl mate))
  have safeGoal : ¬ MateGoal σ.opp.opp q := fun goal => notMate goal.2
  by_cases safe : SafeQueen sk qs wk
  · have noMoves : ¬∃ r, Legal q r := fun moves => notWinning (Or.inr (Or.inr ⟨safe,moves⟩))
    exact FreshGame.terminal_hold (fun ongoing => noMoves ongoing.2.1) safeGoal
  · have h0 : dInf qs wk ≠ 0 := fun h => hq.2.2.1 (dInf_eq_zero_iff.mp h)
    have h1 : dInf sk qs ≠ 0 := fun h => hq.1 (dInf_eq_zero_iff.mp h)
    have near : dInf wk qs = 1 := by
      simp only [LoneKing.Safe,not_or] at safe
      rw [dInf_comm]; omega
    have far : 2 ≤ dInf sk qs := by simp only [LoneKing.Safe,not_or] at safe; omega
    obtain ⟨r,hr,w,b,kk⟩ := LoneKing.unprotected_capture (by decide : PieceType.queen ≠ .king)
      hq turn near far
    exact FreshGame.hold_via_dead_reply turn safeGoal ⟨r,hr,dead_of_legal_into_KK hr kk⟩

/-- Complete WDL50 classification for both colours and turns. All board
wins lift, so this class has no cursed wins or blessed losses at fresh roots. -/
theorem fresh_rule_wdl50 {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (legal : FreshLegal q sk wk) :
    (FreshGame.Win σ (FreshGame.fresh q) ↔ WinningCriterion σ q sk qs wk) ∧
    ¬ FreshGame.Win σ.opp (FreshGame.fresh q) ∧
    ((FreshGame.Hold σ (FreshGame.fresh q) ∧ FreshGame.Hold σ.opp (FreshGame.fresh q)) ↔
      ¬ WinningCriterion σ q sk qs wk) := by
  refine ⟨fresh_outcome_iff hq legal,fresh_no_weak_win hq legal,?_⟩
  constructor
  · rintro ⟨_,holding⟩ winning
    have noWin := FreshGame.hold_not_win holding
    rw [opp_opp] at noWin
    exact noWin ((fresh_outcome_iff hq legal).mpr winning)
  · intro noWin
    exact ⟨fresh_strong_hold hq legal,fresh_weak_hold hq noWin⟩

theorem fresh_uniform98 {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (legal : FreshLegal q sk wk)
    (winning : WinningCriterion σ q sk qs wk) :
    FreshGame.Within σ 98 (FreshGame.fresh q) := by
  have board : MateWithin σ 98 q := by
    rcases colour_cases σ q.turn with strong | weak
    · have hc : inCheck q σ.opp = false := by simpa only [strong] using legal.previousSafe
      exact mateWithin_mono (strong_entry_bound hq strong hc) (by decide)
    · rcases winning with wrong | mate | ⟨safe,moves⟩
      · exact False.elim (opp_ne σ (wrong.symm.trans weak))
      · exact mateWithin_mono (show MateWithin σ 0 q from ⟨weak,mate⟩) (by decide)
      · exact safe_weak_entry_bound hq weak safe moves
  exact FreshGame.fresh_sub100 board (by decide)

/-- The complete classification uses independent actual policies for both
winning and holding, equivalent to the checked finite rule certificates. -/
theorem fresh_wdl50 {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (legal : FreshLegal q sk wk) :
    (FreshGame.ActualWin σ (FreshGame.fresh q) ↔ WinningCriterion σ q sk qs wk) ∧
    ¬ FreshGame.ActualWin σ.opp (FreshGame.fresh q) ∧
    ((FreshGame.Hold σ (FreshGame.fresh q) ∧ FreshGame.Hold σ.opp (FreshGame.fresh q)) ↔
      ¬ WinningCriterion σ q sk qs wk) :=
  ⟨FreshGame.actual_win_iff_rule.trans (fresh_outcome_iff hq legal),
    fun win => fresh_no_weak_win hq legal (FreshGame.actual_win_iff_rule.mp win),
    (fresh_rule_wdl50 hq legal).2.2⟩

/-- No fresh KQK board win is cursed by the 50-move rule. -/
theorem fresh_force_iff {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (legal : FreshLegal q sk wk) :
    FreshGame.ActualWin σ (FreshGame.fresh q) ↔ ForceMate σ q :=
  (fresh_wdl50 hq legal).1.trans
    (board_outcome_iff hq (fun ht => by simpa only [ht] using legal.previousSafe)).symm

theorem fresh_dead_iff {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (legal : FreshLegal q sk wk) :
    DeadK q ↔ q.turn = σ.opp ∧ ¬ MatedK q ∧ ∀ r, Legal q r → ∃ w b, IsKK r w b := by
  rcases colour_cases σ q.turn with strong | weak
  · constructor
    · intro dead
      have hc : inCheck q σ.opp = false := by simpa only [strong] using legal.previousSafe
      exact False.elim (forceMate_not_dead ⟨97,strong_entry_bound hq strong hc⟩ dead)
    · rintro ⟨wrong,_,_⟩
      exact False.elim (opp_ne σ (strong.symm.trans wrong))
  · exact ⟨fun dead => ⟨weak,(weak_dead_iff hq weak).mp dead⟩,
      fun ⟨_,condition⟩ => (weak_dead_iff hq weak).mpr condition⟩

end EndgameChess.Rules.KQK
