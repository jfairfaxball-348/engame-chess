import EndgameChess.Rules.KRKForcing.OutcomeClassification
import EndgameChess.Rules.KRKForcing.WallExamples

/-! S030 fixed controls: safe setup, both colours/flags, failed-policy capture. -/
namespace EndgameChess.Rules
open EndgameChess.KK
private def sq (x y : Fin 8) : Square := (x,y)

/-- Back-rank preparation: Ka1/Rc1 versus Kb3. -/
theorem backrank_preparation_forces :
    ForceMate .white (krkPos .white (sq 0 0) (sq 2 0) (sq 1 2) .white) := by
  apply krk_strong_force_of_not_check (sk := sq 0 0) (rs := sq 2 0) (wk := sq 1 2)
  · exact ⟨by decide, by decide, by decide, rfl⟩
  · rfl
  · decide

/-- Equal-rank kings require a file axis; flags do not restrict the theorem. -/
def flaggedFileSetup : Position :=
  { krkPos .black (sq 0 3) (sq 0 0) (sq 2 3) .black with
    castling := ⟨true, true, true, true⟩, ep := some (sq 4 5) }

theorem black_flagged_file_setup_forces : ForceMate .black flaggedFileSetup := by
  apply krk_strong_force_of_not_check (sk := sq 0 3) (rs := sq 0 0) (wk := sq 2 3)
  · exact ⟨by decide, by decide, by decide, rfl⟩
  · rfl
  · decide

/-- The initial control wins, while both naive unprotected setups lose forcing. -/
theorem safe_setup_capture_controls : ForceMate .white setupBefore ∧
    ¬ ForceMate .white setupRankWall ∧ ¬ ForceMate .white setupFileWall := by
  have hc := direct_setup_capture_controls
  refine ⟨?_, ?_, ?_⟩
  · apply krk_strong_force_of_not_check (sk := sq 0 0) (rs := sq 3 3) (wk := sq 2 2)
    · exact ⟨by decide, by decide, by decide, rfl⟩
    · rfl
    · decide
  · have hl : Legal setupRankWall (play setupRankWall ⟨sq 2 2, sq 3 1, none⟩) :=
      ⟨_, hc.2.1, rfl⟩
    exact dead_reply_not_forceMate rfl hl (dead_of_legal_into_KK hl hc.2.2.1)
  · have hl : Legal setupFileWall (play setupFileWall ⟨sq 2 2, sq 1 3, none⟩) :=
      ⟨_, hc.2.2.2.2.1, rfl⟩
    exact dead_reply_not_forceMate rfl hl (dead_of_legal_into_KK hl hc.2.2.2.2.2)

end EndgameChess.Rules
