import EndgameChess.Rules.KRKForcing.WallEntry

/-! Positive forcing controls and failed direct-setup moves; fixed cases only. -/
namespace EndgameChess.Rules
open EndgameChess.KK
private def sq (x y : Fin 8) : Square := (x,y)
private def mv (x y u v : Fin 8) : Move := ⟨sq x y, sq u v, none⟩

theorem two_file_edge_forcing_control :
    ForceMate .white (krkPos .white (sq 2 5) (sq 0 0) (sq 2 7) .white) := by
  apply krk_two_file_edge_force (sk := sq 2 5) (rs := sq 0 0) (wk := sq 2 7)
  · exact ⟨⟨by decide, by decide, by decide, rfl⟩, rfl⟩
  · unfold Opposed; decide
  all_goals decide

theorem former_chase_cycle_is_forcing :
    ForceMate .white (krkPos .white (sq 1 1) (sq 7 2) (sq 2 3) .white) := by
  apply krk_rank_wall_force (sk := sq 1 1) (rs := sq 7 2) (wk := sq 2 3)
  · exact ⟨⟨by decide, by decide, by decide, rfl⟩, rfl⟩
  all_goals decide

theorem threatened_wall_rook_is_forcing :
    ForceMate .white (krkPos .white (sq 0 0) (sq 1 2) (sq 2 3) .white) := by
  apply krk_rank_wall_force (sk := sq 0 0) (rs := sq 1 2) (wk := sq 2 3)
  · exact ⟨⟨by decide, by decide, by decide, rfl⟩, rfl⟩
  all_goals decide

def setupBefore : Position := krkPos .white (sq 0 0) (sq 3 3) (sq 2 2) .white
def setupRankWall : Position := play setupBefore (mv 3 3 3 1)
def setupFileWall : Position := play setupBefore (mv 3 3 1 3)

set_option maxRecDepth 8192 in
theorem direct_setup_capture_controls :
    isLegal setupBefore (mv 3 3 3 1) = true ∧
    isLegal setupRankWall (mv 2 2 3 1) = true ∧
    IsKK (play setupRankWall (mv 2 2 3 1)) (sq 0 0) (sq 3 1) ∧
    isLegal setupBefore (mv 3 3 1 3) = true ∧
    isLegal setupFileWall (mv 2 2 1 3) = true ∧
    IsKK (play setupFileWall (mv 2 2 1 3)) (sq 0 0) (sq 1 3) := by
  refine ⟨by decide, by decide, ?_, by decide, by decide, ?_⟩
  · refine ⟨by decide, ?_⟩
    have h : ∀ s ∈ allSquares,
        (play setupRankWall (mv 2 2 3 1)).board s = kkBoard (sq 0 0) (sq 3 1) s := by decide
    exact funext fun s => h s (mem_allSquares s)
  · refine ⟨by decide, ?_⟩
    have h : ∀ s ∈ allSquares,
        (play setupFileWall (mv 2 2 1 3)).board s = kkBoard (sq 0 0) (sq 1 3) s := by decide
    exact funext fun s => h s (mem_allSquares s)

end EndgameChess.Rules
