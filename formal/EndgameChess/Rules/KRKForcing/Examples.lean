import EndgameChess.Rules.KRKForcing.CheckProgress

/-! Fixed kernel witnesses and failed-distance controls for S026. -/
namespace EndgameChess.Rules
open EndgameChess.KK
private def esq (x y : Fin 8) : Square := (x,y)
private def em (x y u v : Fin 8) : Move := ⟨esq x y, esq u v, none⟩

/-- The four-file hypothesis is satisfiable; the upper-edge instance actually forces mate. -/
def oppositionEdgePos : Position := krkPos .white (esq 0 5) (esq 7 0) (esq 0 7) .white

theorem opposition_edge_force_example : ForceMate .white oppositionEdgePos := by
  apply krk_opposition_edge_force (sk := esq 0 5) (rs := esq 7 0) (wk := esq 0 7)
  · exact ⟨by decide, by decide, by decide, rfl⟩
  · rfl
  · unfold Opposed; decide
  · decide
  · decide
  · rfl

/-- Gap two: Rc3+ Kb4 Ka2 Kxc3 is legal, so blindly following the check loses the rook. -/
def gapTwoStart : Position := krkPos .white (esq 0 0) (esq 2 0) (esq 0 2) .white
def gapTwoCheck : Position := play gapTwoStart (em 2 0 2 2)
def gapTwoReply : Position := play gapTwoCheck (em 0 2 1 3)
def gapTwoKingUp : Position := play gapTwoReply (em 0 0 0 1)
def gapTwoCaptured : Position := play gapTwoKingUp (em 1 3 2 2)

set_option maxRecDepth 8192 in
theorem two_file_margin_capture :
    isLegal gapTwoStart (em 2 0 2 2) = true ∧
    isLegal gapTwoCheck (em 0 2 1 3) = true ∧
    isLegal gapTwoReply (em 0 0 0 1) = true ∧
    isLegal gapTwoKingUp (em 1 3 2 2) = true ∧ IsKK gapTwoCaptured (esq 0 1) (esq 2 2) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, ?_⟩
  have h : ∀ s ∈ allSquares, gapTwoCaptured.board s = kkBoard (esq 0 1) (esq 2 2) s := by decide
  exact funext fun s => h s (mem_allSquares s)

/-- Gap three can leave the rook hanging after two replies, even without an immediate loss. -/
def gapThreeStart : Position := krkPos .white (esq 0 0) (esq 3 0) (esq 0 2) .white
def gapThreeCheck : Position := play gapThreeStart (em 3 0 3 2)
def gapThreeReply : Position := play gapThreeCheck (em 0 2 1 3)
def gapThreeKingUp : Position := play gapThreeReply (em 0 0 0 1)
def gapThreeEnd : Position := play gapThreeKingUp (em 1 3 2 3)

set_option maxRecDepth 8192 in
theorem three_file_margin_hanging :
    isLegal gapThreeStart (em 3 0 3 2) = true ∧
    isLegal gapThreeCheck (em 0 2 1 3) = true ∧
    isLegal gapThreeReply (em 0 0 0 1) = true ∧
    isLegal gapThreeKingUp (em 1 3 2 3) = true ∧
    IsKRK gapThreeEnd .white (esq 0 1) (esq 3 2) (esq 2 3) ∧
    ¬ SafeRook (esq 0 1) (esq 3 2) (esq 2 3) := by
  refine ⟨by decide, by decide, by decide, by decide,
    ⟨by decide, by decide, by decide, ?_⟩, by unfold SafeRook; decide⟩
  have h : ∀ s ∈ allSquares, gapThreeEnd.board s = krkBoard .white (esq 0 1) (esq 3 2) (esq 2 3) s := by decide
  exact funext fun s => h s (mem_allSquares s)

/-- A valid wide-rook phase need not restore opposed files: setup/re-entry is still needed. -/
def wideStart : Position := krkPos .white (esq 0 0) (esq 7 0) (esq 0 2) .white
def wideCheck : Position := play wideStart (em 7 0 7 2)
def wideReply : Position := play wideCheck (em 0 2 1 3)
def wideKingUp : Position := play wideReply (em 0 0 0 1)
def wideEnd : Position := play wideKingUp (em 1 3 2 3)

set_option maxRecDepth 8192 in
theorem phase_need_not_restore_opposition :
    isLegal wideStart (em 7 0 7 2) = true ∧ isLegal wideCheck (em 0 2 1 3) = true ∧
    isLegal wideReply (em 0 0 0 1) = true ∧ isLegal wideKingUp (em 1 3 2 3) = true ∧
    IsKRK wideEnd .white (esq 0 1) (esq 7 2) (esq 2 3) ∧
    DistantBarrier (esq 0 1) (esq 7 2) (esq 2 3) ∧ ¬ Opposed (esq 0 1) (esq 2 3) := by
  refine ⟨by decide, by decide, by decide, by decide,
    ⟨by decide, by decide, by decide, ?_⟩, by unfold DistantBarrier; decide,
    by unfold Opposed; decide⟩
  have h : ∀ s ∈ allSquares, wideEnd.board s = krkBoard .white (esq 0 1) (esq 7 2) (esq 2 3) s := by decide
  exact funext fun s => h s (mem_allSquares s)

end EndgameChess.Rules
