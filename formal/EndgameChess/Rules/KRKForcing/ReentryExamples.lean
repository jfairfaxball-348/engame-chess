import EndgameChess.Rules.KRKForcing.RankAdvanceRescue

/-! S028 fixed legal failed-policy controls; none is a class-wide proof. -/
namespace EndgameChess.Rules
open EndgameChess.KK
private def sq (x y : Fin 8) : Square := (x,y)
private def mv (x y u v : Fin 8) : Move := ⟨sq x y, sq u v, none⟩

def chaseStart : Position := krkPos .white (sq 1 0) (sq 7 0) (sq 1 2) .white
def chaseCheck : Position := play chaseStart (mv 7 0 7 2)
def chaseFirst : Position := play chaseCheck (mv 1 2 1 3)
def chaseUp : Position := play chaseFirst (mv 1 0 1 1)
def chaseA : Position := play chaseUp (mv 1 3 2 3)
def chaseKingRight : Position := play chaseA (mv 1 1 2 1)
def chaseB : Position := play chaseKingRight (mv 2 3 1 3)
def chaseKingLeft : Position := play chaseB (mv 2 1 1 1)
def chaseReturn : Position := play chaseKingLeft (mv 1 3 2 3)

set_option maxRecDepth 8192 in
theorem phase_image_chase_cycle :
    isLegal chaseStart (mv 7 0 7 2) = true ∧
    isLegal chaseCheck (mv 1 2 1 3) = true ∧
    isLegal chaseFirst (mv 1 0 1 1) = true ∧
    isLegal chaseUp (mv 1 3 2 3) = true ∧
    isLegal chaseA (mv 1 1 2 1) = true ∧
    isLegal chaseKingRight (mv 2 3 1 3) = true ∧
    isLegal chaseB (mv 2 1 1 1) = true ∧
    isLegal chaseKingLeft (mv 1 3 2 3) = true ∧
    PhaseImage (sq 1 1) (sq 7 2) (sq 2 3) ∧
    PhaseImage (sq 2 1) (sq 7 2) (sq 1 3) ∧
    ¬ Opposed (sq 1 1) (sq 2 3) ∧ ¬ Opposed (sq 2 1) (sq 1 3) ∧
    chaseReturn = chaseA := by
  refine ⟨by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide,
    by unfold PhaseImage; decide, by unfold PhaseImage; decide,
    by unfold Opposed; decide, by unfold Opposed; decide, ?_⟩
  have position_eq (a b : Position) (hb : a.board = b.board)
      (ht : a.turn = b.turn) (hc : a.castling = b.castling) (he : a.ep = b.ep) : a = b := by
    cases a; cases b; cases hb; cases ht; cases hc; cases he; rfl
  apply position_eq
  · funext s
    have h : ∀ s ∈ allSquares, chaseReturn.board s = chaseA.board s := by decide
    exact h s (mem_allSquares s)
  all_goals decide

def cornerBefore : Position := krkPos .white (sq 5 5) (sq 0 6) (sq 7 7) .white
def cornerAfter : Position := play cornerBefore (mv 0 6 6 6)

set_option maxRecDepth 8192 in
theorem protected_corner_reentry_stalemate :
    PhaseImage (sq 5 5) (sq 0 6) (sq 7 7) ∧
    isLegal cornerBefore (mv 0 6 6 6) = true ∧
    inCheck cornerAfter .black = false ∧ legalMoves cornerAfter = [] := by
  exact ⟨by unfold PhaseImage; decide, by decide, by decide, by decide⟩

def lowerBefore : Position := krkPos .white (sq 0 1) (sq 4 2) (sq 2 3) .white
def lowerCheck : Position := play lowerBefore (mv 4 2 4 3)

set_option maxRecDepth 8192 in
theorem lower_band_raise_crossing :
    PhaseImage (sq 0 1) (sq 4 2) (sq 2 3) ∧
    isLegal lowerBefore (mv 4 2 4 3) = true ∧
    isLegal lowerCheck (mv 2 3 2 2) = true := by
  exact ⟨by unfold PhaseImage; decide, by decide, by decide⟩

def upperBefore : Position := krkPos .white (sq 0 1) (sq 4 2) (sq 2 4) .white
def upperRaised : Position := play upperBefore (mv 4 2 4 3)
def upperHanging : Position := play upperRaised (mv 2 4 3 4)

set_option maxRecDepth 8192 in
theorem two_file_rank_raise_needs_rescue :
    PhaseImage (sq 0 1) (sq 4 2) (sq 2 4) ∧
    isLegal upperBefore (mv 4 2 4 3) = true ∧
    isLegal upperRaised (mv 2 4 3 4) = true ∧
    ¬ SafeRook (sq 0 1) (sq 4 3) (sq 3 4) ∧
    isLegal upperHanging (mv 4 3 7 3) = true := by
  exact ⟨by unfold PhaseImage; decide, by decide, by decide,
    by unfold SafeRook; decide, by decide⟩

end EndgameChess.Rules
