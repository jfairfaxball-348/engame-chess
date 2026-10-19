import EndgameChess.Rules.ForceMate
import EndgameChess.Rules.KRKConfinement

/-! Fixed non-vacuity and negative examples, S024. Bounded kernel `decide` checks
only; none of the general EC-C009/010 proofs uses a per-position enumeration. -/
namespace EndgameChess.Rules
open EndgameChess.KK

private def sq (x y : Fin 8) : Square := (x, y)

/-- White Kh8, Rb3, Black Ka2, Black to move. Global reachability is not asserted. -/
def optionalCapturePos : Position := krkPos .white (sq 7 7) (sq 1 2) (sq 0 1) .black
def optionalCapture : Move := ⟨sq 0 1, sq 1 2, none⟩
def optionalDecline : Move := ⟨sq 0 1, sq 0 0, none⟩

private theorem optional_capture_legal : Legal optionalCapturePos
    (play optionalCapturePos optionalCapture) := ⟨optionalCapture, by decide, rfl⟩

private theorem optional_capture_KK :
    IsKK (play optionalCapturePos optionalCapture) (sq 7 7) (sq 1 2) := by
  refine ⟨by decide, ?_⟩
  have h : ∀ s ∈ allSquares, (play optionalCapturePos optionalCapture).board s =
      kkBoard (sq 7 7) (sq 1 2) s := by decide
  exact funext fun s => h s (mem_allSquares s)

private theorem optional_decline_legal : Legal optionalCapturePos
    (play optionalCapturePos optionalDecline) := ⟨optionalDecline, by decide, rfl⟩

private theorem optional_decline_KRK :
    IsKRK (play optionalCapturePos optionalDecline) .white (sq 7 7) (sq 1 2) (sq 0 0) := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  have h : ∀ s ∈ allSquares, (play optionalCapturePos optionalDecline).board s =
      krkBoard .white (sq 7 7) (sq 1 2) (sq 0 0) s := by decide
  exact funext fun s => h s (mem_allSquares s)

/-- Liveness is strictly weaker than forcing: one live reply and one dead reply. -/
theorem krk_optional_capture_counterexample :
    Legal optionalCapturePos (play optionalCapturePos optionalCapture) ∧
    DeadK (play optionalCapturePos optionalCapture) ∧
    Legal optionalCapturePos (play optionalCapturePos optionalDecline) ∧
    ¬ DeadK (play optionalCapturePos optionalDecline) ∧
    ¬ DeadK optionalCapturePos ∧ ¬ ForceMate .white optionalCapturePos := by
  have hd := dead_of_legal_into_KK optional_capture_legal optional_capture_KK
  have hlive := krk_strong_to_move_live optional_decline_legal optional_decline_KRK rfl
  refine ⟨optional_capture_legal, hd, optional_decline_legal, hlive, ?_,
    dead_reply_not_forceMate rfl optional_capture_legal hd⟩
  intro hdead
  apply hlive
  rintro ⟨t, ht, hm⟩
  exact hdead ⟨t, reachK_cons optional_decline_legal ht, hm⟩

/-- The capture is an explicit holding action: afterwards neither colour can force mate. -/
theorem optional_capture_holds (σ : Colour) :
    ¬ ForceMate σ (play optionalCapturePos optionalCapture) := by
  intro h
  exact forceMate_not_dead h (dead_of_legal_into_KK optional_capture_legal optional_capture_KK)

set_option maxRecDepth 8192 in
private theorem ra8_goal : MateGoal .white (play krkLive ra8) := by
  refine ⟨rfl, by decide, ?_⟩
  have hmoves : legalMoves (play krkLive ra8) = [] := by decide
  rintro ⟨r, hr⟩
  obtain ⟨m, hmem, _⟩ := legal_of_legalMoves_eq hmoves hr
  simp at hmem

/-- A positive forcing witness with a one-ply bound, plus zero-ply terminal mate. -/
theorem krk_force_mate_in_one_example : MateWithin .white 1 krkLive ∧
    MateWithin .white 0 (play krkLive ra8) ∧
    ¬ ForceMate .black (play krkLive ra8) := by
  refine ⟨Or.inr ⟨krk_live_example, Or.inl ⟨rfl, play krkLive ra8,
    ⟨ra8, by decide, rfl⟩, ra8_goal⟩⟩, ra8_goal, ?_⟩
  intro h
  have hg := (forceMate_no_moves_iff (σ := .black) ra8_goal.2.2).1 h
  have ht := hg.1
  exact (by decide : (play krkLive ra8).turn ≠ Colour.black.opp) ht

/-- Protection plus strict rank separation may still be stalemate. -/
def protectedRankStale : Position := krkPos .white (sq 2 5) (sq 1 6) (sq 0 7) .black

set_option maxRecDepth 8192 in
theorem protected_rank_stalemate_example :
    ProtectedRank (sq 2 5) (sq 1 6) (sq 0 7) ∧
    inCheck protectedRankStale .black = false ∧ legalMoves protectedRankStale = [] ∧
    ∀ σ, ¬ ForceMate σ protectedRankStale := by
  have hn : legalMoves protectedRankStale = [] := by decide
  have hc : inCheck protectedRankStale .black = false := by decide
  refine ⟨by unfold ProtectedRank; decide, hc, hn, fun σ => stalemate_not_forceMate hc ?_⟩
  rintro ⟨r, hr⟩
  obtain ⟨m, hm, _⟩ := legal_of_legalMoves_eq hn hr
  simp at hm

/-- A strong king ON the rook's rank can block it, allowing a legal crossing. -/
def blockedBarrierPos : Position := krkPos .white (sq 4 3) (sq 3 3) (sq 6 4) .black
def blockedBarrierMove : Move := ⟨sq 6 4, sq 6 3, none⟩

theorem blocked_rank_counterexample :
    dInf (sq 4 3) (sq 3 3) = 1 ∧
    Legal blockedBarrierPos (play blockedBarrierPos blockedBarrierMove) :=
  ⟨by decide, blockedBarrierMove, by decide, rfl⟩

end EndgameChess.Rules
