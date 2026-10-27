import EndgameChess.Rules.KRKFourPlyNearCorner

namespace EndgameChess.Rules.KRKFourPlyNearCorner
open EndgameChess.KK KRKThreePly KRKLastReply KRKMateGeometry
set_option maxHeartbeats 300000

theorem near_four_safe {sk rs wk : Square} (file : wk.1.val = 1) (rank : wk.2.val = 0)
    (region : NearFour sk rs) : SafeRook sk rs wk := by
  simp only [NearFour, SafeRook, dInf, absDiff, file, rank] at *
  omega

/-- Complete near-corner kernel classification, retaining the nonempty
legal-reply condition so that stalemate is never promoted to a win. -/
theorem weak_four_iff {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp)
    (far : 2 ≤ dInf sk wk) (file : wk.1.val = 1) (rank : wk.2.val = 0) :
    MateWithin σ 4 q ↔ MatedK q ∨ (NearFour sk rs ∧ ∃ r, Legal q r) := by
  constructor
  · intro win
    have safe := krk_force_weak_safe material turn ⟨4, win⟩
    rcases win with goal | ⟨_, chosen | defended⟩
    · exact Or.inl goal.2
    · exact False.elim (opp_ne σ (chosen.1.symm.trans turn))
    · have every : ∀ u, StepM ⟨sk, rs, wk, false⟩ ⟨sk, rs, u, true⟩ → Three sk rs u := by
        intro u step
        obtain ⟨r, legal, next⟩ := step_sound
          (show Matches q σ ⟨sk, rs, wk, false⟩ from ⟨material, turn⟩) step
        obtain ⟨nextFar, notCheck⟩ := krk_strong_arrival_geometry legal next.1 next.2
        exact (strong_three_iff next.1 next.2 nextFar notCheck).mp (defended.2.2 r legal)
      rcases near_four_necessary material.1 file rank far safe every with terminal | region
      · exact Or.inl ((kernel_mate_iff material turn far).mpr terminal)
      · exact Or.inr ⟨region, defended.2.1⟩
  · rintro (mate | ⟨region, nonempty⟩)
    · exact mateWithin_mono (show MateWithin σ 0 q from ⟨turn, mate⟩) (by omega)
    · have safe := near_four_safe file rank region
      apply mateWithin_defend turn nonempty
      intro v reply
      obtain ⟨t, next, move⟩ := krk_safe_reply material turn safe reply
      obtain ⟨nextFar, notCheck⟩ := krk_strong_arrival_geometry reply next.1 next.2
      exact (strong_three_iff next.1 next.2 nextFar notCheck).mpr
        (near_four_replies material.1 file rank region t move)

end EndgameChess.Rules.KRKFourPlyNearCorner
