import EndgameChess.Rules.KRKSixPlyHistory
import EndgameChess.Rules.KRKFivePlyExact

namespace EndgameChess.Rules.KRKSixPlyExact
open EndgameChess.KK KRKThreePly KRKLastReply KRKOppositionHistory KRKWeakBranch RawHistoryLayer KRKHolding
open KRKCornerWeakBand (Guard guard_legal step_guard)
open KRKSixPlyHistory (Clear sufficient)
set_option maxHeartbeats 300000

theorem necessary {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ.opp) (cert : W σ 6 s) : Clear s.val sk rs wk := by
  have win : F σ s := ⟨6,cert⟩
  have safe : SafeRook sk rs wk := krk_force_weak_safe material turn ⟨6,raw_ruleMateWithin_project s σ 6 cert⟩
  have allCert : ∀ v, BoardStep s v → W σ 5 v := by
    rcases cert with goal | ⟨_,chosen | defended⟩
    · exact False.elim (goal.2.2 (((RawAdjudication.ongoing_iff s.val).mp ongoing).2.1))
    · exact False.elim (opp_ne σ (chosen.1.symm.trans turn))
    · exact defended.2.2.2
  obtain ⟨noClaim, nonempty, all⟩ := weak_force_data ongoing turn win
  have claims := (RawClaims.no_threshold_iff s.val).mp noClaim
  have time : RawClock.clock s.val.trace < 99 := by
    obtain ⟨v, m, legal, _⟩ := nonempty
    have bound := (claims.2.2 m legal).1
    have quiet := weak_safe_quiet material turn safe legal
    change (if RawClock.zeroing (erase s) m then 0 else RawClock.clock s.val.trace + 1) < 100 at bound
    simp only [quiet, Bool.false_eq_true, ↓reduceIte] at bound
    omega
  refine ⟨safe, time, claims.2.1, ?_⟩
  intro t guard
  have legal := guard_legal material turn guard
  have childWin := all (weakChild s ongoing wk t legal) ⟨_, legal, rfl⟩
  have next := weak_material_after material turn safe legal
  have nextTurn : (erase (weakChild s ongoing wk t legal)).turn = σ := by
    change (play (erase s) _).turn = σ; simp only [play_turn,turn,opp_opp]
  have evaluated := (KRKFivePlyExact.rule_five_iff (s := weakChild s ongoing wk t legal)
    next (child_ongoing_of_force material ongoing turn legal childWin) nextTurn).mp
      (allCert _ ⟨_,legal,rfl⟩)
  exact ⟨(claims.2.2 _ legal).2,(KRKFiveWeakPrefix.strong_clear_append_iff material turn safe legal).mp evaluated⟩

theorem rule_six_iff {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s) (turn : (erase s).turn = σ.opp) :
    W σ 6 s ↔ Clear s.val sk rs wk := ⟨necessary material ongoing turn,sufficient material ongoing turn⟩

theorem weak_seven_six {s : State} {σ : Colour} (turn : (erase s).turn = σ.opp)
    (cert : W σ 7 s) : W σ 6 s := by
  rcases cert with goal | ⟨ongoing,chosen | defended⟩
  · exact Or.inl goal
  · exact False.elim (opp_ne σ (chosen.1.symm.trans turn))
  · refine Or.inr ⟨ongoing,Or.inr ⟨turn,defended.2.1,defended.2.2.1,?_⟩⟩
    intro t edge
    have strong : (erase t).turn = σ := by
      have changed : (erase t).turn = (erase s).turn.opp := turn_of_legal (RawTrace.raw_step_sound edge)
      rw [changed,turn,opp_opp]
    exact KRKFivePlyExact.strong_six_five strong (defended.2.2.2 t edge)

end EndgameChess.Rules.KRKSixPlyExact
