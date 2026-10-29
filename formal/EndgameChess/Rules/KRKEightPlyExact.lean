import EndgameChess.Rules.KRKEightPlyHistory
import EndgameChess.Rules.KRKSevenPlyExact

namespace EndgameChess.Rules.KRKEightPlyExact
open EndgameChess.KK KRKThreePly KRKLastReply KRKOppositionHistory KRKWeakBranch RawHistoryLayer KRKHolding
open KRKCornerWeakBand (Guard guard_legal step_guard)
open KRKEightPlyHistory (Clear sufficient)
set_option maxHeartbeats 400000

theorem necessary {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ.opp) (cert : W σ 8 s) :
    Clear s.val sk rs wk := by
  have win : F σ s := ⟨8,cert⟩
  have safe : SafeRook sk rs wk := krk_force_weak_safe material turn ⟨8,raw_ruleMateWithin_project s σ 8 cert⟩
  have allCert : ∀ v, BoardStep s v → W σ 7 v := by
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
  have childClock := child_clock material ongoing turn safe legal
  have evaluated := (KRKSevenPlyExact.rule_seven_iff (s := weakChild s ongoing wk t legal)
    next (child_ongoing_of_force material ongoing turn legal childWin) nextTurn).mp (allCert _ ⟨_,legal,rfl⟩)
  exact ⟨(claims.2.2 _ legal).2,(KRKEightPrefix.seven_append_iff material turn safe legal).mp evaluated⟩


theorem rule_eight_iff {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s) (turn : (erase s).turn = σ.opp) :
    W σ 8 s ↔ Clear s.val sk rs wk := ⟨necessary material ongoing turn,sufficient material ongoing turn⟩

theorem distance_cases {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s) (turn : (erase s).turn = σ.opp)
    (cert : W σ 8 s) :
    (LastReply sk rs wk ∧ W σ 2 s ∧ ¬W σ 1 s) ∨
    (¬LastReply sk rs wk ∧ KRKGlobalWeakBand.Clear s.val sk rs wk ∧ W σ 4 s ∧ ¬W σ 3 s) ∨
    (¬KRKGlobalWeakBand.Clear s.val sk rs wk ∧ KRKSixPlyHistory.Clear s.val sk rs wk ∧ W σ 6 s ∧ ¬W σ 5 s) ∨
    (¬KRKSixPlyHistory.Clear s.val sk rs wk ∧ W σ 8 s ∧ ¬W σ 7 s) := by
  have win : F σ s := ⟨8,cert⟩
  by_cases last : LastReply sk rs wk
  · have noClaim := weak_force_no_claim ongoing turn win
    exact Or.inl ⟨last,(rule_two_iff material ongoing turn).mpr ⟨last,noClaim⟩,weak_not_one ongoing turn⟩
  by_cases four : KRKGlobalWeakBand.Clear s.val sk rs wk
  · refine Or.inr (Or.inl ⟨last,four,(KRKFourPlyExact.rule_four_iff material ongoing turn).mpr four,?_⟩)
    intro cert
    exact last ((rule_two_iff material ongoing turn).mp (KRKDistanceParity.weak_three_two turn cert)).1
  by_cases six : KRKSixPlyHistory.Clear s.val sk rs wk
  · refine Or.inr (Or.inr (Or.inl ⟨four,six,(KRKSixPlyExact.rule_six_iff material ongoing turn).mpr six,?_⟩))
    intro cert
    exact four ((KRKFourPlyExact.rule_four_iff material ongoing turn).mp (KRKDistanceParity.weak_five_four turn cert))
  · refine Or.inr (Or.inr (Or.inr ⟨six,sufficient material ongoing turn ((rule_eight_iff material ongoing turn).mp cert),?_⟩))
    intro cert
    exact six ((KRKSixPlyExact.rule_six_iff material ongoing turn).mp (KRKSixPlyExact.weak_seven_six turn cert))

end EndgameChess.Rules.KRKEightPlyExact
