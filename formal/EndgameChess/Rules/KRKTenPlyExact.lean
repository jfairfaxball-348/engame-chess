import EndgameChess.Rules.KRKTenPlyHistory

namespace EndgameChess.Rules.KRKTenPlyExact
open EndgameChess.KK KRKThreePly KRKLastReply KRKOppositionHistory KRKWeakBranch RawHistoryLayer KRKHolding
open KRKCornerWeakBand (Guard guard_legal step_guard)
open KRKTenPlyHistory (Clear sufficient after_weak_iff)
set_option maxHeartbeats 400000

theorem necessary {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ.opp) (cert : W σ 10 s) :
    Clear s.val sk rs wk := by
  have win : F σ s := ⟨10,cert⟩
  have safe : SafeRook sk rs wk := krk_force_weak_safe material turn ⟨10,raw_ruleMateWithin_project s σ 10 cert⟩
  have allCert : ∀ v, BoardStep s v → W σ 9 v := by
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
  have evaluated := (KRKNinePlyExact.rule_nine_iff (s := weakChild s ongoing wk t legal)
    next (child_ongoing_of_force material ongoing turn legal childWin) nextTurn).mp (allCert _ ⟨_,legal,rfl⟩)
  exact ⟨(claims.2.2 _ legal).2,(after_weak_iff material turn safe legal).mp evaluated⟩


theorem rule_ten_iff {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s) (turn : (erase s).turn = σ.opp) :
    W σ 10 s ↔ Clear s.val sk rs wk := ⟨necessary material ongoing turn,sufficient material ongoing turn⟩

theorem high_clock_distance_split {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s) (turn : (erase s).turn = σ.opp)
    (high : 89 ≤ RawClock.clock s.val.trace) (win : F σ s) :
    (KRKEightPlyHistory.Clear s.val sk rs wk ∧ W σ 8 s) ∨
    (¬KRKEightPlyHistory.Clear s.val sk rs wk ∧ W σ 10 s ∧ ¬W σ 9 s) := by
  by_cases eight : KRKEightPlyHistory.Clear s.val sk rs wk
  · exact Or.inl ⟨eight,KRKEightPlyHistory.sufficient material ongoing turn eight⟩
  · refine Or.inr ⟨eight,sufficient material ongoing turn
      ((KRKTenPlyHistory.high_clock_force_iff material ongoing turn high).mp win),?_⟩
    intro nine
    exact eight ((KRKEightPlyExact.rule_eight_iff material ongoing turn).mp
      (KRKSevenPlyExact.weak_nine_eight turn nine))

theorem high_clock_exact_distance {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s) (turn : (erase s).turn = σ.opp)
    (high : 89 ≤ RawClock.clock s.val.trace) (win : F σ s) :
    ∃ d : Nat, (d = 2 ∨ d = 4 ∨ d = 6 ∨ d = 8 ∨ d = 10) ∧ W σ d s ∧ ¬W σ (d-1) s := by
  rcases high_clock_distance_split material ongoing turn high win with ⟨_,eight⟩ | ⟨_,ten,notNine⟩
  · rcases KRKEightPlyExact.distance_cases material ongoing turn eight with
      ⟨_,two,notOne⟩ | ⟨_,_,four,notThree⟩ | ⟨_,_,six,notFive⟩ | ⟨_,eight,notSeven⟩
    · exact ⟨2,by decide,two,notOne⟩
    · exact ⟨4,by decide,four,notThree⟩
    · exact ⟨6,by decide,six,notFive⟩
    · exact ⟨8,by decide,eight,notSeven⟩
  · exact ⟨10,by decide,ten,notNine⟩

end EndgameChess.Rules.KRKTenPlyExact
