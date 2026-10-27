import EndgameChess.Rules.KRKThreePlyExact
import EndgameChess.Rules.KRKGlobalWeakBand

namespace EndgameChess.Rules.KRKFourPlyExact
open EndgameChess.KK KRKThreePly KRKLastReply KRKOppositionHistory KRKWeakBranch RawHistoryLayer KRKHolding KRKNativeFrame
open KRKCornerWeakBand (Guard guard_legal step_guard)
set_option maxHeartbeats 500000

theorem necessary {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ.opp) (cert : W σ 4 s) :
    KRKGlobalWeakBand.Clear s.val sk rs wk := by
  have win : F σ s := ⟨4,cert⟩
  have safe : SafeRook sk rs wk := by
    exact krk_force_weak_safe material turn ⟨4, raw_ruleMateWithin_project s σ 4 cert⟩
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
  have childCert : W σ 3 (weakChild s ongoing wk t legal) := by
    rcases cert with goal | ⟨_,chosen | defended⟩
    · exact False.elim (goal.2.2 (((RawAdjudication.ongoing_iff s.val).mp ongoing).2.1))
    · exact False.elim (opp_ne σ (chosen.1.symm.trans turn))
    · exact defended.2.2.2 _ ⟨_,legal,rfl⟩
  have next := weak_material_after material turn safe legal
  have nextTurn : (erase (weakChild s ongoing wk t legal)).turn = σ := by
    change (play (erase s) _).turn = σ; simp only [play_turn,turn,opp_opp]
  have history := (KRKThreePlyExact.history_three_iff (s := weakChild s ongoing wk t legal) next
    (child_ongoing_of_force material ongoing turn legal childWin) nextTurn).mp childCert
  have depth := KRKFourPlyEscape.three_depth_zero (history_geometry history)
  have normal := normalize_spec depth
  exact ⟨(claims.2.2 _ legal).2, depth,
    (KRKFramedPrefix.history_append_iff (normalize t) material turn safe legal normal.1 normal.2).mp history⟩

theorem rule_four_iff {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s) (turn : (erase s).turn = σ.opp) :
    W σ 4 s ↔ KRKGlobalWeakBand.Clear s.val sk rs wk :=
  ⟨necessary material ongoing turn, KRKGlobalWeakBand.sufficient material ongoing turn⟩

end EndgameChess.Rules.KRKFourPlyExact
