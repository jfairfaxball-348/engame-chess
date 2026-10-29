import EndgameChess.Rules.KRKSevenPlyHistory
import EndgameChess.Rules.KRKSixPlyExact

namespace EndgameChess.Rules.KRKSevenPlyExact
open EndgameChess.KK KRKNativeFrame RawHistoryLayer KRKHolding
open KRKSevenSlots (Kind point frame)
open KRKSevenPlyHistory (Clear Live)
set_option maxHeartbeats 400000

theorem necessary {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s) (turn : (erase s).turn = σ)
    (cert : W σ 7 s) : Clear s.val sk rs wk := by
  rcases cert with goal | ⟨_,chosen | defended⟩
  · exact False.elim (opp_ne σ (turn.symm.trans goal.1))
  · obtain ⟨_,v,edge,child⟩ := chosen
    have childWin : F σ v := ⟨6,child⟩
    obtain ⟨_,clock⟩ := KRKHighClock.winning_child_quiet material edge childWin
    obtain ⟨m,legal,rawEq⟩ := edge
    have endpoint : erase v = play (erase s) m := congrArg RawTrace.erase rawEq
    obtain ⟨ns,nr,next⟩ := krk_strong_material material turn legal
    have nextV : IsKRK (erase v) σ ns nr wk := by rwa [endpoint]
    have nextTurn : (erase v).turn = σ.opp := by rw [endpoint,play_turn,turn]
    by_cases childOngoing : Ongoing v
    · have six := raw_ruleMateWithin_project v σ 6 child
      have notMate : ¬MatedK (erase v) := fun mate => mate.2 (((RawAdjudication.ongoing_iff v.val).mp childOngoing).2.1)
      have evaluated := (KRKSixPlyExact.rule_six_iff nextV childOngoing nextTurn).mp child
      have rawClear : KRKSixPlyHistory.Clear (RawTrace.append s.val m legal) ns nr wk := by rw [←rawEq]; exact evaluated
      have clearAfter := (KRKSevenPrefix.six_append_iff material turn legal).mp rawClear
      have live : Live ns nr wk := by
        obtain ⟨r,legalReply⟩ := ((RawAdjudication.ongoing_iff v.val).mp childOngoing).2.1
        obtain ⟨t,_,step⟩ := krk_safe_reply nextV nextTurn evaluated.1 legalReply
        exact ⟨t,KRKCornerWeakBand.step_guard step⟩
      rw [endpoint] at six notMate
      rcases KRKSevenEntry.six_entry_move material turn legal next notMate six with
        ⟨src,promo,distance,moved,region⟩ | ⟨src,promo,sees,moved,region⟩
      · have nsEq := KRKCastleFour.king_square next (t := m.dst) (by rw [moved.2.2.2]; exact krkBoard_sk)
        have nrEq := KRKCastleFour.rook_square next (t := rs) (by rw [moved.2.2.2]; exact krkBoard_rs moved.1)
        rw [←nsEq,←nrEq] at live clearAfter
        obtain ⟨i,equal⟩ := KRKSevenSlots.region_point region
        have actual := (frame wk).preimage_eq equal
        have mappedDistance := (frame wk).distance sk m.dst
        rw [equal,distance] at mappedDistance
        have apart : point i ≠ (frame wk).f rs := by rw [←equal]; exact (frame wk).ne_iff.mpr moved.1
        have mappedFar : 2 ≤ dInf (point i) ((frame wk).f wk) := by
          rw [←equal,(frame wk).distance]
          exact KRKEdgeDepth.arrival_far ⟨m,legal,rfl⟩ moved
        have canonical : m = ⟨sk,m.dst,none⟩ := by
          cases m; simp only [Move.mk.injEq]; exact ⟨src,True.intro,promo⟩
        rw [canonical,actual] at clearAfter
        rw [actual] at live region
        exact Or.inr (Or.inl ⟨i,mappedDistance,apart,mappedFar,region,live,clearAfter⟩)
      · have nsEq := KRKCastleFour.king_square next (t := sk) (by rw [moved.2.2.2]; exact krkBoard_sk)
        have nrEq := KRKCastleFour.rook_square next (t := m.dst) (by rw [moved.2.2.2]; exact krkBoard_rs moved.1)
        rw [←nsEq,←nrEq] at live clearAfter
        obtain ⟨i,equal⟩ := KRKSevenSlots.region_point region
        have mappedSees := ((frame wk).sees rs m.dst sk wk).mpr sees
        obtain ⟨a,v,target⟩ := KRKCornerSlotBarriers.line_target mappedSees.1
        have actual := (frame wk).preimage_eq target
        have apartKing : a.target ((frame wk).f rs) v ≠ (frame wk).f sk := by
          rw [←target]; exact (frame wk).ne_iff.mpr moved.1.symm
        have apartWeak : a.target ((frame wk).f rs) v ≠ (frame wk).f wk := by
          rw [←target]; exact (frame wk).ne_iff.mpr moved.2.2.1
        rw [target] at mappedSees
        have canonical : m = ⟨rs,m.dst,none⟩ := by
          cases m; simp only [Move.mk.injEq]; exact ⟨src,True.intro,promo⟩
        rw [canonical,actual] at clearAfter
        rw [actual] at live region
        exact Or.inr (Or.inr ⟨i,equal,a,v,mappedSees,apartKing,apartWeak,region,live,clearAfter⟩)
    · have goal := (KRKHighClock.terminal_force_iff_goal childOngoing).mp childWin
      exact Or.inl ((KRKImmediate.admitted_immediate_iff material ongoing turn).mp ⟨v,⟨m,legal,rawEq⟩,goal⟩)
  · exact False.elim (opp_ne σ (turn.symm.trans defended.1))


theorem rule_seven_iff {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s) (turn : (erase s).turn = σ) :
    W σ 7 s ↔ Clear s.val sk rs wk := ⟨necessary material ongoing turn,KRKSevenPlyHistory.sufficient material ongoing turn⟩

theorem strong_eight_seven {s : State} {σ : Colour} (turn : (erase s).turn = σ)
    (cert : W σ 8 s) : W σ 7 s := by
  rcases cert with goal | ⟨ongoing,chosen | defended⟩
  · exact Or.inl goal
  · obtain ⟨_,t,edge,child⟩ := chosen
    have weak : (erase t).turn = σ.opp := by
      have changed : (erase t).turn = (erase s).turn.opp := turn_of_legal (RawTrace.raw_step_sound edge)
      rw [changed,turn]
    exact Or.inr ⟨ongoing,Or.inl ⟨turn,t,edge,KRKSixPlyExact.weak_seven_six weak child⟩⟩
  · exact False.elim (opp_ne σ (turn.symm.trans defended.1))

theorem weak_nine_eight {s : State} {σ : Colour} (turn : (erase s).turn = σ.opp)
    (cert : W σ 9 s) : W σ 8 s := by
  rcases cert with goal | ⟨ongoing,chosen | defended⟩
  · exact Or.inl goal
  · exact False.elim (opp_ne σ (chosen.1.symm.trans turn))
  · refine Or.inr ⟨ongoing,Or.inr ⟨turn,defended.2.1,defended.2.2.1,?_⟩⟩
    intro t edge
    have strong : (erase t).turn = σ := by
      have changed : (erase t).turn = (erase s).turn.opp := turn_of_legal (RawTrace.raw_step_sound edge)
      rw [changed,turn,opp_opp]
    exact strong_eight_seven strong (defended.2.2.2 t edge)

theorem distance_cases {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s) (turn : (erase s).turn = σ)
    (cert : W σ 7 s) :
    (KRKImmediate.MateNow sk rs wk ∧ W σ 1 s ∧ ¬W σ 0 s) ∨
    (¬KRKImmediate.MateNow sk rs wk ∧ KRKFramedHistory.GlobalClear s.val sk rs wk ∧ W σ 3 s ∧ ¬W σ 2 s) ∨
    (¬KRKFramedHistory.GlobalClear s.val sk rs wk ∧ KRKFivePlyHistory.Clear s.val sk rs wk ∧ W σ 5 s ∧ ¬W σ 4 s) ∨
    (¬KRKFivePlyHistory.Clear s.val sk rs wk ∧ W σ 7 s ∧ ¬W σ 6 s) := by
  by_cases immediate : KRKImmediate.MateNow sk rs wk
  · obtain ⟨v,edge,goal⟩ := (KRKImmediate.admitted_immediate_iff material ongoing turn).mpr immediate
    refine Or.inl ⟨immediate,Or.inr ⟨ongoing,Or.inl ⟨turn,v,edge,goal⟩⟩,?_⟩
    intro zero
    exact opp_ne σ (turn.symm.trans zero.1)
  by_cases three : KRKFramedHistory.GlobalClear s.val sk rs wk
  · exact Or.inr (Or.inl ⟨immediate,three,(KRKThreePlyExact.global_three_iff material ongoing turn).mpr three,
      KRKThreePlyExact.not_immediate_not_two material ongoing turn immediate⟩)
  by_cases five : KRKFivePlyHistory.Clear s.val sk rs wk
  · refine Or.inr (Or.inr (Or.inl ⟨three,five,(KRKFivePlyExact.rule_five_iff material ongoing turn).mpr five,?_⟩))
    intro four
    exact three ((KRKThreePlyExact.global_three_iff material ongoing turn).mp (KRKDistanceParity.strong_four_three turn four))
  · refine Or.inr (Or.inr (Or.inr ⟨five,KRKSevenPlyHistory.sufficient material ongoing turn ((rule_seven_iff material ongoing turn).mp cert),?_⟩))
    intro six
    exact five ((KRKFivePlyExact.rule_five_iff material ongoing turn).mp (KRKFivePlyExact.strong_six_five turn six))

end EndgameChess.Rules.KRKSevenPlyExact
