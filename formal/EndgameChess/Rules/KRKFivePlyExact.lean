import EndgameChess.Rules.KRKFourPlyExact
import EndgameChess.Rules.KRKFivePlyHistory

namespace EndgameChess.Rules.KRKFivePlyExact
open EndgameChess.KK KRKThreePly KRKLastReply KRKNativeFrame KRKFourGeometry RawHistoryLayer KRKHolding
open KRKFourSlots (Kind Valid king Region)
open KRKFivePlyHistory (Live KingPoints RookRays Clear sufficient)
set_option maxHeartbeats 400000

theorem necessary {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ) (cert : W σ 5 s) : Clear s.val sk rs wk := by
  rcases cert with goal | ⟨_, chosen | defended⟩
  · exact False.elim (opp_ne σ (turn.symm.trans goal.1))
  · obtain ⟨_,v,edge,child⟩ := chosen
    have childWin : KRKHolding.F σ v := ⟨4,child⟩
    obtain ⟨_,clock⟩ := KRKHighClock.winning_child_quiet material edge childWin
    obtain ⟨m,legal,rawEq⟩ := edge
    have endpoint : RawHistoryLayer.erase v = play (RawHistoryLayer.erase s) m := congrArg RawTrace.erase rawEq
    obtain ⟨ns,nr,next⟩ := krk_strong_material material turn legal
    have nextV : IsKRK (RawHistoryLayer.erase v) σ ns nr wk := by rwa [endpoint]
    have nextTurn : (RawHistoryLayer.erase v).turn = σ.opp := by rw [endpoint,play_turn,turn]
    by_cases childOngoing : RawHistoryLayer.Ongoing v
    · have four := raw_ruleMateWithin_project v σ 4 child
      have noMate : ¬MatedK (RawHistoryLayer.erase v) := by
        intro mate
        exact mate.2 (((RawAdjudication.ongoing_iff v.val).mp childOngoing).2.1)
      rw [endpoint] at four noMate
      have geometry := global_shape_necessary next (by rw [play_turn,turn])
        (KRKEdgeDepth.arrival_far ⟨m,legal,rfl⟩ next) noMate four
      have normal := normalize_spec geometry.1
      have evaluated := (KRKFourPlyExact.rule_four_iff nextV childOngoing nextTurn).mp child
      have rawClear : KRKGlobalWeakBand.Clear (RawTrace.append s.val m legal) ns nr wk := by
        rw [←rawEq]; exact evaluated
      have clearAfter := (KRKStrongPrefix.weak_append_iff material turn legal).mp rawClear
      have live : Live ns nr wk := by
        obtain ⟨r,edge⟩ := ((RawAdjudication.ongoing_iff v.val).mp childOngoing).2.1
        obtain ⟨t,_,step⟩ := krk_safe_reply nextV nextTurn evaluated.1 edge
        exact ⟨t,KRKCornerWeakBand.step_guard step⟩
      refine Or.inr ⟨geometry.1,?_⟩
      rcases KRKCastleFour.four_entry_move material turn legal next noMate four with
        ⟨src,promo,distance,moved,shape⟩ | ⟨src,promo,sees,moved,shape⟩
      · have nsEq := KRKCastleFour.king_square next (t := m.dst) (by rw [moved.2.2.2]; exact krkBoard_sk)
        have nrEq := KRKCastleFour.rook_square next (t := rs) (by rw [moved.2.2.2]; exact krkBoard_rs moved.1)
        rw [←nsEq,←nrEq] at live clearAfter
        obtain ⟨i,valid,equal,region⟩ := (KRKFourSlots.shape_iff normal.1 normal.2).mp shape
        have actual := (normalize wk).preimage_eq equal
        have mappedDistance := (normalize wk).distance sk m.dst
        rw [equal,distance] at mappedDistance
        have apart : king ((normalize wk).f wk) i ≠ (normalize wk).f rs := by
          rw [←equal]; exact (normalize wk).ne_iff.mpr moved.1
        have mappedFar : 2 ≤ dInf (king ((normalize wk).f wk) i) ((normalize wk).f wk) := by
          rw [←equal,(normalize wk).distance]
          exact KRKEdgeDepth.arrival_far ⟨m,legal,rfl⟩ moved
        have canonical : m = ⟨sk,m.dst,none⟩ := by
          cases m; simp only [Move.mk.injEq]; exact ⟨src,True.intro,promo⟩
        rw [canonical,actual] at clearAfter
        rw [actual] at live
        exact Or.inl ⟨i,valid,region,mappedDistance,apart,mappedFar,live,clearAfter⟩
      · have nsEq := KRKCastleFour.king_square next (t := sk) (by rw [moved.2.2.2]; exact krkBoard_sk)
        have nrEq := KRKCastleFour.rook_square next (t := m.dst) (by rw [moved.2.2.2]; exact krkBoard_rs moved.1)
        rw [←nsEq,←nrEq] at live clearAfter
        obtain ⟨i,valid,equal,region⟩ := (KRKFourSlots.shape_iff normal.1 normal.2).mp shape
        have mappedSees := ((normalize wk).sees rs m.dst sk wk).mpr sees
        obtain ⟨a,v,target⟩ := KRKCornerSlotBarriers.line_target mappedSees.1
        have actual := (normalize wk).preimage_eq target
        have apartKing : a.target ((normalize wk).f rs) v ≠ (normalize wk).f sk := by
          rw [←target]; exact (normalize wk).ne_iff.mpr moved.1.symm
        have apartWeak : a.target ((normalize wk).f rs) v ≠ (normalize wk).f wk := by
          rw [←target]; exact (normalize wk).ne_iff.mpr moved.2.2.1
        rw [target] at mappedSees region
        have canonical : m = ⟨rs,m.dst,none⟩ := by
          cases m; simp only [Move.mk.injEq]; exact ⟨src,True.intro,promo⟩
        rw [canonical,actual] at clearAfter
        rw [actual] at live
        exact Or.inr ⟨i,valid,equal,a,v,mappedSees,apartKing,apartWeak,region,live,clearAfter⟩
    · have goal := (KRKHighClock.terminal_force_iff_goal childOngoing).mp childWin
      exact Or.inl ((KRKImmediate.admitted_immediate_iff material ongoing turn).mp ⟨v,⟨m,legal,rawEq⟩,goal⟩)
  · exact False.elim (opp_ne σ (turn.symm.trans defended.1))


theorem rule_five_iff {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s) (turn : (erase s).turn = σ) :
    W σ 5 s ↔ Clear s.val sk rs wk :=
  ⟨necessary material ongoing turn,sufficient material ongoing turn⟩

theorem strong_six_five {s : State} {σ : Colour} (turn : (erase s).turn = σ)
    (cert : W σ 6 s) : W σ 5 s := by
  rcases cert with goal | ⟨ongoing,chosen | defended⟩
  · exact Or.inl goal
  · obtain ⟨_,t,edge,child⟩ := chosen
    have weak : (erase t).turn = σ.opp := by
      have changed : (erase t).turn = (erase s).turn.opp := turn_of_legal (RawTrace.raw_step_sound edge)
      rw [changed,turn]
    exact Or.inr ⟨ongoing,Or.inl ⟨turn,t,edge,KRKDistanceParity.weak_five_four weak child⟩⟩
  · exact False.elim (opp_ne σ (turn.symm.trans defended.1))

end EndgameChess.Rules.KRKFivePlyExact
