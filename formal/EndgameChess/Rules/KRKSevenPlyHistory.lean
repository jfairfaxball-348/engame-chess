import EndgameChess.Rules.KRKSevenEntry
import EndgameChess.Rules.KRKFivePlyExact

namespace EndgameChess.Rules.KRKSevenPlyHistory
open EndgameChess.KK KRKNativeFrame RawHistoryLayer KRKHolding
open KRKSevenSlots (Kind point frame)
set_option maxHeartbeats 400000

def Live (sk rs wk : Square) : Prop := ∃ t, KRKCornerWeakBand.Guard sk rs wk t

def KingPoints (s : RawTrace.State) (sk rs wk : Square) : Prop :=
  let g := frame wk
  ∃ i : Kind, dInf (g.f sk) (point i) = 1 ∧ point i ≠ g.f rs ∧ 2 ≤ dInf (point i) (g.f wk) ∧
    KRKSixGlobal.Region (g.r (point i)) rs wk ∧ Live (g.r (point i)) rs wk ∧
      KRKSevenPrefix.SixAfter s ⟨sk,g.r (point i),none⟩ (g.r (point i)) rs wk

def RookRays (s : RawTrace.State) (sk rs wk : Square) : Prop :=
  let g := frame wk
  ∃ i : Kind, g.f sk = point i ∧ ∃ a : KRKCornerSlotBarriers.Axis, ∃ v : Fin 8,
    RookSees (g.f rs) (a.target (g.f rs) v) (g.f sk) (g.f wk) ∧
      a.target (g.f rs) v ≠ g.f sk ∧ a.target (g.f rs) v ≠ g.f wk ∧
      KRKSixGlobal.Region sk (g.r (a.target (g.f rs) v)) wk ∧ Live sk (g.r (a.target (g.f rs) v)) wk ∧
      KRKSevenPrefix.SixAfter s ⟨rs,g.r (a.target (g.f rs) v),none⟩ sk (g.r (a.target (g.f rs) v)) wk

/-- Explicit twenty-point king entries, rook lines and original-trace key
tests. No future winning/holding predicate or legal-move search occurs. -/
def Clear (s : RawTrace.State) (sk rs wk : Square) : Prop :=
  KRKImmediate.MateNow sk rs wk ∨ KingPoints s sk rs wk ∨ RookRays s sk rs wk

theorem entry_certificate {s : State} {σ : Colour} {sk rs wk ns nr : Square} {m : Move}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s) (turn : (erase s).turn = σ)
    (legal : isLegal (erase s) m = true) (next : IsKRK (play (erase s) m) σ ns nr wk)
    (region : KRKSixGlobal.Region ns nr wk) (live : Live ns nr wk)
    (clear : KRKSevenPrefix.SixAfter s.val m ns nr wk) : W σ 7 s := by
  let v : State := ⟨RawTrace.append s.val m legal,
    ((StoppedHistory.append_and_reply_lifting s.val).1 m legal).mpr ⟨s.property,ongoing⟩⟩
  have nextV : IsKRK (erase v) σ ns nr wk := next
  have nextTurn : (erase v).turn = σ.opp := by change (play (erase s) m).turn = σ.opp; rw [play_turn,turn]
  have evaluated : KRKSixPlyHistory.Clear v.val ns nr wk :=
    (KRKSevenPrefix.six_append_iff material turn legal).mpr clear
  have board : MateWithin σ 6 (erase v) :=
    (KRKSixGlobal.kernel_six_iff nextV nextTurn (KRKEdgeDepth.arrival_far ⟨m,legal,rfl⟩ next)).mpr
      (Or.inr ⟨region,clear.1,live⟩)
  have nonempty : ∃ r, Legal (erase v) r := by
    obtain ⟨t,guard⟩ := live
    exact ⟨_,⟨_,KRKCornerWeakBand.guard_legal nextV nextTurn guard,rfl⟩⟩
  have childOngoing : Ongoing v := (RawAdjudication.ongoing_iff v.val).mpr
    ⟨forceMate_not_dead ⟨6,board⟩,nonempty,by have := evaluated.2.1; omega,by have := evaluated.2.2.1; omega⟩
  have child := KRKSixPlyHistory.sufficient nextV childOngoing nextTurn evaluated
  exact Or.inr ⟨ongoing,Or.inl ⟨turn,v,⟨m,legal,rfl⟩,child⟩⟩

theorem sufficient {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s) (turn : (erase s).turn = σ)
    (clear : Clear s.val sk rs wk) : W σ 7 s := by
  rcases clear with immediate | points | rays
  · obtain ⟨v,edge,goal⟩ := (KRKImmediate.admitted_immediate_iff material ongoing turn).mpr immediate
    exact Or.inr ⟨ongoing,Or.inl ⟨turn,v,edge,Or.inl goal⟩⟩
  · obtain ⟨i,mappedDistance,apart,mappedFar,region,live,clear⟩ := points
    have distance : dInf sk ((frame wk).r (point i)) = 1 := by
      have preserved := (frame wk).distance sk ((frame wk).r (point i))
      rw [(frame wk).right_inv,mappedDistance] at preserved
      exact preserved.symm
    have notRook : (frame wk).r (point i) ≠ rs := by
      intro equal
      have same := congrArg (frame wk).f equal
      rw [(frame wk).right_inv] at same
      exact apart same
    have far : 2 ≤ dInf ((frame wk).r (point i)) wk := by
      have preserved := (frame wk).distance ((frame wk).r (point i)) wk
      rw [(frame wk).right_inv] at preserved
      rwa [←preserved]
    have legal := KRKOrdinaryEntry.king_legal material turn distance notRook far
    exact entry_certificate material ongoing turn legal (KRKThreePly.canonical_king_material material turn distance notRook far)
      region live clear
  · obtain ⟨i,equal,a,v,mappedSees,notKing,notWeak,region,live,clear⟩ := rays
    have sees : RookSees rs ((frame wk).r (a.target ((frame wk).f rs) v)) sk wk := by
      apply ((frame wk).sees _ _ _ _).mp
      simpa only [(frame wk).right_inv] using mappedSees
    have apartKing : (frame wk).r (a.target ((frame wk).f rs) v) ≠ sk := by
      intro equal
      have same := congrArg (frame wk).f equal
      rw [(frame wk).right_inv] at same
      exact notKing same
    have apartWeak : (frame wk).r (a.target ((frame wk).f rs) v) ≠ wk := by
      intro equal
      have same := congrArg (frame wk).f equal
      rw [(frame wk).right_inv] at same
      exact notWeak same
    have legal := KRKOrdinaryEntry.rook_legal material turn sees apartKing apartWeak (KRKWeakBranch.admitted_far material)
    exact entry_certificate material ongoing turn legal (KRKMatingMove.rook_move_model material turn legal rfl).1 region live clear

theorem entry_kernel {s : RawTrace.State} {σ : Colour} {sk rs wk ns nr : Square} {m : Move}
    (material : IsKRK (RawTrace.erase s) σ sk rs wk) (turn : (RawTrace.erase s).turn = σ)
    (legal : isLegal (RawTrace.erase s) m = true) (next : IsKRK (play (RawTrace.erase s) m) σ ns nr wk)
    (region : KRKSixGlobal.Region ns nr wk) (live : Live ns nr wk)
    (clear : KRKSevenPrefix.SixAfter s m ns nr wk) : MateWithin σ 7 (RawTrace.erase s) := by
  have nextTurn : (play (RawTrace.erase s) m).turn = σ.opp := by rw [play_turn,turn]
  have board := (KRKSixGlobal.kernel_six_iff next nextTurn (KRKEdgeDepth.arrival_far ⟨m,legal,rfl⟩ next)).mpr
    (Or.inr ⟨region,clear.1,live⟩)
  exact mateWithin_choose turn ⟨m,legal,rfl⟩ board

theorem clear_kernel {s : RawTrace.State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (RawTrace.erase s) σ sk rs wk) (turn : (RawTrace.erase s).turn = σ)
    (far : 2 ≤ dInf sk wk) (notCheck : ¬RookSees rs wk sk wk)
    (clear : Clear s sk rs wk) : MateWithin σ 7 (RawTrace.erase s) := by
  rcases clear with immediate | points | rays
  · obtain ⟨r,edge,goal⟩ := (KRKImmediate.immediate_iff material turn far notCheck).mpr immediate
    exact mateWithin_choose turn edge (Or.inl goal)
  · obtain ⟨i,mappedDistance,apart,mappedFar,region,live,clear⟩ := points
    have distance : dInf sk ((frame wk).r (point i)) = 1 := by
      have preserved := (frame wk).distance sk ((frame wk).r (point i))
      rw [(frame wk).right_inv,mappedDistance] at preserved
      exact preserved.symm
    have notRook : (frame wk).r (point i) ≠ rs := by
      intro equal
      have same := congrArg (frame wk).f equal
      rw [(frame wk).right_inv] at same
      exact apart same
    have far : 2 ≤ dInf ((frame wk).r (point i)) wk := by
      have preserved := (frame wk).distance ((frame wk).r (point i)) wk
      rw [(frame wk).right_inv] at preserved
      rwa [←preserved]
    have legal := KRKOrdinaryEntry.king_legal material turn distance notRook far
    exact entry_kernel material turn legal (KRKThreePly.canonical_king_material material turn distance notRook far)
      region live clear
  · obtain ⟨i,equal,a,v,mappedSees,notKing,notWeak,region,live,clear⟩ := rays
    have sees : RookSees rs ((frame wk).r (a.target ((frame wk).f rs) v)) sk wk := by
      apply ((frame wk).sees _ _ _ _).mp
      simpa only [(frame wk).right_inv] using mappedSees
    have apartKing : (frame wk).r (a.target ((frame wk).f rs) v) ≠ sk := by
      intro equal
      have same := congrArg (frame wk).f equal
      rw [(frame wk).right_inv] at same
      exact notKing same
    have apartWeak : (frame wk).r (a.target ((frame wk).f rs) v) ≠ wk := by
      intro equal
      have same := congrArg (frame wk).f equal
      rw [(frame wk).right_inv] at same
      exact notWeak same
    have legal := KRKOrdinaryEntry.rook_legal material turn sees apartKing apartWeak far
    exact entry_kernel material turn legal (KRKMatingMove.rook_move_model material turn legal rfl).1 region live clear

theorem necessary {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s) (turn : (erase s).turn = σ)
    (high : 92 ≤ RawClock.clock s.val.trace) (win : F σ s) : Clear s.val sk rs wk := by
  obtain ⟨n,cert⟩ := win
  cases n with
  | zero => exact False.elim (opp_ne σ (turn.symm.trans cert.1))
  | succ n =>
    rcases cert with goal | ⟨_,chosen | defended⟩
    · exact False.elim (opp_ne σ (turn.symm.trans goal.1))
    · obtain ⟨_,v,edge,child⟩ := chosen
      have childWin : F σ v := ⟨n,child⟩
      obtain ⟨_,clock⟩ := KRKHighClock.winning_child_quiet material edge childWin
      obtain ⟨m,legal,rawEq⟩ := edge
      have endpoint : erase v = play (erase s) m := congrArg RawTrace.erase rawEq
      obtain ⟨ns,nr,next⟩ := krk_strong_material material turn legal
      have nextV : IsKRK (erase v) σ ns nr wk := by rwa [endpoint]
      have nextTurn : (erase v).turn = σ.opp := by rw [endpoint,play_turn,turn]
      by_cases childOngoing : Ongoing v
      · have deadline := (KRKDeadline.winning_deadline nextV childWin).2
        have budget : KRKDeadline.budget σ v ≤ 7 := by
          have notStrong : (erase v).turn ≠ σ := fun h => opp_ne σ (h.symm.trans nextTurn)
          simp only [KRKDeadline.budget,notStrong,↓reduceIte]
          omega
        have six := KRKSixGeometry.weak_seven_six nextV nextTurn (mateWithin_mono deadline budget)
        have notMate : ¬MatedK (erase v) := fun mate => mate.2 (((RawAdjudication.ongoing_iff v.val).mp childOngoing).2.1)
        have evaluated := (KRKSixPlyHistory.high_clock_force_iff nextV childOngoing nextTurn (by omega)).mp childWin
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

theorem high_clock_force_iff {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s) (turn : (erase s).turn = σ)
    (high : 92 ≤ RawClock.clock s.val.trace) : F σ s ↔ Clear s.val sk rs wk :=
  ⟨necessary material ongoing turn high,fun clear => ⟨7,sufficient material ongoing turn clear⟩⟩

theorem high_clock_actual_iff {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s) (turn : (erase s).turn = σ)
    (high : 92 ≤ RawClock.clock s.val.trace) : KRKWinning.ActualWin σ s ↔ Clear s.val sk rs wk :=
  (KRKWinning.actual_win_iff_force (Or.inl ⟨sk,rs,wk,material⟩)).trans
    (high_clock_force_iff material ongoing turn high)

theorem high_clock_draw_iff {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s) (turn : (erase s).turn = σ)
    (high : 92 ≤ RawClock.clock s.val.trace) :
    (RuleHold σ s ∧ RuleHold σ.opp s) ↔ ¬Clear s.val sk rs wk := by
  have dual := holding_iff_not_force (σ := σ) (c := σ.opp) (s := s) (Or.inl ⟨sk,rs,wk,material⟩)
  have weakHold : RuleHold σ.opp s ↔ ¬Clear s.val sk rs wk := by
    simpa only [opp_opp,high_clock_force_iff material ongoing turn high] using dual
  exact ⟨fun holds => weakHold.mp holds.2,fun outside => ⟨KRKHighClock.strong_hold material,weakHold.mpr outside⟩⟩

theorem high_clock_distance_cases {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s) (turn : (erase s).turn = σ)
    (high : 92 ≤ RawClock.clock s.val.trace) (win : F σ s) :
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
  · refine Or.inr (Or.inr (Or.inr ⟨five,sufficient material ongoing turn ((high_clock_force_iff material ongoing turn high).mp win),?_⟩))
    intro six
    exact five ((KRKFivePlyExact.rule_five_iff material ongoing turn).mp (KRKFivePlyExact.strong_six_five turn six))

end EndgameChess.Rules.KRKSevenPlyHistory
