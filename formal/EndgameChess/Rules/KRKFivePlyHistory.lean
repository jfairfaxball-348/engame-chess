import EndgameChess.Rules.KRKFourSlots
import EndgameChess.Rules.KRKOrdinaryEntry
import EndgameChess.Rules.KRKThreePlyExact

namespace EndgameChess.Rules.KRKFivePlyHistory
open EndgameChess.KK KRKThreePly KRKLastReply KRKNativeFrame KRKFourGeometry RawHistoryLayer KRKHolding
open KRKFourSlots (Kind Valid king Region)
open KRKStrongPrefix (WeakAfter)
set_option maxHeartbeats 500000

def Live (sk rs wk : Square) : Prop := ∃ t, KRKCornerWeakBand.Guard sk rs wk t

def KingPoints (s : RawTrace.State) (sk rs wk : Square) : Prop :=
  let g := normalize wk
  ∃ i : Kind, Valid (g.f wk) i ∧ Region (g.f wk) (g.f rs) i ∧
    dInf (g.f sk) (king (g.f wk) i) = 1 ∧ king (g.f wk) i ≠ g.f rs ∧
      2 ≤ dInf (king (g.f wk) i) (g.f wk) ∧
      Live (g.r (king (g.f wk) i)) rs wk ∧
      WeakAfter s ⟨sk,g.r (king (g.f wk) i),none⟩ (g.r (king (g.f wk) i)) rs wk

def RookRays (s : RawTrace.State) (sk rs wk : Square) : Prop :=
  let g := normalize wk
  ∃ i : Kind, Valid (g.f wk) i ∧ g.f sk = king (g.f wk) i ∧
    ∃ a : KRKCornerSlotBarriers.Axis, ∃ v : Fin 8,
      RookSees (g.f rs) (a.target (g.f rs) v) (g.f sk) (g.f wk) ∧
      a.target (g.f rs) v ≠ g.f sk ∧ a.target (g.f rs) v ≠ g.f wk ∧
      Region (g.f wk) (a.target (g.f rs) v) i ∧
      Live sk (g.r (a.target (g.f rs) v)) wk ∧
      WeakAfter s ⟨rs,g.r (a.target (g.f rs) v),none⟩ sk (g.r (a.target (g.f rs) v)) wk

/-- Explicit finite coordinate/old-key formula, with no legal or future
outcome predicate. Slots restrict entries before the history tests are made. -/
def Clear (s : RawTrace.State) (sk rs wk : Square) : Prop :=
  KRKImmediate.MateNow sk rs wk ∨
    (KRKEdgeDepth.depth wk = 0 ∧ (KingPoints s sk rs wk ∨ RookRays s sk rs wk))

theorem entry_certificate {s : State} {σ : Colour} {sk rs wk ns nr : Square} {m : Move}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s) (turn : (erase s).turn = σ)
    (legal : isLegal (erase s) m = true) (next : IsKRK (play (erase s) m) σ ns nr wk)
    (live : Live ns nr wk) (clear : WeakAfter s.val m ns nr wk) : W σ 5 s := by
  let v : State := ⟨RawTrace.append s.val m legal,
    ((StoppedHistory.append_and_reply_lifting s.val).1 m legal).mpr ⟨s.property,ongoing⟩⟩
  have nextV : IsKRK (erase v) σ ns nr wk := next
  have nextTurn : (erase v).turn = σ.opp := by change (play (erase s) m).turn = σ.opp; rw [play_turn,turn]
  have evaluated : KRKGlobalWeakBand.Clear v.val ns nr wk :=
    (KRKStrongPrefix.weak_append_iff material turn legal).mpr clear
  have childOngoing := KRKStrongPrefix.weak_clear_ongoing nextV nextTurn evaluated live
  have child := KRKGlobalWeakBand.sufficient nextV childOngoing nextTurn evaluated
  exact Or.inr ⟨ongoing,Or.inl ⟨turn,v,⟨m,legal,rfl⟩,child⟩⟩

theorem sufficient {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s) (turn : (erase s).turn = σ)
    (clear : Clear s.val sk rs wk) : W σ 5 s := by
  rcases clear with immediate | ⟨depth,points | rays⟩
  · obtain ⟨v,edge,goal⟩ := (KRKImmediate.admitted_immediate_iff material ongoing turn).mpr immediate
    have child : W σ 4 v := Or.inl goal
    exact Or.inr ⟨ongoing,Or.inl ⟨turn,v,edge,child⟩⟩
  · obtain ⟨i,valid,region,mappedDistance,apart,mappedFar,live,clear⟩ := points
    have distance : dInf sk ((normalize wk).r (king ((normalize wk).f wk) i)) = 1 := by
      have preserved := (normalize wk).distance sk ((normalize wk).r (king ((normalize wk).f wk) i))
      rw [(normalize wk).right_inv,mappedDistance] at preserved
      exact preserved.symm
    have notRook : (normalize wk).r (king ((normalize wk).f wk) i) ≠ rs := by
      intro equal; have same := congrArg (normalize wk).f equal
      rw [(normalize wk).right_inv] at same
      exact apart same
    have far : 2 ≤ dInf ((normalize wk).r (king ((normalize wk).f wk) i)) wk := by
      have preserved := (normalize wk).distance ((normalize wk).r (king ((normalize wk).f wk) i)) wk
      rw [(normalize wk).right_inv] at preserved
      rwa [←preserved]
    have legal := KRKOrdinaryEntry.king_legal material turn distance notRook far
    exact entry_certificate material ongoing turn legal (canonical_king_material material turn distance notRook far) live clear
  · obtain ⟨i,valid,equal,a,v,mappedSees,notKing,notWeak,region,live,clear⟩ := rays
    have sees : RookSees rs ((normalize wk).r (a.target ((normalize wk).f rs) v)) sk wk := by
      apply ((normalize wk).sees _ _ _ _).mp
      simpa only [(normalize wk).right_inv] using mappedSees
    have apartKing : (normalize wk).r (a.target ((normalize wk).f rs) v) ≠ sk := by
      intro equal; have same := congrArg (normalize wk).f equal
      rw [(normalize wk).right_inv] at same
      exact notKing same
    have apartWeak : (normalize wk).r (a.target ((normalize wk).f rs) v) ≠ wk := by
      intro equal; have same := congrArg (normalize wk).f equal
      rw [(normalize wk).right_inv] at same
      exact notWeak same
    have legal := KRKOrdinaryEntry.rook_legal material turn sees apartKing apartWeak (KRKWeakBranch.admitted_far material)
    exact entry_certificate material ongoing turn legal (KRKMatingMove.rook_move_model material turn legal rfl).1 live clear

theorem entry_kernel {s : RawTrace.State} {σ : Colour} {sk rs wk ns nr : Square} {m : Move}
    (material : IsKRK (RawTrace.erase s) σ sk rs wk) (turn : (RawTrace.erase s).turn = σ)
    (legal : isLegal (RawTrace.erase s) m = true) (next : IsKRK (play (RawTrace.erase s) m) σ ns nr wk)
    (live : Live ns nr wk) (clear : WeakAfter s m ns nr wk) : MateWithin σ 5 (RawTrace.erase s) := by
  have evaluated := (KRKStrongPrefix.weak_append_iff material turn legal).mpr clear
  have child := KRKStrongPrefix.weak_clear_kernel (s := RawTrace.append s m legal) next
    (by change (play (RawTrace.erase s) m).turn = σ.opp; rw [play_turn,turn]) evaluated live
  exact mateWithin_choose turn ⟨m,legal,rfl⟩ child

theorem clear_kernel {s : RawTrace.State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (RawTrace.erase s) σ sk rs wk) (turn : (RawTrace.erase s).turn = σ)
    (far : 2 ≤ dInf sk wk) (notCheck : ¬RookSees rs wk sk wk)
    (clear : Clear s sk rs wk) : MateWithin σ 5 (RawTrace.erase s) := by
  rcases clear with immediate | ⟨depth,points | rays⟩
  · obtain ⟨r,edge,goal⟩ := (KRKImmediate.immediate_iff material turn far notCheck).mpr immediate
    exact mateWithin_choose turn edge (Or.inl goal)
  · obtain ⟨i,valid,region,mappedDistance,apart,mappedFar,live,clear⟩ := points
    have distance : dInf sk ((normalize wk).r (king ((normalize wk).f wk) i)) = 1 := by
      have preserved := (normalize wk).distance sk ((normalize wk).r (king ((normalize wk).f wk) i))
      rw [(normalize wk).right_inv,mappedDistance] at preserved
      exact preserved.symm
    have notRook : (normalize wk).r (king ((normalize wk).f wk) i) ≠ rs := by
      intro equal; have same := congrArg (normalize wk).f equal
      rw [(normalize wk).right_inv] at same
      exact apart same
    have far : 2 ≤ dInf ((normalize wk).r (king ((normalize wk).f wk) i)) wk := by
      have preserved := (normalize wk).distance ((normalize wk).r (king ((normalize wk).f wk) i)) wk
      rw [(normalize wk).right_inv] at preserved
      rwa [←preserved]
    have legal := KRKOrdinaryEntry.king_legal material turn distance notRook far
    exact entry_kernel material turn legal (canonical_king_material material turn distance notRook far) live clear
  · obtain ⟨i,valid,equal,a,v,mappedSees,notKing,notWeak,region,live,clear⟩ := rays
    have sees : RookSees rs ((normalize wk).r (a.target ((normalize wk).f rs) v)) sk wk := by
      apply ((normalize wk).sees _ _ _ _).mp
      simpa only [(normalize wk).right_inv] using mappedSees
    have apartKing : (normalize wk).r (a.target ((normalize wk).f rs) v) ≠ sk := by
      intro equal; have same := congrArg (normalize wk).f equal
      rw [(normalize wk).right_inv] at same
      exact notKing same
    have apartWeak : (normalize wk).r (a.target ((normalize wk).f rs) v) ≠ wk := by
      intro equal; have same := congrArg (normalize wk).f equal
      rw [(normalize wk).right_inv] at same
      exact notWeak same
    have legal := KRKOrdinaryEntry.rook_legal material turn sees apartKing apartWeak far
    exact entry_kernel material turn legal (KRKMatingMove.rook_move_model material turn legal rfl).1 live clear

theorem necessary {s : RawHistoryLayer.State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (RawHistoryLayer.erase s) σ sk rs wk) (ongoing : RawHistoryLayer.Ongoing s)
    (turn : (RawHistoryLayer.erase s).turn = σ) (high : 94 ≤ RawClock.clock s.val.trace)
    (win : KRKHolding.F σ s) : Clear s.val sk rs wk := by
  obtain ⟨n,cert⟩ := win
  cases n with
  | zero => exact False.elim (opp_ne σ (turn.symm.trans cert.1))
  | succ n =>
    rcases cert with goal | ⟨_, chosen | defended⟩
    · exact False.elim (opp_ne σ (turn.symm.trans goal.1))
    · obtain ⟨_,v,edge,child⟩ := chosen
      have childWin : KRKHolding.F σ v := ⟨n,child⟩
      obtain ⟨_,clock⟩ := KRKHighClock.winning_child_quiet material edge childWin
      obtain ⟨m,legal,rawEq⟩ := edge
      have endpoint : RawHistoryLayer.erase v = play (RawHistoryLayer.erase s) m := congrArg RawTrace.erase rawEq
      obtain ⟨ns,nr,next⟩ := krk_strong_material material turn legal
      have nextV : IsKRK (RawHistoryLayer.erase v) σ ns nr wk := by rwa [endpoint]
      have nextTurn : (RawHistoryLayer.erase v).turn = σ.opp := by rw [endpoint,play_turn,turn]
      by_cases childOngoing : RawHistoryLayer.Ongoing v
      · have deadline := (KRKDeadline.winning_deadline nextV childWin).2
        have budget : KRKDeadline.budget σ v ≤ 5 := by
          have notStrong : (RawHistoryLayer.erase v).turn ≠ σ := fun h => opp_ne σ (h.symm.trans nextTurn)
          simp only [KRKDeadline.budget,notStrong,↓reduceIte]
          omega
        have four := KRKFourPlyEscape.weak_five_to_four nextV nextTurn (mateWithin_mono deadline budget)
        have noMate : ¬MatedK (RawHistoryLayer.erase v) := by
          intro mate
          exact mate.2 (((RawAdjudication.ongoing_iff v.val).mp childOngoing).2.1)
        rw [endpoint] at four noMate
        have geometry := global_shape_necessary next (by rw [play_turn,turn])
          (KRKEdgeDepth.arrival_far ⟨m,legal,rfl⟩ next) noMate four
        have normal := normalize_spec geometry.1
        have evaluated := (KRKGlobalWeakBand.high_clock_force_iff nextV childOngoing nextTurn (by omega)).mp childWin
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


theorem high_clock_force_iff {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ) (high : 94 ≤ RawClock.clock s.val.trace) :
    F σ s ↔ Clear s.val sk rs wk := by
  constructor
  · exact necessary material ongoing turn high
  · intro clear; exact ⟨5,sufficient material ongoing turn clear⟩

theorem high_clock_actual_iff {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ) (high : 94 ≤ RawClock.clock s.val.trace)
 :
    KRKWinning.ActualWin σ s ↔ Clear s.val sk rs wk :=
  (KRKWinning.actual_win_iff_force (Or.inl ⟨sk, rs, wk, material⟩)).trans
    (high_clock_force_iff material ongoing turn high)

theorem high_clock_hold_iff {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ) (high : 94 ≤ RawClock.clock s.val.trace)
 :
    KRKHolding.RuleHold σ.opp s ↔ ¬Clear s.val sk rs wk := by
  have dual := KRKHolding.holding_iff_not_force (σ := σ) (c := σ.opp)
    (s := s) (Or.inl ⟨sk, rs, wk, material⟩)
  simpa only [opp_opp, high_clock_force_iff material ongoing turn high] using dual

theorem high_clock_draw_iff {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ) (high : 94 ≤ RawClock.clock s.val.trace) :
    (KRKHolding.RuleHold σ s ∧ KRKHolding.RuleHold σ.opp s) ↔ ¬Clear s.val sk rs wk := by
  constructor
  · intro holds; exact (high_clock_hold_iff material ongoing turn high).mp holds.2
  · intro outside
    exact ⟨KRKHighClock.strong_hold material, (high_clock_hold_iff material ongoing turn high).mpr outside⟩

theorem high_clock_distance_cases {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ) (high : 94 ≤ RawClock.clock s.val.trace) (win : F σ s) :
    (KRKImmediate.MateNow sk rs wk ∧ W σ 1 s ∧ ¬W σ 0 s) ∨
    (¬KRKImmediate.MateNow sk rs wk ∧ KRKFramedHistory.GlobalClear s.val sk rs wk ∧ W σ 3 s ∧ ¬W σ 2 s) ∨
    (¬KRKImmediate.MateNow sk rs wk ∧ ¬KRKFramedHistory.GlobalClear s.val sk rs wk ∧ W σ 5 s ∧ ¬W σ 4 s) := by
  by_cases immediate : KRKImmediate.MateNow sk rs wk
  · obtain ⟨v,edge,goal⟩ := (KRKImmediate.admitted_immediate_iff material ongoing turn).mpr immediate
    refine Or.inl ⟨immediate,Or.inr ⟨ongoing,Or.inl ⟨turn,v,edge,goal⟩⟩,?_⟩
    intro zero; exact opp_ne σ (turn.symm.trans zero.1)
  by_cases three : KRKFramedHistory.GlobalClear s.val sk rs wk
  · exact Or.inr (Or.inl ⟨immediate,three,(KRKThreePlyExact.global_three_iff material ongoing turn).mpr three,
      KRKThreePlyExact.not_immediate_not_two material ongoing turn immediate⟩)
  · refine Or.inr (Or.inr ⟨immediate,three,sufficient material ongoing turn ((high_clock_force_iff material ongoing turn high).mp win),?_⟩)
    intro four
    exact three ((KRKThreePlyExact.global_three_iff material ongoing turn).mp (KRKDistanceParity.strong_four_three turn four))

end EndgameChess.Rules.KRKFivePlyHistory
