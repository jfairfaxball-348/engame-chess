import EndgameChess.Rules.KRKElevenGeometry
import EndgameChess.Rules.KRKTenPlyHistory

namespace EndgameChess.Rules.KRKElevenPlyHistory
open EndgameChess.KK KRKNativeFrame RawHistoryLayer KRKHolding
open KRKElevenSlots (Kind point frame)
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

def After (s : RawTrace.State) (m : Move) (sk rs wk : Square) : Prop :=
  ∀ legal : isLegal (RawTrace.erase s) m = true,
    KRKTenPlyHistory.Clear (RawTrace.append s m legal) sk rs wk

def KingPoints (s : RawTrace.State) (sk rs wk : Square) : Prop :=
  let g := frame wk
  ∃ i : Kind, dInf (g.f sk) (point i) = 1 ∧ point i ≠ g.f rs ∧ 2 ≤ dInf (point i) (g.f wk) ∧
    KRKTenGlobal.Region (g.r (point i)) rs wk ∧
      After s ⟨sk,g.r (point i),none⟩ (g.r (point i)) rs wk

def RookRays (s : RawTrace.State) (sk rs wk : Square) : Prop :=
  let g := frame wk
  ∃ i : Kind, g.f sk = point i ∧ ∃ a : KRKCornerSlotBarriers.Axis, ∃ v : Fin 8,
    RookSees (g.f rs) (a.target (g.f rs) v) (g.f sk) (g.f wk) ∧
      a.target (g.f rs) v ≠ g.f sk ∧ a.target (g.f rs) v ≠ g.f wk ∧
      KRKTenGlobal.Region sk (g.r (a.target (g.f rs) v)) wk ∧
        After s ⟨rs,g.r (a.target (g.f rs) v),none⟩ sk (g.r (a.target (g.f rs) v)) wk

/-- Fixed point/ray geometry plus explicit original-trace clock/key tests.
`After` quantifies over proofs of one specified move, never over moves. -/
def Clear (s : RawTrace.State) (sk rs wk : Square) : Prop :=
  KRKImmediate.MateNow sk rs wk ∨ KingPoints s sk rs wk ∨ RookRays s sk rs wk

theorem clear_geometry {s : RawTrace.State} {sk rs wk : Square} (clear : Clear s sk rs wk) :
    KRKElevenGeometry.Clear sk rs wk := by
  rcases clear with immediate | ⟨i,distance,apart,far,region,_⟩ | ⟨i,equal,a,v,sees,notKing,notWeak,region,_⟩
  · exact Or.inl immediate
  · exact Or.inr (Or.inl ⟨i,distance,apart,far,region⟩)
  · exact Or.inr (Or.inr ⟨i,equal,a,v,sees,notKing,notWeak,region⟩)

theorem clear_kernel {s : RawTrace.State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (RawTrace.erase s) σ sk rs wk) (turn : (RawTrace.erase s).turn = σ)
    (far : 2 ≤ dInf sk wk) (notCheck : ¬RookSees rs wk sk wk)
    (clear : Clear s sk rs wk) : MateWithin σ 11 (RawTrace.erase s) :=
  KRKElevenGeometry.sufficient material turn far notCheck (clear_geometry clear)

theorem entry_certificate {s : State} {σ : Colour} {sk rs wk ns nr : Square} {m : Move}
    (_material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s) (turn : (erase s).turn = σ)
    (legal : isLegal (erase s) m = true) (next : IsKRK (play (erase s) m) σ ns nr wk)
    (region : KRKTenGlobal.Region ns nr wk) (history : After s.val m ns nr wk) : W σ 11 s := by
  let v : State := ⟨RawTrace.append s.val m legal,
    ((StoppedHistory.append_and_reply_lifting s.val).1 m legal).mpr ⟨s.property,ongoing⟩⟩
  have nextV : IsKRK (erase v) σ ns nr wk := next
  have nextTurn : (erase v).turn = σ.opp := by change (play (erase s) m).turn = σ.opp; rw [play_turn,turn]
  have evaluated : KRKTenPlyHistory.Clear v.val ns nr wk := history legal
  have far := KRKEdgeDepth.arrival_far ⟨m,legal,rfl⟩ next
  have board : MateWithin σ 10 (erase v) := (KRKTenGlobal.kernel_ten_iff nextV nextTurn far).mpr (Or.inr region)
  have nonempty := KRKTenGlobal.region_live nextV nextTurn far region
  have childOngoing : Ongoing v := (RawAdjudication.ongoing_iff v.val).mpr
    ⟨forceMate_not_dead ⟨10,board⟩,nonempty,by have := evaluated.2.1; omega,by have := evaluated.2.2.1; omega⟩
  exact Or.inr ⟨ongoing,Or.inl ⟨turn,v,⟨m,legal,rfl⟩,
    KRKTenPlyHistory.sufficient nextV childOngoing nextTurn evaluated⟩⟩

theorem sufficient {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s) (turn : (erase s).turn = σ)
    (clear : Clear s.val sk rs wk) : W σ 11 s := by
  rcases clear with immediate | points | rays
  · obtain ⟨v,edge,goal⟩ := (KRKImmediate.admitted_immediate_iff material ongoing turn).mpr immediate
    exact Or.inr ⟨ongoing,Or.inl ⟨turn,v,edge,Or.inl goal⟩⟩
  · obtain ⟨i,mappedDistance,apart,mappedFar,region,history⟩ := points
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
    exact entry_certificate material ongoing turn legal
      (KRKThreePly.canonical_king_material material turn distance notRook far) region history
  · obtain ⟨i,equal,a,v,mappedSees,notKing,notWeak,region,history⟩ := rays
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
    exact entry_certificate material ongoing turn legal (KRKMatingMove.rook_move_model material turn legal rfl).1 region history

theorem necessary {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (_ongoing : Ongoing s) (turn : (erase s).turn = σ)
    (high : 88 ≤ RawClock.clock s.val.trace) (win : F σ s) : Clear s.val sk rs wk := by
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
        have budget : KRKDeadline.budget σ v ≤ 11 := by
          have notStrong : (erase v).turn ≠ σ := fun h => opp_ne σ (h.symm.trans nextTurn)
          simp only [KRKDeadline.budget,notStrong,↓reduceIte]
          omega
        have eight := KRKTenGeometry.weak_eleven_ten nextV nextTurn (mateWithin_mono deadline budget)
        have notMate : ¬MatedK (erase v) := fun mate => mate.2 (((RawAdjudication.ongoing_iff v.val).mp childOngoing).2.1)
        have evaluated := (KRKTenPlyHistory.high_clock_force_iff nextV childOngoing nextTurn (by omega)).mp childWin
        have history : After s.val m ns nr wk := by
          intro anyLegal
          rw [←rawEq]
          exact evaluated
        have far := KRKEdgeDepth.arrival_far ⟨m,legal,rfl⟩ next
        have notTerminal : ¬KRKMateGeometry.Terminal ns nr wk := fun h =>
          notMate ((KRKMateGeometry.kernel_mate_iff nextV nextTurn far).mpr h)
        have region := ((KRKTenGlobal.kernel_ten_iff nextV nextTurn far).mp eight).resolve_left notTerminal
        rw [endpoint] at eight notMate
        rcases KRKElevenEntry.ten_entry_move material turn legal next notMate eight with
          ⟨src,promo,distance,moved,_⟩ | ⟨src,promo,sees,moved,_⟩
        · have nsEq := KRKCastleFour.king_square next (t := m.dst) (by rw [moved.2.2.2]; exact krkBoard_sk)
          have nrEq := KRKCastleFour.rook_square next (t := rs) (by rw [moved.2.2.2]; exact krkBoard_rs moved.1)
          rw [←nsEq,←nrEq] at region history
          obtain ⟨i,equal⟩ := KRKElevenSlots.region_point region
          have actual := (frame wk).preimage_eq equal
          have mappedDistance := (frame wk).distance sk m.dst
          rw [equal,distance] at mappedDistance
          have apart : point i ≠ (frame wk).f rs := by rw [←equal]; exact (frame wk).ne_iff.mpr moved.1
          have mappedFar : 2 ≤ dInf (point i) ((frame wk).f wk) := by
            rw [←equal,(frame wk).distance]
            exact KRKEdgeDepth.arrival_far ⟨m,legal,rfl⟩ moved
          have canonical : m = ⟨sk,m.dst,none⟩ := by
            cases m; simp only [Move.mk.injEq]; exact ⟨src,True.intro,promo⟩
          rw [canonical,actual] at history
          rw [actual] at region
          exact Or.inr (Or.inl ⟨i,mappedDistance,apart,mappedFar,region,history⟩)
        · have nsEq := KRKCastleFour.king_square next (t := sk) (by rw [moved.2.2.2]; exact krkBoard_sk)
          have nrEq := KRKCastleFour.rook_square next (t := m.dst) (by rw [moved.2.2.2]; exact krkBoard_rs moved.1)
          rw [←nsEq,←nrEq] at region history
          obtain ⟨i,equal⟩ := KRKElevenSlots.region_point region
          have mappedSees := ((frame wk).sees rs m.dst sk wk).mpr sees
          obtain ⟨a,v,target⟩ := KRKCornerSlotBarriers.line_target mappedSees.1
          have actual := (frame wk).preimage_eq target
          have apartKing : a.target ((frame wk).f rs) v ≠ (frame wk).f sk := by rw [←target]; exact (frame wk).ne_iff.mpr moved.1.symm
          have apartWeak : a.target ((frame wk).f rs) v ≠ (frame wk).f wk := by rw [←target]; exact (frame wk).ne_iff.mpr moved.2.2.1
          rw [target] at mappedSees
          have canonical : m = ⟨rs,m.dst,none⟩ := by
            cases m; simp only [Move.mk.injEq]; exact ⟨src,True.intro,promo⟩
          rw [canonical,actual] at history
          rw [actual] at region
          exact Or.inr (Or.inr ⟨i,equal,a,v,mappedSees,apartKing,apartWeak,region,history⟩)
      · have goal := (KRKHighClock.terminal_force_iff_goal childOngoing).mp childWin
        exact Or.inl ((KRKImmediate.admitted_immediate_iff material _ongoing turn).mp ⟨v,⟨m,legal,rawEq⟩,goal⟩)
    · exact False.elim (opp_ne σ (turn.symm.trans defended.1))

theorem high_clock_force_iff {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s) (turn : (erase s).turn = σ)
    (high : 88 ≤ RawClock.clock s.val.trace) : F σ s ↔ Clear s.val sk rs wk :=
  ⟨necessary material ongoing turn high,fun clear => ⟨11,sufficient material ongoing turn clear⟩⟩

theorem high_clock_actual_iff {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s) (turn : (erase s).turn = σ)
    (high : 88 ≤ RawClock.clock s.val.trace) : KRKWinning.ActualWin σ s ↔ Clear s.val sk rs wk :=
  (KRKWinning.actual_win_iff_force (Or.inl ⟨sk,rs,wk,material⟩)).trans
    (high_clock_force_iff material ongoing turn high)

theorem high_clock_draw_iff {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s) (turn : (erase s).turn = σ)
    (high : 88 ≤ RawClock.clock s.val.trace) :
    (RuleHold σ s ∧ RuleHold σ.opp s) ↔ ¬Clear s.val sk rs wk := by
  have dual := holding_iff_not_force (σ := σ) (c := σ.opp) (s := s) (Or.inl ⟨sk,rs,wk,material⟩)
  have weakHold : RuleHold σ.opp s ↔ ¬Clear s.val sk rs wk := by
    simpa only [opp_opp,high_clock_force_iff material ongoing turn high] using dual
  exact ⟨fun holds => weakHold.mp holds.2,fun outside => ⟨KRKHighClock.strong_hold material,weakHold.mpr outside⟩⟩

end EndgameChess.Rules.KRKElevenPlyHistory
