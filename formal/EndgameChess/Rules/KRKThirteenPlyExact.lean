import EndgameChess.Rules.KRKThirteenPlyHistory
import EndgameChess.Rules.KRKTwelvePlyExact

namespace EndgameChess.Rules.KRKThirteenPlyExact
open EndgameChess.KK KRKNativeFrame RawHistoryLayer KRKHolding
open KRKThirteenSlots (Kind point frame)
open KRKThirteenPlyHistory (Clear After)
set_option maxHeartbeats 500000

theorem necessary {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (_ongoing : Ongoing s) (turn : (erase s).turn = σ)
    (cert : W σ 13 s) : Clear s.val sk rs wk := by
  rcases cert with goal | ⟨_,chosen | defended⟩
  · exact False.elim (opp_ne σ (turn.symm.trans goal.1))
  · obtain ⟨_,v,edge,child⟩ := chosen
    have childWin : F σ v := ⟨12,child⟩
    obtain ⟨_,clock⟩ := KRKHighClock.winning_child_quiet material edge childWin
    obtain ⟨m,legal,rawEq⟩ := edge
    have endpoint : erase v = play (erase s) m := congrArg RawTrace.erase rawEq
    obtain ⟨ns,nr,next⟩ := krk_strong_material material turn legal
    have nextV : IsKRK (erase v) σ ns nr wk := by rwa [endpoint]
    have nextTurn : (erase v).turn = σ.opp := by rw [endpoint,play_turn,turn]
    by_cases childOngoing : Ongoing v
    · have eight := raw_ruleMateWithin_project v σ 12 child
      have notMate : ¬MatedK (erase v) := fun mate => mate.2 (((RawAdjudication.ongoing_iff v.val).mp childOngoing).2.1)
      have evaluated := (KRKTwelvePlyExact.rule_twelve_iff nextV childOngoing nextTurn).mp child
      have history : After s.val m ns nr wk := by
        intro anyLegal
        rw [←rawEq]
        exact evaluated
      have far := KRKEdgeDepth.arrival_far ⟨m,legal,rfl⟩ next
      have notTerminal : ¬KRKMateGeometry.Terminal ns nr wk := fun h =>
        notMate ((KRKMateGeometry.kernel_mate_iff nextV nextTurn far).mpr h)
      have region := ((KRKTwelveGlobal.kernel_twelve_iff nextV nextTurn far).mp eight).resolve_left notTerminal
      rw [endpoint] at eight notMate
      rcases KRKThirteenEntry.twelve_entry_move material turn legal next notMate eight with
        ⟨src,promo,distance,moved,_⟩ | ⟨src,promo,sees,moved,_⟩
      · have nsEq := KRKCastleFour.king_square next (t := m.dst) (by rw [moved.2.2.2]; exact krkBoard_sk)
        have nrEq := KRKCastleFour.rook_square next (t := rs) (by rw [moved.2.2.2]; exact krkBoard_rs moved.1)
        rw [←nsEq,←nrEq] at region history
        obtain ⟨i,equal⟩ := KRKThirteenSlots.region_point region
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
        obtain ⟨i,equal⟩ := KRKThirteenSlots.region_point region
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


theorem rule_thirteen_iff {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s) (turn : (erase s).turn = σ) :
    W σ 13 s ↔ Clear s.val sk rs wk := ⟨necessary material ongoing turn,KRKThirteenPlyHistory.sufficient material ongoing turn⟩

theorem strong_fourteen_thirteen {s : State} {σ : Colour} (turn : (erase s).turn = σ)
    (cert : W σ 14 s) : W σ 13 s := by
  rcases cert with goal | ⟨ongoing,chosen | defended⟩
  · exact Or.inl goal
  · obtain ⟨_,t,edge,child⟩ := chosen
    have weak : (erase t).turn = σ.opp := by
      have changed : (erase t).turn = (erase s).turn.opp := turn_of_legal (RawTrace.raw_step_sound edge)
      rw [changed,turn]
    exact Or.inr ⟨ongoing,Or.inl ⟨turn,t,edge,KRKElevenPlyExact.weak_thirteen_twelve weak child⟩⟩
  · exact False.elim (opp_ne σ (turn.symm.trans defended.1))

theorem weak_fifteen_fourteen {s : State} {σ : Colour} (turn : (erase s).turn = σ.opp)
    (cert : W σ 15 s) : W σ 14 s := by
  rcases cert with goal | ⟨ongoing,chosen | defended⟩
  · exact Or.inl goal
  · exact False.elim (opp_ne σ (chosen.1.symm.trans turn))
  · refine Or.inr ⟨ongoing,Or.inr ⟨turn,defended.2.1,defended.2.2.1,?_⟩⟩
    intro t edge
    have strong : (erase t).turn = σ := by
      have changed : (erase t).turn = (erase s).turn.opp := turn_of_legal (RawTrace.raw_step_sound edge)
      rw [changed,turn,opp_opp]
    exact strong_fourteen_thirteen strong (defended.2.2.2 t edge)


theorem distance_cases {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s) (turn : (erase s).turn = σ)
    (cert : W σ 13 s) :
    ∃ d : Nat, (d = 1 ∨ d = 3 ∨ d = 5 ∨ d = 7 ∨ d = 9 ∨ d = 11 ∨ d = 13) ∧ W σ d s ∧ ¬W σ (d-1) s := by
  by_cases old : KRKElevenPlyHistory.Clear s.val sk rs wk
  · obtain ⟨d,choices,win,lower⟩ := KRKElevenPlyExact.distance_cases material ongoing turn
      (KRKElevenPlyHistory.sufficient material ongoing turn old)
    exact ⟨d,by omega,win,lower⟩
  · refine ⟨13,by decide,cert,?_⟩
    intro twelve
    exact old ((KRKElevenPlyExact.rule_eleven_iff material ongoing turn).mp
      (KRKElevenPlyExact.strong_twelve_eleven turn twelve))

theorem high_clock_exact_distance {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s) (turn : (erase s).turn = σ)
    (high : 86 ≤ RawClock.clock s.val.trace) (win : F σ s) :
    ∃ d : Nat, (d = 1 ∨ d = 3 ∨ d = 5 ∨ d = 7 ∨ d = 9 ∨ d = 11 ∨ d = 13) ∧ W σ d s ∧ ¬W σ (d-1) s :=
  distance_cases material ongoing turn (KRKThirteenPlyHistory.sufficient material ongoing turn
    ((KRKThirteenPlyHistory.high_clock_force_iff material ongoing turn high).mp win))

end EndgameChess.Rules.KRKThirteenPlyExact
