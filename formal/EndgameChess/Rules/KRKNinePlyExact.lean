import EndgameChess.Rules.KRKNinePlyHistory
import EndgameChess.Rules.KRKEightPlyExact

namespace EndgameChess.Rules.KRKNinePlyExact
open EndgameChess.KK KRKNativeFrame RawHistoryLayer KRKHolding
open KRKNineSlots (Kind point frame)
open KRKNinePlyHistory (Clear After)
set_option maxHeartbeats 500000

theorem necessary {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (_ongoing : Ongoing s) (turn : (erase s).turn = σ)
    (cert : W σ 9 s) : Clear s.val sk rs wk := by
  rcases cert with goal | ⟨_,chosen | defended⟩
  · exact False.elim (opp_ne σ (turn.symm.trans goal.1))
  · obtain ⟨_,v,edge,child⟩ := chosen
    have childWin : F σ v := ⟨8,child⟩
    obtain ⟨_,clock⟩ := KRKHighClock.winning_child_quiet material edge childWin
    obtain ⟨m,legal,rawEq⟩ := edge
    have endpoint : erase v = play (erase s) m := congrArg RawTrace.erase rawEq
    obtain ⟨ns,nr,next⟩ := krk_strong_material material turn legal
    have nextV : IsKRK (erase v) σ ns nr wk := by rwa [endpoint]
    have nextTurn : (erase v).turn = σ.opp := by rw [endpoint,play_turn,turn]
    by_cases childOngoing : Ongoing v
    · have eight := raw_ruleMateWithin_project v σ 8 child
      have notMate : ¬MatedK (erase v) := fun mate => mate.2 (((RawAdjudication.ongoing_iff v.val).mp childOngoing).2.1)
      have evaluated := (KRKEightPlyExact.rule_eight_iff nextV childOngoing nextTurn).mp child
      have history : After s.val m ns nr wk := by
        intro anyLegal
        rw [←rawEq]
        exact evaluated
      have far := KRKEdgeDepth.arrival_far ⟨m,legal,rfl⟩ next
      have notTerminal : ¬KRKMateGeometry.Terminal ns nr wk := fun h =>
        notMate ((KRKMateGeometry.kernel_mate_iff nextV nextTurn far).mpr h)
      have region := ((KRKEightGlobal.kernel_eight_iff nextV nextTurn far).mp eight).resolve_left notTerminal
      rw [endpoint] at eight notMate
      rcases KRKNineEntry.eight_entry_move material turn legal next notMate eight with
        ⟨src,promo,distance,moved,_⟩ | ⟨src,promo,sees,moved,_⟩
      · have nsEq := KRKCastleFour.king_square next (t := m.dst) (by rw [moved.2.2.2]; exact krkBoard_sk)
        have nrEq := KRKCastleFour.rook_square next (t := rs) (by rw [moved.2.2.2]; exact krkBoard_rs moved.1)
        rw [←nsEq,←nrEq] at region history
        obtain ⟨i,equal⟩ := KRKNineSlots.region_point region
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
        obtain ⟨i,equal⟩ := KRKNineSlots.region_point region
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


theorem rule_nine_iff {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s) (turn : (erase s).turn = σ) :
    W σ 9 s ↔ Clear s.val sk rs wk := ⟨necessary material ongoing turn,KRKNinePlyHistory.sufficient material ongoing turn⟩

theorem strong_ten_nine {s : State} {σ : Colour} (turn : (erase s).turn = σ)
    (cert : W σ 10 s) : W σ 9 s := by
  rcases cert with goal | ⟨ongoing,chosen | defended⟩
  · exact Or.inl goal
  · obtain ⟨_,t,edge,child⟩ := chosen
    have weak : (erase t).turn = σ.opp := by
      have changed : (erase t).turn = (erase s).turn.opp := turn_of_legal (RawTrace.raw_step_sound edge)
      rw [changed,turn]
    exact Or.inr ⟨ongoing,Or.inl ⟨turn,t,edge,KRKSevenPlyExact.weak_nine_eight weak child⟩⟩
  · exact False.elim (opp_ne σ (turn.symm.trans defended.1))

theorem weak_eleven_ten {s : State} {σ : Colour} (turn : (erase s).turn = σ.opp)
    (cert : W σ 11 s) : W σ 10 s := by
  rcases cert with goal | ⟨ongoing,chosen | defended⟩
  · exact Or.inl goal
  · exact False.elim (opp_ne σ (chosen.1.symm.trans turn))
  · refine Or.inr ⟨ongoing,Or.inr ⟨turn,defended.2.1,defended.2.2.1,?_⟩⟩
    intro t edge
    have strong : (erase t).turn = σ := by
      have changed : (erase t).turn = (erase s).turn.opp := turn_of_legal (RawTrace.raw_step_sound edge)
      rw [changed,turn,opp_opp]
    exact strong_ten_nine strong (defended.2.2.2 t edge)

theorem high_clock_distance_split {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s) (turn : (erase s).turn = σ)
    (high : 90 ≤ RawClock.clock s.val.trace) (win : F σ s) :
    (KRKSevenPlyHistory.Clear s.val sk rs wk ∧ W σ 7 s) ∨
    (¬KRKSevenPlyHistory.Clear s.val sk rs wk ∧ W σ 9 s ∧ ¬W σ 8 s) := by
  by_cases seven : KRKSevenPlyHistory.Clear s.val sk rs wk
  · exact Or.inl ⟨seven,KRKSevenPlyHistory.sufficient material ongoing turn seven⟩
  · refine Or.inr ⟨seven,KRKNinePlyHistory.sufficient material ongoing turn
      ((KRKNinePlyHistory.high_clock_force_iff material ongoing turn high).mp win),?_⟩
    intro eight
    exact seven ((KRKSevenPlyExact.rule_seven_iff material ongoing turn).mp
      (KRKSevenPlyExact.strong_eight_seven turn eight))

theorem high_clock_exact_distance {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s) (turn : (erase s).turn = σ)
    (high : 90 ≤ RawClock.clock s.val.trace) (win : F σ s) :
    ∃ d : Nat, (d = 1 ∨ d = 3 ∨ d = 5 ∨ d = 7 ∨ d = 9) ∧ W σ d s ∧ ¬W σ (d-1) s := by
  rcases high_clock_distance_split material ongoing turn high win with ⟨_,seven⟩ | ⟨_,nine,notEight⟩
  · rcases KRKSevenPlyExact.distance_cases material ongoing turn seven with
      ⟨_,one,notZero⟩ | ⟨_,_,three,notTwo⟩ | ⟨_,_,five,notFour⟩ | ⟨_,seven,notSix⟩
    · exact ⟨1,by decide,one,notZero⟩
    · exact ⟨3,by decide,three,notTwo⟩
    · exact ⟨5,by decide,five,notFour⟩
    · exact ⟨7,by decide,seven,notSix⟩
  · exact ⟨9,by decide,nine,notEight⟩

end EndgameChess.Rules.KRKNinePlyExact
