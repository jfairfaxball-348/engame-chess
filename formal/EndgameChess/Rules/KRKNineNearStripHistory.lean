import EndgameChess.Rules.KRKNineNearStrip
import EndgameChess.Rules.KRKEightPlyHistory

namespace EndgameChess.Rules.KRKNineNearStripHistory
open EndgameChess.KK RawHistoryLayer KRKHolding
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

/-- The already evaluated eight-ply original-trace key tests after one
specified move. The quantifier ranges over proofs of that move's legality,
not over candidate moves or future winning predicates. -/
def After (s : RawTrace.State) (m : Move) (sk rs : Square) : Prop :=
  ∀ legal : isLegal (RawTrace.erase s) m = true,
    KRKEightPlyHistory.Clear (RawTrace.append s m legal) sk rs (1,2)

/-- One fixed king destination or five symbolic rank-three rook destinations,
with all original incoming occurrences retained in the prefix tests. -/
def Clear (s : RawTrace.State) (sk rs : Square) : Prop :=
  (rs.2.val = 3 ∧ 3 ≤ rs.1.val ∧ dInf sk (3,1) = 1 ∧
    After s ⟨sk,((3 : Fin 8),1),none⟩ (3,1) rs) ∨
  (sk = ((3 : Fin 8),1) ∧ ∃ x : Fin 8, 3 ≤ x.val ∧
    RookSees rs (x,3) sk (1,2) ∧ After s ⟨rs,(x,3),none⟩ sk (x,3))

theorem entry_certificate {s : State} {σ : Colour} {sk rs ns nr : Square} {m : Move}
    (_material : IsKRK (erase s) σ sk rs (1,2)) (ongoing : Ongoing s) (turn : (erase s).turn = σ)
    (legal : isLegal (erase s) m = true) (next : IsKRK (play (erase s) m) σ ns nr (1,2))
    (region : KRKEightStrip.Region ns nr (1,2)) (history : After s.val m ns nr) : W σ 9 s := by
  let v : State := ⟨RawTrace.append s.val m legal,
    ((StoppedHistory.append_and_reply_lifting s.val).1 m legal).mpr ⟨s.property,ongoing⟩⟩
  have nextV : IsKRK (erase v) σ ns nr (1,2) := next
  have nextTurn : (erase v).turn = σ.opp := by change (play (erase s) m).turn = σ.opp; rw [play_turn,turn]
  have evaluated : KRKEightPlyHistory.Clear v.val ns nr (1,2) := history legal
  have far := KRKEdgeDepth.arrival_far ⟨m,legal,rfl⟩ next
  have board : MateWithin σ 8 (erase v) := (KRKEightNearStrip.kernel_eight_iff nextV nextTurn far).mpr region
  have nonempty : ∃ r,Legal (erase v) r := by
    obtain ⟨t,guard⟩ := (KRKEightStrip.region_clear region).2.1
    exact ⟨_,⟨_,KRKCornerWeakBand.guard_legal nextV nextTurn guard,rfl⟩⟩
  have childOngoing : Ongoing v := (RawAdjudication.ongoing_iff v.val).mpr
    ⟨forceMate_not_dead ⟨8,board⟩,nonempty,by have := evaluated.2.1; omega,by have := evaluated.2.2.1; omega⟩
  have child := KRKEightPlyHistory.sufficient nextV childOngoing nextTurn evaluated
  exact Or.inr ⟨ongoing,Or.inl ⟨turn,v,⟨m,legal,rfl⟩,child⟩⟩

theorem sufficient {s : State} {σ : Colour} {sk rs : Square}
    (material : IsKRK (erase s) σ sk rs (1,2)) (ongoing : Ongoing s) (turn : (erase s).turn = σ)
    (clear : Clear s.val sk rs) : W σ 9 s := by
  rcases clear with ⟨row,width,distance,history⟩ | ⟨king,x,width,sees,history⟩
  · have notRook : ((3 : Fin 8),1) ≠ rs := by simp only [ne_iff_coords,row]; dsimp; omega
    have far : 2 ≤ dInf ((3 : Fin 8),1) (1,2) := by decide
    have legal := KRKOrdinaryEntry.king_legal material turn distance notRook far
    have next := KRKThreePly.canonical_king_material material turn distance notRook far
    exact entry_certificate material ongoing turn legal next ⟨rfl,rfl,rfl,rfl,row,width⟩ history
  · have notKing : (x,(3 : Fin 8)) ≠ sk := by rw [king]; simp [ne_iff_coords] <;> omega
    have notWeak : (x,(3 : Fin 8)) ≠ ((1 : Fin 8),2) := by simp [ne_iff_coords]
    have legal := KRKOrdinaryEntry.rook_legal material turn sees notKing notWeak (KRKWeakBranch.admitted_far material)
    have next := (KRKMatingMove.rook_move_model material turn legal rfl).1
    apply entry_certificate material ongoing turn legal next ?_ history
    rw [king]
    exact ⟨rfl,rfl,rfl,rfl,rfl,width⟩

theorem necessary {s : State} {σ : Colour} {sk rs : Square}
    (material : IsKRK (erase s) σ sk rs (1,2)) (_ongoing : Ongoing s) (turn : (erase s).turn = σ)
    (high : 90 ≤ RawClock.clock s.val.trace) (win : F σ s) : Clear s.val sk rs := by
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
      have nextV : IsKRK (erase v) σ ns nr (1,2) := by rwa [endpoint]
      have nextTurn : (erase v).turn = σ.opp := by rw [endpoint,play_turn,turn]
      have far := KRKEdgeDepth.arrival_far ⟨m,legal,rfl⟩ next
      have notMate : ¬MatedK (erase v) := by
        intro mate
        have zero := KRKEdgeDepth.terminal_depth_zero
          ((KRKMateGeometry.kernel_mate_iff nextV nextTurn far).mp mate)
        change 1 = 0 at zero
        contradiction
      have childOngoing : Ongoing v := by
        apply Classical.byContradiction
        intro stopped
        exact notMate ((KRKHighClock.terminal_force_iff_goal stopped).mp childWin).2
      have deadline := (KRKDeadline.winning_deadline nextV childWin).2
      have budget : KRKDeadline.budget σ v ≤ 9 := by
        have notStrong : (erase v).turn ≠ σ := fun h => opp_ne σ (h.symm.trans nextTurn)
        simp only [KRKDeadline.budget,notStrong,↓reduceIte]
        omega
      have eight := KRKEightGeometry.weak_nine_eight nextV nextTurn (mateWithin_mono deadline budget)
      have evaluated := (KRKEightPlyHistory.high_clock_force_iff nextV childOngoing nextTurn (by omega)).mp childWin
      have rawClear : KRKEightPlyHistory.Clear (RawTrace.append s.val m legal) ns nr (1,2) := by
        rw [←rawEq]; exact evaluated
      rw [endpoint] at eight notMate
      rcases KRKNineEntry.eight_entry_move material turn legal next notMate eight with
        ⟨src,promo,distance,moved,geometry⟩ | ⟨src,promo,sees,moved,geometry⟩
      · have nsEq := KRKCastleFour.king_square next (t := m.dst) (by rw [moved.2.2.2]; exact krkBoard_sk)
        have nrEq := KRKCastleFour.rook_square next (t := rs) (by rw [moved.2.2.2]; exact krkBoard_rs moved.1)
        rw [←nsEq,←nrEq] at rawClear
        obtain ⟨_,_,sx,sy,row,width⟩ := KRKEightNearStrip.necessary moved.1
          (KRKEdgeDepth.arrival_far ⟨m,legal,rfl⟩ moved) geometry
        have target : m.dst = ((3 : Fin 8),1) := Prod.ext (Fin.ext sx) (Fin.ext sy)
        have canonical : m = ⟨sk,((3 : Fin 8),1),none⟩ := by
          cases m; simp only [Move.mk.injEq]; exact ⟨src,target,promo⟩
        rw [target] at distance rawClear
        refine Or.inl ⟨row,width,distance,?_⟩
        intro canonicalLegal
        simpa only [canonical] using rawClear
      · have nsEq := KRKCastleFour.king_square next (t := sk) (by rw [moved.2.2.2]; exact krkBoard_sk)
        have nrEq := KRKCastleFour.rook_square next (t := m.dst) (by rw [moved.2.2.2]; exact krkBoard_rs moved.1)
        rw [←nsEq,←nrEq] at rawClear
        obtain ⟨_,_,sx,sy,row,width⟩ := KRKEightNearStrip.necessary moved.1
          (KRKEdgeDepth.arrival_far ⟨m,legal,rfl⟩ moved) geometry
        have king : sk = ((3 : Fin 8),1) := Prod.ext (Fin.ext sx) (Fin.ext sy)
        have target : m.dst = (m.dst.1,(3 : Fin 8)) := Prod.ext rfl (Fin.ext row)
        have canonical : m = ⟨rs,m.dst,none⟩ := by
          cases m; simp only [Move.mk.injEq]; exact ⟨src,True.intro,promo⟩
        have history : After s.val ⟨rs,m.dst,none⟩ sk m.dst := by
          intro canonicalLegal
          rcases m with ⟨source,destination,promotion⟩
          dsimp only at src promo rawClear canonicalLegal ⊢
          subst source
          subst promotion
          exact rawClear
        refine Or.inr ⟨king,m.dst.1,width,?_,?_⟩
        · rw [←target]; exact sees
        · rw [←target]; exact history
    · exact False.elim (opp_ne σ (turn.symm.trans defended.1))

theorem high_clock_force_iff {s : State} {σ : Colour} {sk rs : Square}
    (material : IsKRK (erase s) σ sk rs (1,2)) (ongoing : Ongoing s) (turn : (erase s).turn = σ)
    (high : 90 ≤ RawClock.clock s.val.trace) : F σ s ↔ Clear s.val sk rs :=
  ⟨necessary material ongoing turn high,fun clear => ⟨9,sufficient material ongoing turn clear⟩⟩

theorem high_clock_actual_iff {s : State} {σ : Colour} {sk rs : Square}
    (material : IsKRK (erase s) σ sk rs (1,2)) (ongoing : Ongoing s) (turn : (erase s).turn = σ)
    (high : 90 ≤ RawClock.clock s.val.trace) : KRKWinning.ActualWin σ s ↔ Clear s.val sk rs :=
  (KRKWinning.actual_win_iff_force (Or.inl ⟨sk,rs,(1,2),material⟩)).trans
    (high_clock_force_iff material ongoing turn high)

theorem high_clock_draw_iff {s : State} {σ : Colour} {sk rs : Square}
    (material : IsKRK (erase s) σ sk rs (1,2)) (ongoing : Ongoing s) (turn : (erase s).turn = σ)
    (high : 90 ≤ RawClock.clock s.val.trace) :
    (RuleHold σ s ∧ RuleHold σ.opp s) ↔ ¬Clear s.val sk rs := by
  have dual := holding_iff_not_force (σ := σ) (c := σ.opp) (s := s) (Or.inl ⟨sk,rs,(1,2),material⟩)
  have weakHold : RuleHold σ.opp s ↔ ¬Clear s.val sk rs := by
    simpa only [opp_opp,high_clock_force_iff material ongoing turn high] using dual
  exact ⟨fun holds => weakHold.mp holds.2,fun outside => ⟨KRKHighClock.strong_hold material,weakHold.mpr outside⟩⟩

theorem exact_nine {s : State} {σ : Colour} {sk rs : Square}
    (material : IsKRK (erase s) σ sk rs (1,2)) (ongoing : Ongoing s) (turn : (erase s).turn = σ)
    (notCheck : ¬RookSees rs (1,2) sk (1,2)) (clear : Clear s.val sk rs) :
    W σ 9 s ∧ ¬W σ 8 s := by
  have nine := sufficient material ongoing turn clear
  have far := KRKWeakBranch.admitted_far material
  have boardNine := raw_ruleMateWithin_project s σ 9 nine
  have condition := KRKNineNearStrip.necessary material turn boardNine
  refine ⟨nine,?_⟩
  intro eight
  exact (KRKNineNearStrip.kernel_exact_nine material turn far notCheck condition).2
    (raw_ruleMateWithin_project s σ 8 eight)

end EndgameChess.Rules.KRKNineNearStripHistory
