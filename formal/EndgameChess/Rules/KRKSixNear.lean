import EndgameChess.Rules.KRKFiveCornerEntries

namespace EndgameChess.Rules.KRKSixNear
open EndgameChess.KK KRKFourPlyEscape KRKMateGeometry
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

private theorem val0 : ((0 : Fin 8).val) = 0 := rfl
private theorem val1 : ((1 : Fin 8).val) = 1 := rfl
private theorem val2 : ((2 : Fin 8).val) = 2 := rfl
private theorem val3 : ((3 : Fin 8).val) = 3 := rfl
private theorem val4 : ((4 : Fin 8).val) = 4 := rfl
private theorem min37 : min (3 : Nat) 7 = 3 := rfl
private theorem max12 : max (1 : Nat) 2 = 2 := rfl
private theorem max21 : max (2 : Nat) 1 = 2 := rfl
private theorem max13 : max (1 : Nat) 3 = 3 := rfl
private theorem max31 : max (3 : Nat) 1 = 3 := rfl
private theorem max23 : max (2 : Nat) 3 = 3 := rfl
private theorem max32 : max (3 : Nat) 2 = 3 := rfl

def Extra (sk rs : Square) : Prop :=
  (sk.1.val = 2 ∧ sk.2.val = 2) ∨
  (sk.1.val = 3 ∧ sk.2.val = 0 ∧ ((rs.2.val = 1 ∧ 3 ≤ rs.1.val) ∨ (rs.1.val = 1 ∧ (rs.2.val = 2 ∨ rs.2.val = 3)))) ∨
  (sk.1.val = 3 ∧ sk.2.val = 1 ∧ ((rs.1.val = 1 ∧ 2 ≤ rs.2.val) ∨ (rs.1.val = 2 ∧ rs.2.val = 1))) ∨
  (sk.1.val = 3 ∧ sk.2.val = 2 ∧
    ((rs.1.val = 1 ∧ 2 ≤ rs.2.val) ∨ (rs.1.val = 2 ∧ rs.2.val = 1)))

def Region (sk rs : Square) : Prop := KRKFourPlyNearCorner.NearFour sk rs ∨ Extra sk rs

theorem necessary {sk rs wk : Square} (distinct : sk ≠ rs)
    (file : wk.1.val = 1) (rank : wk.2.val = 0)
    (far : 2 ≤ dInf sk wk) (safe : SafeRook sk rs wk)
    (every : ∀ u, StepM ⟨sk,rs,wk,false⟩ ⟨sk,rs,u,true⟩ → KRKFiveGeometry.Clear sk rs u) :
    Terminal sk rs wk ∨ Region sk rs := by
  have a := covered_box (KRKCastleSix.interior_covered (t := ((1 : Fin 8),1)) safe
    (by simp [dInf,absDiff,file,rank]) (by decide) every)
  have b := covered_box (KRKCastleSix.interior_covered (t := ((2 : Fin 8),1)) safe
    (by simp [dInf,absDiff,file,rank]) (by decide) every)
  have r := KRKSixMiddle.covered_or_five (t := ((2 : Fin 8),0)) distinct safe
    (by simp [dInf,absDiff,file,rank]) rfl (by decide) (by decide) every
  have mappedSafe : SafeRook (symSwap.f sk) (symSwap.f rs) (symSwap.f wk) := by
    simpa only [SafeRook,symSwap.dInf_eq] using safe
  have c := KRKSixCorner.blocked_or_near (t := ((1 : Fin 8),0)) (symSwap.ne_iff.mpr distinct) mappedSafe
    (by simp [symSwap,dInf,absDiff,file,rank]) rfl rfl (KRKSixInterior.every_map symSwap distinct every)
  have reduced : Terminal sk rs wk ∨ Region sk rs ∨
      (sk.1.val = 3 ∧ sk.2.val = 1 ∧ rs.2.val = 1 ∧ 4 ≤ rs.1.val) ∨
      (sk.1.val = 3 ∧ sk.2.val = 0 ∧ rs.1.val = 2 ∧ rs.2.val = 1) := by
    clear every mappedSafe
    have files : sk.1.val = 0 ∨ sk.1.val = 1 ∨ sk.1.val = 2 ∨ sk.1.val = 3 ∨ 4 ≤ sk.1.val := by omega
    have ranks : sk.2.val = 0 ∨ sk.2.val = 1 ∨ sk.2.val = 2 ∨ sk.2.val = 3 ∨ 4 ≤ sk.2.val := by omega
    rcases files with sx | sx | sx | sx | sx <;>
      rcases ranks with sy | sy | sy | sy | sy <;>
      (try simp [dInf,absDiff,file,rank,sx,sy] at far) <;>
      simp only [KRKFiveMiddle.BottomFive,KRKFiveMiddle.Five,KRKFiveMiddle.KingEntries,KRKFiveMiddle.RookEntries,
        KRKFiveNear.Five,KRKFiveNear.KingEntries,KRKFiveNear.RookEntries,KRKCanonicalSlots.left,KRKCanonicalSlots.right,
        symSwap,SafeRook,dInf,absDiff,RookSees,RookLine,OnSeg,square_eq_iff,Fin.ext_iff,ne_iff_coords,file,rank,sx,
        sy,val0,val1,val2,val3,val4] at a b c r far safe distinct <;>
      (try dsimp only at a b c r) <;>
      (try simp only [val0,val1,val2,val3,val4] at a b c r) <;>
      (try have row : rs.2.val = 1 := by clear c r safe distinct far; omega) <;>
      (try simp only [row] at c r safe) <;>
      dsimp [Terminal,Horizontal,Region,Extra,KRKFourPlyNearCorner.NearFour,absDiff] <;>
      simp only [file,rank,sx,sy] <;>
      (try simp only [val0,val1,val2,val3,val4,Nat.reduceAdd,Nat.reduceSub,Nat.reduceEqDiff,Nat.reduceLeDiff,Nat.reduceLT,
        min37,max12,max21,max13,max31,max23,max32,Nat.max_self,Nat.zero_max,Nat.max_zero,Nat.zero_sub,Nat.sub_zero,Nat.add_zero,Nat.zero_add,true_implies,false_implies,ite_true,ite_false,true_and,and_true,false_and,and_false,true_or,or_true,false_or,or_false,not_true_eq_false,not_false_eq_true] at *) <;> first | (exfalso; clear c; omega) | (clear c; omega) | omega
  rcases reduced with terminal | region | ⟨sx,sy,ry,rx⟩ | ⟨sx,sy,rx,ry⟩
  · exact Or.inl terminal
  · exact Or.inr region
  · have step : StepM ⟨sk,rs,wk,false⟩ ⟨sk,rs,((1 : Fin 8),1),true⟩ := by
      refine StepM.lone ?_ ?_ ?_ ?_ <;>
        simp only [dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,file,rank,sx,sy,ry,val0,val1,val3] <;>
        (try simp) <;> omega
    have zero := KRKCastleSix.five_depth_zero (every _ step)
    simp [KRKEdgeDepth.depth] at zero
  · have step : StepM ⟨sk,rs,wk,false⟩ ⟨sk,rs,((0 : Fin 8),0),true⟩ := by
      refine StepM.lone ?_ ?_ ?_ ?_ <;>
        simp only [dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,file,rank,sx,sy,rx,ry,val0,val1,val2,val3] <;>
        (try simp) <;> omega
    have clear := every _ step
    have king : sk = ((3 : Fin 8),0) := Prod.ext (Fin.ext sx) (Fin.ext sy)
    have rook : rs = ((2 : Fin 8),1) := Prod.ext (Fin.ext rx) (Fin.ext ry)
    rw [king,rook] at clear
    exact False.elim (KRKFiveCornerEntries.no_capture_square_entry clear)
theorem extra_replies {sk rs wk t : Square} (distinct : sk ≠ rs)
    (file : wk.1.val = 1) (rank : wk.2.val = 0) (extra : Extra sk rs)
    (step : StepM ⟨sk,rs,wk,false⟩ ⟨sk,rs,t,true⟩) : KRKFiveGeometry.Clear sk rs t := by
  have guard := KRKCornerWeakBand.step_guard step
  have choices : (t.1.val = 0 ∧ t.2.val = 0) ∨ (t.1.val = 0 ∧ t.2.val = 1) ∨
      (t.1.val = 2 ∧ t.2.val = 0) := by
    dsimp [Extra] at extra
    simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,file,rank] at guard
    omega
  rcases choices with ⟨tx,ty⟩ | ⟨tx,ty⟩ | ⟨tx,ty⟩
  · have equal : t = ((0 : Fin 8),0) := Prod.ext (Fin.ext tx) (Fin.ext ty)
    rw [equal]
    rcases extra with ⟨sx,sy⟩ | ⟨sx,sy,h⟩ | ⟨sx,sy,h⟩ | ⟨sx,sy,h⟩
    · have king : sk = ((2 : Fin 8),2) := Prod.ext (Fin.ext sx) (Fin.ext sy)
      rw [king]
      apply KRKFiveCornerEntries.corner22_five
      · simpa only [king] using distinct
      · simpa only [equal] using guard.2.1.symm
      · simpa only [equal,king] using guard.2.2.2
    · rcases h with ⟨ry,rx⟩ | ⟨rx,ry⟩
      · exact KRKFiveCornerEntries.low_right_five sx (by omega) ry rx
      · exact KRKFiveCornerEntries.side_right_five sx (by omega) rx (by omega)
    · rcases h with ⟨rx,ry⟩ | ⟨rx,ry⟩
      · exact KRKFiveCornerEntries.side_right_five sx (by omega) rx ry
      · apply KRKFiveCornerEntries.corner22_king_five
        · simp only [dInf,absDiff,sx,sy,val2]; omega
        · change (3 ≤ rs.1.val ∧ 3 ≤ rs.2.val) ∨ (rs.1.val = 0 ∧ 2 ≤ rs.2.val) ∨
            (rs.2.val = 0 ∧ 2 ≤ rs.1.val) ∨ (rs.1.val = 1 ∧ rs.2.val = 2) ∨
            (rs.1.val = 2 ∧ rs.2.val = 1)
          omega
    · rcases h with ⟨rx,ry⟩ | ⟨rx,ry⟩
      · exact KRKFiveCornerEntries.side_right_five sx (by omega) rx ry
      · apply KRKFiveCornerEntries.corner22_king_five
        · simp only [dInf,absDiff,sx,sy,val2]; omega
        · change (3 ≤ rs.1.val ∧ 3 ≤ rs.2.val) ∨ (rs.1.val = 0 ∧ 2 ≤ rs.2.val) ∨
            (rs.2.val = 0 ∧ 2 ≤ rs.1.val) ∨ (rs.1.val = 1 ∧ rs.2.val = 2) ∨
            (rs.1.val = 2 ∧ rs.2.val = 1)
          omega
  · have notKing : sk ≠ t := ne_of_dInf_pos (by have := guard.2.2.1; omega)
    apply (KRKFiveGeometry.map_iff symSwap distinct notKing guard.2.1.symm guard.2.2.1 guard.2.2.2).mp
    have notCheck : ¬RookSees (symSwap.f rs) (symSwap.f t) (symSwap.f sk) (symSwap.f t) :=
      fun h => guard.2.2.2 ((symSwap.sees_iff _ _ _ _).mp h)
    apply (KRKFiveNear.clear_iff (sk := symSwap.f sk) (rs := symSwap.f rs) (wk := symSwap.f t)
      tx ty (symSwap.ne_iff.mpr distinct) (symSwap.ne_iff.mpr guard.2.1.symm) notCheck).mpr
    have notSeen := guard.2.2.2
    rcases extra with ⟨sx,sy⟩ | ⟨sx,sy,h⟩ | ⟨sx,sy,h⟩ | ⟨sx,sy,h⟩ <;>
      simp only [KRKFiveNear.Five,KRKFiveNear.KingEntries,KRKFiveNear.RookEntries,
        symSwap,square_eq_iff,dInf,absDiff,sx,sy] <;>
      simp only [RookSees,RookLine,OnSeg,tx,ty,sx,sy] at notSeen <;>
      (try dsimp only at *) <;> (try simp_all [val0,val1,val2,val3,val4]) <;> omega
  · apply (KRKFiveMiddle.clear_iff ty (by omega) (by omega) distinct guard.2.1.symm guard.2.2.2).mpr
    have notSeen := guard.2.2.2
    have far := guard.2.2.1
    rcases extra with ⟨sx,sy⟩ | ⟨sx,sy,h⟩ | ⟨sx,sy,h⟩ | ⟨sx,sy,h⟩ <;>
      simp only [KRKFiveMiddle.Five,KRKFiveMiddle.KingEntries,KRKFiveMiddle.RookEntries,
        KRKCanonicalSlots.left,KRKCanonicalSlots.right,square_eq_iff,dInf,absDiff,sx,sy,tx] <;>
      simp only [RookSees,RookLine,OnSeg,tx,ty,sx,sy] at notSeen <;>
      simp only [dInf,absDiff,tx,ty,sx,sy] at far <;>
      (try dsimp only at *) <;> (try simp_all [val0,val1,val2,val3,val4]) <;> omega

theorem kernel_six_iff {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp) (far : 2 ≤ dInf sk wk)
    (file : wk.1.val = 1) (rank : wk.2.val = 0) : MateWithin σ 6 q ↔
      Terminal sk rs wk ∨ (Region sk rs ∧ SafeRook sk rs wk ∧ ∃ t, KRKCornerWeakBand.Guard sk rs wk t) := by
  by_cases mate : MatedK q
  · have terminal := (KRKMateGeometry.kernel_mate_iff material turn far).mp mate
    exact ⟨fun _ => Or.inl terminal,fun _ => Or.inl ⟨turn,mate⟩⟩
  constructor
  · intro six
    obtain ⟨safe,live,every⟩ := (KRKSixGeometry.kernel_six_iff material turn mate).mp six
    have result := necessary material.1 file rank far safe
      (fun t step => every t (KRKCornerWeakBand.step_guard step))
    exact result.elim Or.inl (fun region => Or.inr ⟨region,safe,live⟩)
  · rintro (terminal | ⟨region,safe,⟨t,guard⟩⟩)
    · exact False.elim (mate ((KRKMateGeometry.kernel_mate_iff material turn far).mpr terminal))
    rcases region with old | extra
    · have legal := KRKCornerWeakBand.guard_legal material turn guard
      have four := (KRKFourPlyNearCorner.weak_four_iff material turn far file rank).mpr
        (Or.inr ⟨old,⟨_,⟨_,legal,rfl⟩⟩⟩)
      exact mateWithin_mono four (by decide)
    · apply (KRKSixGeometry.kernel_six_iff material turn mate).mpr
      exact ⟨safe,⟨t,guard⟩,fun u h => extra_replies material.1 file rank extra
        (StepM.lone h.1 h.2.1 h.2.2.1 h.2.2.2)⟩

def NewSix (sk rs : Square) : Prop :=
  (sk.1.val = 2 ∧ sk.2.val = 2 ∧
    (rs.1.val = 1 ∨ rs.1.val = 2 ∨ (rs.1.val = 3 ∧ rs.2.val = 1))) ∨
  (sk.1.val = 3 ∧ sk.2.val = 0 ∧ ((rs.2.val = 1 ∧ 3 ≤ rs.1.val) ∨ (rs.1.val = 1 ∧ (rs.2.val = 2 ∨ rs.2.val = 3)))) ∨
  (sk.1.val = 3 ∧ sk.2.val = 1 ∧ ((rs.1.val = 1 ∧ 2 ≤ rs.2.val) ∨ (rs.1.val = 2 ∧ rs.2.val = 1))) ∨
  (sk.1.val = 3 ∧ sk.2.val = 2 ∧
    ((rs.1.val = 1 ∧ 2 ≤ rs.2.val) ∨ (rs.1.val = 2 ∧ rs.2.val = 1)))

theorem kernel_exact_six_iff {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp) (far : 2 ≤ dInf sk wk)
    (file : wk.1.val = 1) (rank : wk.2.val = 0) :
    (MateWithin σ 6 q ∧ ¬MateWithin σ 5 q) ↔
      NewSix sk rs ∧ SafeRook sk rs wk ∧ ∃ t, KRKCornerWeakBand.Guard sk rs wk t := by
  have four := KRKFourPlyNearCorner.weak_four_iff material turn far file rank
  constructor
  · rintro ⟨six,notFive⟩
    have notFour : ¬MateWithin σ 4 q := fun win => notFive (mateWithin_mono win (by decide))
    have notMate : ¬MatedK q := fun mate => notFour (four.mpr (Or.inl mate))
    have notTerminal : ¬Terminal sk rs wk := fun terminal =>
      notMate ((KRKMateGeometry.kernel_mate_iff material turn far).mpr terminal)
    obtain ⟨region,safe,live⟩ := ((kernel_six_iff material turn far file rank).mp six).resolve_left notTerminal
    obtain ⟨t,guard⟩ := live
    have legal := KRKCornerWeakBand.guard_legal material turn guard
    have notOld : ¬KRKFourPlyNearCorner.NearFour sk rs := fun old =>
      notFour (four.mpr (Or.inr ⟨old,⟨_,⟨_,legal,rfl⟩⟩⟩))
    have extra : Extra sk rs := region.resolve_left notOld
    refine ⟨?_,safe,⟨t,guard⟩⟩
    simp only [KRKFourPlyNearCorner.NearFour] at notOld
    simp only [SafeRook,dInf,absDiff,file,rank] at safe
    rcases extra with ⟨sx,sy⟩ | h | h | h
    · apply Or.inl
      refine ⟨sx,sy,?_⟩
      simp only [sx,sy] at notOld safe
      simp at notOld
      simp only [Fin.ext_iff,val0] at notOld
      omega
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  · rintro ⟨new,safe,live⟩
    have extra : Extra sk rs := by
      rcases new with ⟨sx,sy,_⟩ | h | h | h
      · exact Or.inl ⟨sx,sy⟩
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
    have notOld : ¬KRKFourPlyNearCorner.NearFour sk rs := by
      dsimp [NewSix] at new
      dsimp [KRKFourPlyNearCorner.NearFour]
      omega
    have notTerminal : ¬Terminal sk rs wk := by
      dsimp [Extra] at extra
      simp only [Terminal,Horizontal,file,rank]
      omega
    refine ⟨(kernel_six_iff material turn far file rank).mpr (Or.inr ⟨Or.inr extra,safe,live⟩),?_⟩
    intro five
    rcases four.mp (KRKFourPlyEscape.weak_five_to_four material turn five) with mate | ⟨old,_⟩
    · exact notTerminal ((KRKMateGeometry.kernel_mate_iff material turn far).mp mate)
    · exact notOld old

end EndgameChess.Rules.KRKSixNear














