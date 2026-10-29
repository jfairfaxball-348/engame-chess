import EndgameChess.Rules.KRKSixCorner
import EndgameChess.Rules.KRKSixMiddle

namespace EndgameChess.Rules.KRKSixSecond
open EndgameChess.KK KRKFourPlyEscape KRKMateGeometry
set_option maxHeartbeats 200000
set_option linter.unusedSimpArgs false

private theorem val0 : ((0 : Fin 8).val) = 0 := rfl
private theorem val1 : ((1 : Fin 8).val) = 1 := rfl
private theorem val2 : ((2 : Fin 8).val) = 2 := rfl
private theorem val3 : ((3 : Fin 8).val) = 3 := rfl
private theorem val4 : ((4 : Fin 8).val) = 4 := rfl

/-- Canonical second-edge six-ply region, with weak king at (2,0). -/
def Region (sk rs : Square) : Prop := sk.2.val = 2 ∧
  ((sk.1.val = 1 ∧ rs.1.val = 3 ∧ 2 ≤ rs.2.val) ∨
   (sk.1.val = 2 ∧ (3 ≤ rs.2.val ∨
     (rs.2.val = 2 ∧ 3 ≤ rs.1.val) ∨ (rs.2.val = 1 ∧ (rs.1.val = 3 ∨ rs.1.val = 4)))) ∨
   (sk.1.val = 3 ∧ ((rs.1.val = 1 ∧ 2 ≤ rs.2.val) ∨
     (rs.2.val = 1 ∧ 4 ≤ rs.1.val))))

theorem necessary {sk rs wk : Square} (distinct : sk ≠ rs)
    (file : wk.1.val = 2) (rank : wk.2.val = 0)
    (far : 2 ≤ dInf sk wk) (safe : SafeRook sk rs wk)
    (every : ∀ u, StepM ⟨sk,rs,wk,false⟩ ⟨sk,rs,u,true⟩ → KRKFiveGeometry.Clear sk rs u) :
    Terminal sk rs wk ∨ Region sk rs := by
  have a := covered_box (KRKCastleSix.interior_covered (t := ((1 : Fin 8),1)) safe
    (by simp [dInf,absDiff,file,rank,val0,val1,val2,val3]) (by decide) every)
  have b := covered_box (KRKCastleSix.interior_covered (t := ((2 : Fin 8),1)) safe
    (by simp [dInf,absDiff,file,rank,val0,val1,val2,val3]) (by decide) every)
  have c := covered_box (KRKCastleSix.interior_covered (t := ((3 : Fin 8),1)) safe
    (by simp [dInf,absDiff,file,rank,val0,val1,val2,val3]) (by decide) every)
  have l := KRKSixCorner.blocked_or_near (t := ((1 : Fin 8),0)) distinct safe
    (by simp [dInf,absDiff,file,rank,val0,val1,val2,val3]) rfl rfl every
  have r := KRKSixMiddle.covered_or_five (t := ((3 : Fin 8),0)) distinct safe
    (by simp [dInf,absDiff,file,rank,val0,val1,val2,val3]) rfl (by decide) (by decide) every
  clear every
  simp only [dInf,absDiff,file,rank] at far
  dsimp only at a b c r
  simp only [val0,val1,val2,val3,val4] at a b c r
  have sy : sk.2.val = 2 := by
    have prison : sk.2.val = 2 ∨ rs.2.val = 1 := by
      clear l r
      simp only [SafeRook,dInf,absDiff,file,rank] at far safe
      (try dsimp only at a b c)
      omega
    rcases prison with sy | ry
    · exact sy
    · have r0 := r
      clear r
      rw [KRKFiveMiddle.low_rook_bottom_iff (wk := ((3 : Fin 8),0)) (by decide) (by decide) (by omega)] at r0
      dsimp [KRKFiveMiddle.LowRookFive] at r0
      (try simp only [dInf,absDiff,file,rank] at far)
      (try dsimp only at a b c r0)
      simp only [KRKFiveNear.Five,KRKFiveNear.KingEntries,KRKFiveNear.RookEntries,RookSees,RookLine,OnSeg,dInf,absDiff,square_eq_iff,ry] at l
      simp only [SafeRook,dInf,absDiff,file,rank,ry] at safe
      (try dsimp only at l)
      simp_all [val0,val1,val2,val3,val4] <;> omega
  by_cases zero : rs.2.val = 0
  · left
    clear l r
    simp only [Terminal,Horizontal,file,rank,sy,zero,absDiff]
    simp only [SafeRook,dInf,absDiff,rank,file,sy,zero] at safe
    simp_all [val0,val1,val2,val3,val4] <;> omega
  · right
    by_cases one : rs.2.val = 1
    · have r0 := r
      clear r
      rw [KRKFiveMiddle.low_rook_bottom_iff (wk := ((3 : Fin 8),0)) (by decide) (by decide) (by omega)] at r0
      simp only [KRKFiveMiddle.LowRookFive] at r0
      simp only [KRKFiveNear.Five,KRKFiveNear.KingEntries,KRKFiveNear.RookEntries,
        square_eq_iff,Fin.ext_iff,dInf,absDiff,RookSees,RookLine,OnSeg,sy,one] at l
      dsimp [Region]
      (try dsimp only at a b c l r0)
      simp only [SafeRook,dInf,absDiff,file,rank,sy,one] at safe
      simp_all [val0,val1,val2,val3,val4] <;> omega
    · by_cases two : rs.2.val = 2
      · have r0 := r
        clear r
        rw [KRKFiveMiddle.rank_two_bottom_iff (wk := ((3 : Fin 8),0)) (by decide) (by decide) sy two] at r0
        dsimp [KRKFiveMiddle.RankTwoFive] at r0
        simp only [RookSees,RookLine,OnSeg,sy,two,dInf,absDiff] at l
        dsimp [Region]
        simp only [ne_iff_coords] at distinct
        (try dsimp only at a b c l r0)
        clear l
        simp_all [val0,val1,val2,val3,val4]
        omega
      · clear l r
        dsimp [Region]
        (try dsimp only at a b c)
        omega

theorem region_replies {sk rs wk t : Square} (distinct : sk ≠ rs)
    (file : wk.1.val = 2) (rank : wk.2.val = 0) (region : Region sk rs)
    (step : StepM ⟨sk,rs,wk,false⟩ ⟨sk,rs,t,true⟩) : KRKFiveGeometry.Clear sk rs t := by
  have guard := KRKCornerWeakBand.step_guard step
  have choices : (t.1.val = 1 ∧ t.2.val = 0) ∨ (t.1.val = 3 ∧ t.2.val = 0) := by
    simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,file,rank] at guard
    dsimp [Region] at region
    omega
  rcases choices with ⟨tx,ty⟩ | ⟨tx,ty⟩
  · have notCheck := guard.2.2.2
    simp only [RookSees,RookLine,OnSeg,tx,ty] at notCheck
    apply (KRKFiveNear.clear_iff ty tx distinct guard.2.1.symm guard.2.2.2).mpr
    rcases region with ⟨sy,h⟩
    rcases h with ⟨sx,rx,ry⟩ | ⟨sx,h⟩ | ⟨sx,h⟩ <;>
      simp only [KRKFiveNear.Five,KRKFiveNear.KingEntries,KRKFiveNear.RookEntries,
        square_eq_iff,Fin.ext_iff,dInf,absDiff,sy,sx] <;>
      (try dsimp only at *) <;>
      (try simp_all [val0,val1,val2,val3,val4]) <;> omega
  · apply (KRKFiveMiddle.clear_iff ty (by omega) (by omega) distinct guard.2.1.symm guard.2.2.2).mpr
    have notCheck := guard.2.2.2
    simp only [RookSees,RookLine,OnSeg,tx,ty] at notCheck
    rcases region with ⟨sy,h⟩
    rcases h with ⟨sx,rx,ry⟩ | ⟨sx,h⟩ | ⟨sx,h⟩ <;>
      simp only [KRKFiveMiddle.Five,KRKFiveMiddle.KingEntries,KRKFiveMiddle.RookEntries,
        square_eq_iff,Fin.ext_iff,dInf,absDiff,sy,sx,tx,ty] <;>
      dsimp [KRKCanonicalSlots.left,KRKCanonicalSlots.right] <;>
      (try dsimp only at *) <;>
      (try simp_all [val0,val1,val2,val3,val4]) <;> omega

theorem kernel_six_iff {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp) (far : 2 ≤ dInf sk wk)
    (file : wk.1.val = 2) (rank : wk.2.val = 0) : MateWithin σ 6 q ↔
      Terminal sk rs wk ∨ (Region sk rs ∧ SafeRook sk rs wk ∧ ∃ t, KRKCornerWeakBand.Guard sk rs wk t) := by
  by_cases mate : MatedK q
  · have terminal := (KRKMateGeometry.kernel_mate_iff material turn far).mp mate
    exact ⟨fun _ => Or.inl terminal,fun _ => Or.inl ⟨turn,mate⟩⟩
  rw [KRKSixGeometry.kernel_six_iff material turn mate]
  constructor
  · rintro ⟨safe,live,every⟩
    have result := necessary material.1 file rank far safe
      (fun t step => every t (KRKCornerWeakBand.step_guard step))
    exact result.elim Or.inl (fun region => Or.inr ⟨region,safe,live⟩)
  · rintro (terminal | ⟨region,safe,live⟩)
    · exact False.elim (mate ((KRKMateGeometry.kernel_mate_iff material turn far).mpr terminal))
    · exact ⟨safe,live,fun t guard => region_replies material.1 file rank region
        (StepM.lone guard.1 guard.2.1 guard.2.2.1 guard.2.2.2)⟩

/-- The additional second-edge boards have exact clock-free distance six. -/
def NewSix (sk rs : Square) : Prop := sk.2.val = 2 ∧
  ((sk.1.val = 2 ∧ ((rs.2.val = 2 ∧ 3 ≤ rs.1.val) ∨
    (rs.2.val = 1 ∧ (rs.1.val = 3 ∨ rs.1.val = 4)))) ∨
   (sk.1.val = 3 ∧ rs.2.val = 1 ∧ 4 ≤ rs.1.val))

theorem new_geometry {sk rs wk : Square} (file : wk.1.val = 2) (rank : wk.2.val = 0)
    (new : NewSix sk rs) : Region sk rs ∧ SafeRook sk rs wk ∧
      KRKCornerWeakBand.Guard sk rs wk ((1 : Fin 8),0) ∧ ¬Terminal sk rs wk := by
  simp only [NewSix] at new
  simp only [Region,SafeRook,KRKCornerWeakBand.Guard,Terminal,Horizontal,dInf,absDiff,
    RookSees,RookLine,OnSeg,ne_iff_coords,file,rank]
  (try dsimp only)
  simp only [val0,val1,val2,val3,val4]
  omega

theorem kernel_exact_six_iff {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp) (far : 2 ≤ dInf sk wk)
    (file : wk.1.val = 2) (rank : wk.2.val = 0) :
    (MateWithin σ 6 q ∧ ¬MateWithin σ 5 q) ↔ NewSix sk rs := by
  have four := KRKFourPlySecond.weak_four_iff material turn far rank file
  have last := KRKThreePly.last_middle_iff (sk := sk) (rs := rs) rank (by omega) (by omega)
  constructor
  · rintro ⟨six,notFive⟩
    have notFour : ¬MateWithin σ 4 q := fun win => notFive (mateWithin_mono win (by decide))
    have notMate : ¬MatedK q := fun mate => notFour (four.mpr (Or.inl mate))
    have notTerminal : ¬Terminal sk rs wk := fun terminal =>
      notMate ((KRKMateGeometry.kernel_mate_iff material turn far).mpr terminal)
    have region := (kernel_six_iff material turn far file rank).mp six
    have shape : Region sk rs := region.resolve_left notTerminal |>.1
    have notLast : ¬KRKLastReply.LastReply sk rs wk := fun h => notFour (four.mpr (Or.inr (Or.inl h)))
    have notOpp : ¬(sk.1.val = wk.1.val ∧ sk.2.val = 2 ∧ 3 ≤ rs.2.val) :=
      fun h => notFour (four.mpr (Or.inr (Or.inr h)))
    rw [last] at notLast
    dsimp [Region] at shape
    dsimp [NewSix]
    omega
  · intro new
    obtain ⟨region,safe,guard,notTerminal⟩ := new_geometry file rank new
    refine ⟨(kernel_six_iff material turn far file rank).mpr (Or.inr ⟨region,safe,⟨_,guard⟩⟩),?_⟩
    intro five
    have shape := four.mp (KRKFourPlyEscape.weak_five_to_four material turn five)
    rcases shape with mate | lastReply | opposition
    · exact notTerminal ((KRKMateGeometry.kernel_mate_iff material turn far).mp mate)
    · have h := last.mp lastReply
      dsimp [NewSix] at new
      omega
    · dsimp [NewSix] at new
      omega

end EndgameChess.Rules.KRKSixSecond





