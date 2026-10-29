import EndgameChess.Rules.KRKNineMiddleLow

namespace EndgameChess.Rules.KRKTenCentralStrip
open EndgameChess.KK KRKNativeFrame KRKFourPlyEscape
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false

def Prison (sk rs : Square) : Prop :=
  (sk.1.val = 3 ∧ (sk.2.val = 2 ∨ sk.2.val = 3) ∧ rs.2.val = 4) ∨
  (sk.2.val = 5 ∧ sk.1.val ≤ 2 ∧ rs.1.val = 2) ∨
  (sk.1.val = 3 ∧ sk.2.val = 3 ∧ rs.1.val = 1) ∨
  (rs.1.val = 2 ∧ rs.2.val = 4)

theorem prison {sk rs : Square} (distinct : sk ≠ rs) (far : 2 ≤ dInf sk (1,3))
    (clear : KRKTenGeometry.Clear sk rs (1,3)) : Prison sk rs := by
  have a := covered_box (KRKTenSecondCorner.bad_neighbour_covered distinct clear (t := (1,4)) (by decide)
    (Or.inr (Or.inl ⟨Or.inl rfl,by decide,by decide⟩)))
  have b := covered_box (KRKTenSecondCorner.bad_neighbour_covered distinct clear (t := (2,2)) (by decide) (Or.inl (by decide)))
  have c := covered_box (KRKTenSecondCorner.bad_neighbour_covered distinct clear (t := (2,3)) (by decide) (Or.inl (by decide)))
  have d := covered_box (KRKTenSecondCorner.bad_neighbour_covered distinct clear (t := (2,4)) (by decide) (Or.inl (by decide)))
  have safe := clear.1
  clear clear
  dsimp at a b c d
  have kingFar : 3 ≤ sk.1.val ∨ sk.2.val ≤ 1 ∨ 5 ≤ sk.2.val := by
    dsimp [dInf,absDiff] at far
    omega
  have protection : 3 ≤ rs.1.val ∨ rs.2.val ≤ 1 ∨ 5 ≤ rs.2.val ∨
      (sk.1.val ≤ rs.1.val + 1 ∧ rs.1.val ≤ sk.1.val + 1 ∧
       sk.2.val ≤ rs.2.val + 1 ∧ rs.2.val ≤ sk.2.val + 1) := by
    dsimp [SafeRook,dInf,absDiff] at safe
    omega
  clear safe far
  dsimp [Prison]
  by_cases file : rs.1.val = 1 <;> by_cases row : rs.2.val = 4 <;> omega

private theorem near_guard_impossible {sk rs : Square} (distinct : sk ≠ rs)
    (clear : KRKTenGeometry.Clear sk rs (1,3)) (guard : KRKCornerWeakBand.Guard sk rs (1,3) (1,2))
    (noNine : ¬KRKNineNearStrip.Nine sk rs) : False := by
  exact noNine ((KRKNineNearStrip.clear_iff distinct (ne_of_dInf_pos (by have h := guard.2.2.1; omega))
    guard.2.1.symm guard.2.2.1 guard.2.2.2).mp (clear.2.2 _ guard))

theorem row_four_no_clear {sk rs : Square} (distinct : sk ≠ rs) (sx : sk.1.val = 3)
    (ry : rs.2.val = 4) (notOne : sk.2.val ≠ 1) : ¬KRKTenGeometry.Clear sk rs (1,3) := by
  intro clear
  have notFile : rs.1.val ≠ 1 := by
    have safe := clear.1
    dsimp [SafeRook,dInf,absDiff] at safe
    omega
  have guard : KRKCornerWeakBand.Guard sk rs (1,3) (1,2) := by
    simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,sx,ry]
    simp <;> omega
  apply near_guard_impossible distinct clear guard
  dsimp [KRKNineNearStrip.Nine]
  simp only [square_eq_iff,Fin.ext_iff]
  dsimp
  omega

theorem upper_no_clear {sk rs : Square} (distinct : sk ≠ rs) (sy : sk.2.val = 5)
    (rx : rs.1.val = 2) : ¬KRKTenGeometry.Clear sk rs (1,3) := by
  intro clear
  have notRow : rs.2.val ≠ 2 := by
    have safe := clear.1
    dsimp [SafeRook,dInf,absDiff] at safe
    omega
  have guard : KRKCornerWeakBand.Guard sk rs (1,3) (1,2) := by
    simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,sy,rx]
    simp <;> omega
  apply near_guard_impossible distinct clear guard
  dsimp [KRKNineNearStrip.Nine,dInf,absDiff]
  simp only [square_eq_iff,Fin.ext_iff]
  dsimp
  omega

theorem opposition_no_clear {sk rs : Square} (distinct : sk ≠ rs) (sx : sk.1.val = 3)
    (sy : sk.2.val = 3) (rx : rs.1.val = 1) : ¬KRKTenGeometry.Clear sk rs (1,3) := by
  intro clear
  have height : rs.2.val ≤ 1 ∨ 5 ≤ rs.2.val := by
    have safe := clear.1
    dsimp [SafeRook,dInf,absDiff] at safe
    omega
  rcases height with low | high
  · have guard : KRKCornerWeakBand.Guard sk rs (1,3) (0,3) := by
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,sx,sy,rx]
      simp <;> omega
    let g := Frame.ofSym symSwap
    have mapped := KRKNineGeometry.frame_map g distinct
      (ne_of_dInf_pos (by have h := guard.2.2.1; omega)) guard.2.1.symm guard.2.2.1 guard.2.2.2
      (clear.2.2 _ guard)
    exact KRKNineMiddleLow.no_nine (g.ne_iff.mpr distinct) sx (by dsimp [g,Frame.ofSym,symSwap]; omega) rx mapped
  · have guard : KRKCornerWeakBand.Guard sk rs (1,3) (0,4) := by
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,sx,sy,rx]
      simp <;> omega
    let g := (Frame.ofSym symSwap).comp (Frame.ofSym symX)
    have mapped := KRKNineGeometry.frame_map g distinct
      (ne_of_dInf_pos (by have h := guard.2.2.1; omega)) guard.2.1.symm guard.2.2.1 guard.2.2.2
      (clear.2.2 _ guard)
    exact KRKNineMiddleLow.no_nine (g.ne_iff.mpr distinct) sx
      (by dsimp [g,Frame.comp,Frame.ofSym,symSwap,symX]; omega) rx mapped

theorem not_clear {sk rs : Square} (distinct : sk ≠ rs) (far : 2 ≤ dInf sk (1,3)) :
    ¬KRKTenGeometry.Clear sk rs (1,3) := by
  intro clear
  rcases prison distinct far clear with ⟨sx,sy,ry⟩ | ⟨sy,_,rx⟩ | ⟨sx,sy,rx⟩ | ⟨rx,ry⟩
  · exact row_four_no_clear distinct sx ry (by omega) clear
  · exact upper_no_clear distinct sy rx clear
  · exact opposition_no_clear distinct sx sy rx clear
  · have shape : sk.1.val = 3 ∨ sk.2.val = 5 := by
      have safe := clear.1
      dsimp [SafeRook,dInf,absDiff] at safe far
      omega
    rcases shape with sx | sy
    · have notOne : sk.2.val ≠ 1 := by
        have safe := clear.1
        dsimp [SafeRook,dInf,absDiff] at safe
        omega
      exact row_four_no_clear distinct sx ry notOne clear
    · exact upper_no_clear distinct sy rx clear

theorem framed_not_clear (g : Frame) {sk rs wk : Square} (target : g.f wk = ((1 : Fin 8),3))
    (distinct : sk ≠ rs) (far : 2 ≤ dInf sk wk) : ¬KRKTenGeometry.Clear sk rs wk := by
  intro clear
  have mapped := KRKTenGeometry.frame_map g distinct clear
  have mappedFar : 2 ≤ dInf (g.f sk) (g.f wk) := by rw [g.distance]; exact far
  rw [target] at mapped mappedFar
  exact not_clear (g.ne_iff.mpr distinct) mappedFar mapped

theorem file_one_not_clear {sk rs wk : Square} (file : wk.1.val = 1)
    (low : 3 ≤ wk.2.val) (high : wk.2.val ≤ 4) (distinct : sk ≠ rs) (far : 2 ≤ dInf sk wk) :
    ¬KRKTenGeometry.Clear sk rs wk := by
  by_cases three : wk.2.val = 3
  · have target : wk = ((1 : Fin 8),3) := Prod.ext (Fin.ext file) (Fin.ext three)
    rw [target] at far ⊢
    exact not_clear distinct far
  · apply framed_not_clear (Frame.ofSym symY) (distinct := distinct) (far := far)
    rw [square_eq_iff]
    dsimp [Frame.ofSym,symY]
    omega

theorem middle_not_clear {sk rs wk : Square} (middle : KRKEightCentralStrip.MiddleStrip wk)
    (distinct : sk ≠ rs) (far : 2 ≤ dInf sk wk) : ¬KRKTenGeometry.Clear sk rs wk := by
  intro clear
  rcases middle with ⟨file,low,high⟩ | ⟨rank,low,high⟩
  · rcases file with left | right
    · exact file_one_not_clear left low high distinct far clear
    · let g := Frame.ofSym symX
      have mapped := KRKTenGeometry.frame_map g distinct clear
      exact file_one_not_clear (wk := g.f wk) (by dsimp [g,Frame.ofSym,symX]; omega) low high
        (g.ne_iff.mpr distinct) (by rw [g.distance]; exact far) mapped
  · rcases rank with bottom | top
    · let g := Frame.ofSym symSwap
      have mapped := KRKTenGeometry.frame_map g distinct clear
      exact file_one_not_clear bottom low high (g.ne_iff.mpr distinct)
        (by change 2 ≤ dInf (g.f sk) (g.f wk); rw [g.distance]; exact far) mapped
    · let g := (Frame.ofSym symSwap).comp (Frame.ofSym symX)
      have mapped := KRKTenGeometry.frame_map g distinct clear
      exact file_one_not_clear (wk := g.f wk) (by dsimp [g,Frame.comp,Frame.ofSym,symSwap,symX]; omega)
        low high (g.ne_iff.mpr distinct) (by rw [g.distance]; exact far) mapped

theorem middle_kernel_no_ten {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp)
    (middle : KRKEightCentralStrip.MiddleStrip wk) (far : 2 ≤ dInf sk wk) : ¬MateWithin σ 10 q := by
  intro ten
  have inside : 0 < KRKEdgeDepth.depth wk := by
    dsimp [KRKEightCentralStrip.MiddleStrip,KRKEdgeDepth.depth] at middle ⊢
    omega
  have notMate : ¬MatedK q := by
    intro mate
    have zero := KRKEdgeDepth.terminal_depth_zero ((KRKMateGeometry.kernel_mate_iff material turn far).mp mate)
    omega
  exact middle_not_clear middle material.1 far ((KRKTenGeometry.kernel_ten_iff material turn notMate).mp ten)

end EndgameChess.Rules.KRKTenCentralStrip
