import EndgameChess.Rules.KRKTwelveSecondCorner
import EndgameChess.Rules.KRKTwelveCentralEntries

namespace EndgameChess.Rules.KRKTwelveCentralStrip
open EndgameChess.KK KRKNativeFrame KRKFourPlyEscape
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false

def Prison (sk rs : Square) : Prop :=
  (sk.1.val = 3 ∧ (sk.2.val = 2 ∨ sk.2.val = 3) ∧ rs.2.val = 4) ∨
  (sk.2.val = 5 ∧ sk.1.val ≤ 2 ∧ rs.1.val = 2) ∨
  (sk.1.val = 3 ∧ sk.2.val = 3 ∧ rs.1.val = 1) ∨
  (rs.1.val = 2 ∧ rs.2.val = 4)

theorem prison {sk rs : Square} (distinct : sk ≠ rs) (far : 2 ≤ dInf sk (1,3))
    (clear : KRKTwelveGeometry.Clear sk rs (1,3)) : Prison sk rs := by
  have a := covered_box (KRKTwelveSecondCorner.bad_neighbour_covered distinct clear (t := (1,4)) (by decide)
    (Or.inr (Or.inl ⟨Or.inl rfl,by decide,by decide⟩)))
  have b := covered_box (KRKTwelveSecondCorner.bad_neighbour_covered distinct clear (t := (2,2)) (by decide) (Or.inl (by decide)))
  have c := covered_box (KRKTwelveSecondCorner.bad_neighbour_covered distinct clear (t := (2,3)) (by decide) (Or.inl (by decide)))
  have d := covered_box (KRKTwelveSecondCorner.bad_neighbour_covered distinct clear (t := (2,4)) (by decide) (Or.inl (by decide)))
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

theorem row_four_necessary {sk rs : Square} (distinct : sk ≠ rs) (sx : sk.1.val = 3)
    (sy : sk.2.val = 2 ∨ sk.2.val = 3) (ry : rs.2.val = 4)
    (clear : KRKTwelveGeometry.Clear sk rs (1,3)) : sk.2.val = 2 ∧ 3 ≤ rs.1.val := by
  have notFile : rs.1.val ≠ 1 := by
    have safe := clear.1
    dsimp [SafeRook,dInf,absDiff] at safe
    omega
  have guard : KRKCornerWeakBand.Guard sk rs (1,3) (1,2) := by
    simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,sx,ry]
    simp <;> omega
  have sourceNotWeak : rs ≠ ((1 : Fin 8),2) := by simp only [ne_iff_coords,ry]; dsimp; omega
  have evaluated := (KRKElevenNearStrip.clear_iff distinct sourceNotWeak).mp (clear.2.2 _ guard)
  have rank : sk.2.val = 2 := by
    rcases evaluated with ⟨i,distance,_,shape⟩ | ⟨i,equal,condition⟩
    · cases i <;> dsimp [KRKElevenNearStrip.king,KRKElevenNearStrip.RookRegion,dInf,absDiff] at distance shape <;> omega
    · cases i <;> simp only [KRKElevenNearStrip.king,square_eq_iff,Fin.ext_iff] at equal <;> dsimp at equal <;> omega
  have safe := clear.1
  dsimp [SafeRook,dInf,absDiff] at safe
  exact ⟨rank,by omega⟩

theorem upper_necessary {sk rs : Square} (distinct : sk ≠ rs) (sy : sk.2.val = 5)
    (sx : sk.1.val ≤ 2) (rx : rs.1.val = 2) (clear : KRKTwelveGeometry.Clear sk rs (1,3)) :
    4 ≤ rs.2.val ∧ (rs.2.val = 4 → 1 ≤ sk.1.val) := by
  have notRow : rs.2.val ≠ 2 := by
    have safe := clear.1
    dsimp [SafeRook,dInf,absDiff] at safe
    omega
  have guard : KRKCornerWeakBand.Guard sk rs (1,3) (1,2) := by
    simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,sy,rx]
    simp <;> omega
  have sourceNotWeak : rs ≠ ((1 : Fin 8),2) := by simp only [ne_iff_coords,rx]; dsimp; omega
  have evaluated := (KRKElevenNearStrip.clear_iff distinct sourceNotWeak).mp (clear.2.2 _ guard)
  have height : 3 ≤ rs.2.val := by
    rcases evaluated with ⟨i,distance,_,shape⟩ | ⟨i,equal,condition⟩
    · cases i <;> dsimp [KRKElevenNearStrip.king,KRKElevenNearStrip.RookRegion,dInf,absDiff] at distance shape <;> omega
    · cases i <;> simp only [KRKElevenNearStrip.king,square_eq_iff,Fin.ext_iff] at equal <;> dsimp at equal <;> omega
  have safe := clear.1
  dsimp [SafeRook,dInf,absDiff] at safe
  constructor <;> omega

theorem protected_two_four_no_clear {sk rs : Square} (distinct : sk ≠ rs) (sx : sk.1.val = 3)
    (rx : rs.1.val = 2) (ry : rs.2.val = 4) : ¬KRKTwelveGeometry.Clear sk rs (1,3) := by
  intro clear
  have guard : KRKCornerWeakBand.Guard sk rs (1,3) (1,2) := by
    simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,sx,rx,ry]
    simp <;> omega
  have sourceNotWeak : rs ≠ ((1 : Fin 8),2) := by simp only [ne_iff_coords,rx]; dsimp; omega
  have evaluated := (KRKElevenNearStrip.clear_iff distinct sourceNotWeak).mp (clear.2.2 _ guard)
  have safe := clear.1
  dsimp [SafeRook,dInf,absDiff] at safe
  rcases evaluated with ⟨i,distance,_,shape⟩ | ⟨i,equal,condition⟩
  · cases i <;> dsimp [KRKElevenNearStrip.king,KRKElevenNearStrip.RookRegion,dInf,absDiff] at distance shape <;> omega
  · cases i <;> simp only [KRKElevenNearStrip.king,square_eq_iff,Fin.ext_iff] at equal <;>
      dsimp [KRKElevenNearStrip.RookCondition,KRKElevenNearStrip.SideRow,KRKElevenNearStrip.SideFile,
        KRKNineNearStrip.RookCondition] at condition <;> dsimp at equal <;> omega

/-- A necessary geometric reduction only. Edge replies still require
independent eleven-ply evaluation before this can be a winning criterion. -/
def Candidate (sk rs : Square) : Prop :=
  (sk.1.val = 3 ∧ sk.2.val = 2 ∧ rs.2.val = 4 ∧ 3 ≤ rs.1.val) ∨
  (sk.2.val = 5 ∧ sk.1.val ≤ 2 ∧ rs.1.val = 2 ∧ 4 ≤ rs.2.val ∧
    (rs.2.val = 4 → 1 ≤ sk.1.val)) ∨
  (sk.1.val = 3 ∧ sk.2.val = 3 ∧ rs.1.val = 1 ∧ (rs.2.val ≤ 1 ∨ 5 ≤ rs.2.val))

theorem candidate_necessary {sk rs : Square} (distinct : sk ≠ rs) (far : 2 ≤ dInf sk (1,3))
    (clear : KRKTwelveGeometry.Clear sk rs (1,3)) : Candidate sk rs := by
  rcases prison distinct far clear with ⟨sx,sy,ry⟩ | ⟨sy,sx,rx⟩ | ⟨sx,sy,rx⟩ | ⟨rx,ry⟩
  · have shape := row_four_necessary distinct sx sy ry clear
    exact Or.inl ⟨sx,shape.1,ry,shape.2⟩
  · have shape := upper_necessary distinct sy sx rx clear
    exact Or.inr (Or.inl ⟨sy,sx,rx,shape⟩)
  · have height : rs.2.val ≤ 1 ∨ 5 ≤ rs.2.val := by
      have safe := clear.1
      dsimp [SafeRook,dInf,absDiff] at safe
      omega
    exact Or.inr (Or.inr ⟨sx,sy,rx,height⟩)
  · have shape : sk.1.val = 3 ∨ sk.2.val = 5 := by
      have safe := clear.1
      dsimp [SafeRook,dInf,absDiff] at safe far
      omega
    by_cases sx : sk.1.val = 3
    · exact False.elim (protected_two_four_no_clear distinct sx rx ry clear)
    · have sy : sk.2.val = 5 := shape.resolve_left sx
      have file : sk.1.val ≤ 2 := by
        have safe := clear.1
        dsimp [SafeRook,dInf,absDiff] at safe far
        omega
      have condition := upper_necessary distinct sy file rx clear
      exact Or.inr (Or.inl ⟨sy,file,rx,condition⟩)

def RowFour (sk rs : Square) : Prop :=
  sk.1.val = 3 ∧ sk.2.val = 2 ∧ rs.2.val = 4 ∧ 3 ≤ rs.1.val

theorem row_four_clear {sk rs : Square} (region : RowFour sk rs) : KRKTwelveGeometry.Clear sk rs (1,3) := by
  obtain ⟨sx,sy,ry,rx⟩ := region
  have distinct : sk ≠ rs := by simp only [ne_iff_coords,sy,ry]; omega
  have safe : SafeRook sk rs (1,3) := by dsimp [SafeRook,dInf,absDiff]; omega
  refine ⟨safe,⟨((0 : Fin 8),2),?_⟩,?_⟩
  · simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,sx,sy,ry]
    simp <;> omega
  · intro t guard
    have targets : t = ((0 : Fin 8),2) ∨ t = ((0 : Fin 8),3) ∨ t = ((1 : Fin 8),2) := by
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,sx,sy,ry] at guard
      simp only [square_eq_iff,Fin.ext_iff]
      dsimp at guard ⊢
      omega
    rcases targets with rfl | rfl | rfl
    · let g := Frame.ofSym symSwap
      have region : KRKTenGlobal.Region (3,2) (g.f rs) (2,0) :=
        KRKTwelveCentralEntries.second_ten_region ry rx
      have apart : ((3 : Fin 8),2) ≠ g.f rs := by
        simp only [ne_iff_coords]
        dsimp [g,Frame.ofSym,symSwap]
        omega
      have mapped : KRKElevenGeometry.Clear (g.f sk) (g.f rs) (g.f ((0 : Fin 8),2)) :=
        KRKElevenGeometry.king_step_clear (ns := ((3 : Fin 8),2))
          (by dsimp [g,Frame.ofSym,symSwap,dInf,absDiff]; omega) apart (by decide) region
      have back := KRKElevenGeometry.frame_map g.inverse (g.ne_iff.mpr distinct)
        (g.ne_iff.mpr (ne_of_dInf_pos (by have h := guard.2.2.1; omega)))
        (g.ne_iff.mpr guard.2.1.symm) (by rw [g.distance]; exact guard.2.2.1)
        (fun h => guard.2.2.2 ((g.sees _ _ _ _).mp h)) mapped
      simpa only [Frame.inverse,g.left_inv] using back
    · let g := Frame.ofSym symSwap
      have region : KRKTenGlobal.Region (3,2) (g.f rs) (3,0) :=
        KRKTwelveCentralEntries.middle_ten_region ry rx
      have apart : ((3 : Fin 8),2) ≠ g.f rs := by
        simp only [ne_iff_coords]
        dsimp [g,Frame.ofSym,symSwap]
        omega
      have mapped : KRKElevenGeometry.Clear (g.f sk) (g.f rs) (g.f ((0 : Fin 8),3)) :=
        KRKElevenGeometry.king_step_clear (ns := ((3 : Fin 8),2))
          (by dsimp [g,Frame.ofSym,symSwap,dInf,absDiff]; omega) apart (by decide) region
      have back := KRKElevenGeometry.frame_map g.inverse (g.ne_iff.mpr distinct)
        (g.ne_iff.mpr (ne_of_dInf_pos (by have h := guard.2.2.1; omega)))
        (g.ne_iff.mpr guard.2.1.symm) (by rw [g.distance]; exact guard.2.2.1)
        (fun h => guard.2.2.2 ((g.sees _ _ _ _).mp h)) mapped
      simpa only [Frame.inverse,g.left_inv] using back
    · have notWeak : rs ≠ ((1 : Fin 8),2) := by simp only [ne_iff_coords,ry]; dsimp; omega
      apply (KRKElevenNearStrip.clear_iff distinct notWeak).mpr
      have equal : sk = KRKElevenNearStrip.king .side := Prod.ext (Fin.ext sx) (Fin.ext sy)
      exact Or.inr ⟨.side,equal,Or.inr (Or.inr (Or.inl ry))⟩

theorem kernel_row_four_iff {q : Position} {σ : Colour} {sk rs : Square}
    (material : IsKRK q σ sk rs (1,3)) (turn : q.turn = σ.opp) (far : 2 ≤ dInf sk (1,3))
    (sx : sk.1.val = 3) (sy : sk.2.val = 2 ∨ sk.2.val = 3) (ry : rs.2.val = 4) :
    MateWithin σ 12 q ↔ RowFour sk rs := by
  have notMate : ¬MatedK q := by
    intro mate
    have zero := KRKEdgeDepth.terminal_depth_zero ((KRKMateGeometry.kernel_mate_iff material turn far).mp mate)
    change 1 = 0 at zero
    contradiction
  constructor
  · intro win
    have shape := row_four_necessary material.1 sx sy ry
      ((KRKTwelveGeometry.kernel_twelve_iff material turn notMate).mp win)
    exact ⟨sx,shape.1,ry,shape.2⟩
  · intro region
    exact (KRKTwelveGeometry.kernel_twelve_iff material turn notMate).mpr (row_four_clear region)

theorem kernel_row_four_exact_twelve {q : Position} {σ : Colour} {sk rs : Square}
    (material : IsKRK q σ sk rs (1,3)) (turn : q.turn = σ.opp) (far : 2 ≤ dInf sk (1,3))
    (sx : sk.1.val = 3) (sy : sk.2.val = 2 ∨ sk.2.val = 3) (ry : rs.2.val = 4) :
    (MateWithin σ 12 q ∧ ¬MateWithin σ 11 q) ↔ RowFour sk rs := by
  have notTen := KRKTenCentralStrip.middle_kernel_no_ten material turn
    (Or.inl ⟨Or.inl rfl,by decide,by decide⟩) far
  exact ⟨fun h => (kernel_row_four_iff material turn far sx sy ry).mp h.1,fun region =>
    ⟨(kernel_row_four_iff material turn far sx sy ry).mpr region,
      fun eleven => notTen (KRKTenGeometry.weak_eleven_ten material turn eleven)⟩⟩

end EndgameChess.Rules.KRKTwelveCentralStrip
