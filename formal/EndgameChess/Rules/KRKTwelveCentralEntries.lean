import EndgameChess.Rules.KRKElevenNearStrip

namespace EndgameChess.Rules.KRKTwelveCentralEntries
open EndgameChess.KK KRKNativeFrame KRKFourPlyEscape
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

theorem near_eight_region : KRKEightGlobal.Region ((3 : Fin 8),2) ((4 : Fin 8),1) (1,0) := by
  change KRKEightEdge.Region ((3 : Fin 8),2) ((4 : Fin 8),1) (1,0)
  refine ⟨Or.inl (by decide),⟨.west,by dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg,KRKEightEdge.destination,KRKEightEdge.left]; decide⟩,?_⟩
  intro i guard
  cases i with
  | west =>
    refine Or.inl ⟨rfl,Or.inr (Or.inr ⟨.highMiddle,rfl,?_⟩)⟩
    exact Or.inl (by decide)
  | east =>
    exact Or.inr (Or.inr (Or.inl ⟨rfl,Or.inr ⟨.east,rfl,True.intro⟩⟩))
  | northWest => exact False.elim ((by dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg,KRKEightEdge.destination,KRKEightEdge.left]; decide : ¬KRKCornerWeakBand.Guard ((3 : Fin 8),2) ((4 : Fin 8),1) (1,0) (0,1)) guard)
  | north => exact False.elim ((by dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg,KRKEightEdge.destination,KRKEightEdge.left]; decide : ¬KRKCornerWeakBand.Guard ((3 : Fin 8),2) ((4 : Fin 8),1) (1,0) (1,1)) guard)
  | northEast => exact False.elim ((by dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg,KRKEightEdge.destination,KRKEightEdge.left]; decide : ¬KRKCornerWeakBand.Guard ((3 : Fin 8),2) ((4 : Fin 8),1) (1,0) (2,1)) guard)

theorem near_nine_clear {rs : Square} (rx : rs.1.val = 4) (high : 3 ≤ rs.2.val) :
    KRKNineGeometry.Clear ((3 : Fin 8),2) rs (1,0) := by
  have sees : RookSees rs ((4 : Fin 8),1) (3,2) (1,0) := by
    simp only [RookSees,RookLine,OnSeg,ne_iff_coords,rx]
    simp <;> omega
  exact KRKNineGeometry.rook_step_clear sees (by decide) (by decide) near_eight_region

/-- The aligned middle-edge family can reuse its six-ply strategy. -/
theorem middle_ten_region {rs : Square} (rx : rs.1.val = 4) (high : 3 ≤ rs.2.val) :
    KRKTenGlobal.Region ((3 : Fin 8),2) rs (3,0) := by
  let q := krkPos .white (3,2) rs (3,0) .black
  have distinct : ((3 : Fin 8),2) ≠ rs := by simp only [ne_iff_coords,rx]; dsimp; omega
  have notWeak : rs ≠ ((3 : Fin 8),0) := by simp only [ne_iff_coords,rx]; dsimp; omega
  have material : IsKRK q .white (3,2) rs (3,0) := ⟨distinct,by decide,notWeak,rfl⟩
  have region : KRKSixGlobal.Region ((3 : Fin 8),2) rs (3,0) := by
    change KRKSixGlobal.EdgeRegion ((3 : Fin 8),2) rs (3,0)
    exact Or.inr (Or.inr (Or.inr ⟨rfl,rfl,Or.inr (Or.inr ⟨rfl,high⟩)⟩))
  have safe : SafeRook ((3 : Fin 8),2) rs (3,0) := by dsimp [SafeRook,dInf,absDiff]; omega
  have live : ∃ t,KRKCornerWeakBand.Guard ((3 : Fin 8),2) rs (3,0) t := by
    refine ⟨((2 : Fin 8),0),?_⟩
    simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,rx]
    simp <;> omega
  have six := (KRKSixGlobal.kernel_six_iff material rfl (by decide)).mpr (Or.inr ⟨region,safe,live⟩)
  have notTerminal : ¬KRKMateGeometry.Terminal ((3 : Fin 8),2) rs (3,0) := by
    dsimp [KRKMateGeometry.Terminal,KRKMateGeometry.Horizontal] at *
    omega
  exact ((KRKTenGlobal.kernel_ten_iff material rfl (by decide)).mp (mateWithin_mono six (by decide))).resolve_left notTerminal

theorem middle_eight_region {rs : Square} (high : 3 ≤ rs.2.val) :
    KRKEightGlobal.Region ((3 : Fin 8),2) rs (3,0) := by
  let q := krkPos .white (3,2) rs (3,0) .black
  have distinct : ((3 : Fin 8),2) ≠ rs := by simp only [ne_iff_coords]; dsimp; omega
  have notWeak : rs ≠ ((3 : Fin 8),0) := by simp only [ne_iff_coords]; dsimp; omega
  have material : IsKRK q .white (3,2) rs (3,0) := ⟨distinct,by decide,notWeak,rfl⟩
  have region : KRKSixGlobal.Region ((3 : Fin 8),2) rs (3,0) := by
    change KRKSixGlobal.EdgeRegion ((3 : Fin 8),2) rs (3,0)
    exact Or.inr (Or.inr (Or.inr ⟨rfl,rfl,Or.inr (Or.inr ⟨rfl,high⟩)⟩))
  have safe : SafeRook ((3 : Fin 8),2) rs (3,0) := by dsimp [SafeRook,dInf,absDiff]; omega
  let x : Fin 8 := if rs.1.val = 2 then 4 else 2
  have width : (x.val = 2 ∨ x.val = 4) ∧ x.val ≠ rs.1.val := by dsimp [x]; split <;> (try simp_all) <;> omega
  have live : ∃ t,KRKCornerWeakBand.Guard ((3 : Fin 8),2) rs (3,0) t := by
    refine ⟨(x,0),?_⟩
    simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords]
    simp <;> omega
  have six := (KRKSixGlobal.kernel_six_iff material rfl (by decide)).mpr (Or.inr ⟨region,safe,live⟩)
  have notTerminal : ¬KRKMateGeometry.Terminal ((3 : Fin 8),2) rs (3,0) := by
    dsimp [KRKMateGeometry.Terminal,KRKMateGeometry.Horizontal]
    omega
  exact ((KRKEightGlobal.kernel_eight_iff material rfl (by decide)).mp (mateWithin_mono six (by decide))).resolve_left notTerminal

theorem middle_nine_clear {rs : Square} (rx : rs.1.val = 4) (high : 3 ≤ rs.2.val) :
    KRKNineGeometry.Clear ((3 : Fin 8),2) rs (3,0) := by
  let nr : Square := (5,rs.2)
  have sees : RookSees rs nr (3,2) (3,0) := by
    simp only [RookSees,RookLine,OnSeg,ne_iff_coords,nr,rx]
    simp <;> omega
  apply KRKNineGeometry.rook_step_clear sees ?_ ?_ (middle_eight_region (rs := nr) high)
  · simp [nr,ne_iff_coords]
  · simp [nr,ne_iff_coords]

theorem second_ten_region {rs : Square} (rx : rs.1.val = 4) (high : 3 ≤ rs.2.val) :
    KRKTenGlobal.Region ((3 : Fin 8),2) rs (2,0) := by
  change KRKTenEdge.Region ((3 : Fin 8),2) rs (2,0)
  have safe : SafeRook ((3 : Fin 8),2) rs (2,0) := by dsimp [SafeRook,dInf,absDiff]; omega
  have west : KRKCornerWeakBand.Guard ((3 : Fin 8),2) rs (2,0) (1,0) := by
    simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,rx]
    simp <;> omega
  refine ⟨safe,⟨.west,west⟩,?_⟩
  intro i guard
  cases i with
  | west =>
    have nine := (KRKNineEdge.clear_iff (wk := ((1 : Fin 8),0)) rfl (by decide)).mp (near_nine_clear rx high)
    simpa [KRKTenEdge.NineTest,KRKEightEdge.destination,KRKEightEdge.left] using nine
  | east =>
    have nine := (KRKNineEdge.clear_iff (wk := ((3 : Fin 8),0)) rfl (by decide)).mp (middle_nine_clear rx high)
    simpa [KRKTenEdge.NineTest,KRKEightEdge.destination,KRKEightEdge.right] using nine
  | northWest =>
    have nine : KRKNineInner.Nine ((3 : Fin 8),2) rs :=
      Or.inr (Or.inl ⟨.high,rfl,Or.inl high⟩)
    simpa [KRKTenEdge.NineTest,KRKEightEdge.destination,KRKEightEdge.left] using nine
  | north =>
    have far := guard.2.2.1
    change 2 ≤ dInf ((3 : Fin 8),2) (2,1) at far
    contradiction
  | northEast =>
    have far := guard.2.2.1
    change 2 ≤ dInf ((3 : Fin 8),2) (3,1) at far
    contradiction

end EndgameChess.Rules.KRKTwelveCentralEntries
