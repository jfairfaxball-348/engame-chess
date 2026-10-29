import EndgameChess.Rules.KRKTenNearStrip
import EndgameChess.Rules.KRKNineNearDiagonal

namespace EndgameChess.Rules.KRKEightDiagonalEntries
open EndgameChess.KK KRKNativeFrame
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

theorem corner_clear {rs : Square} (far : 3 ≤ dInf rs (0,0)) : KRKEightGeometry.Clear (2,2) rs (0,0) := by
  have distinct : ((2 : Fin 8),2) ≠ rs := by
    intro equal
    rw [←equal] at far
    change 3 ≤ 2 at far
    omega
  have live : ∃ t,KRKCornerWeakBand.Guard ((2 : Fin 8),2) rs (0,0) t := by
    by_cases side : rs.1.val = 0 ∨ rs.2.val = 1
    · refine ⟨((1 : Fin 8),0),?_⟩
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords]
      dsimp [dInf,absDiff] at far
      simp <;> omega
    · refine ⟨((0 : Fin 8),1),?_⟩
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords]
      dsimp [dInf,absDiff] at far
      simp <;> omega
  refine ⟨Or.inl (by omega),live,?_⟩
  intro t guard
  have targets : t = ((0 : Fin 8),1) ∨ t = ((1 : Fin 8),0) := by
    have distance := guard.1
    have separate := guard.2.2.1
    simp only [square_eq_iff,Fin.ext_iff]
    dsimp [dInf,absDiff] at distance separate
    dsimp
    omega
  rcases targets with rfl | rfl
  · apply (KRKEightEdge.seven_test_iff distinct (by decide) guard.2.1.symm guard.2.2.1 guard.2.2.2
      (by decide) (by decide)).mpr
    simpa [KRKEightEdge.SevenTest,KRKSevenNear.Seven] using
      (Or.inr ⟨.diagonal,rfl,True.intro⟩ : KRKSevenNear.Seven (symSwap.f ((2 : Fin 8),2)) (symSwap.f rs))
  · exact (KRKSevenNear.clear_iff distinct guard.2.1.symm guard.2.2.2).mpr (Or.inr ⟨.diagonal,rfl,True.intro⟩)

theorem corner_region {rs : Square} (far : 3 ≤ dInf rs (0,0)) : KRKEightGlobal.Region (2,2) rs (0,0) := by
  have distinct : ((2 : Fin 8),2) ≠ rs := by intro h; rw [←h] at far; change 3 ≤ 2 at far; omega
  exact (KRKEightGlobal.edge_clear_iff distinct (by decide)).mp (corner_clear far)

theorem near_region {rs : Square} (distinct : ((2 : Fin 8),2) ≠ rs) (safe : SafeRook (2,2) rs (1,0)) :
    KRKEightGlobal.Region (2,2) rs (1,0) :=
  (KRKEightGlobal.edge_clear_iff distinct (by decide)).mp (KRKTenNearStrip.diagonal_near_eight_clear distinct safe)

theorem second_region {rs : Square} (region : KRKSevenSecond.RookRegion rs .middle) :
    KRKEightGlobal.Region (2,2) rs (2,0) := by
  have p := KRKSevenSecond.properties region
  have notWeak : rs ≠ ((2 : Fin 8),0) := by
    dsimp [KRKSevenSecond.RookRegion] at region
    simp only [ne_iff_coords]
    dsimp
    omega
  let q := krkPos .white (2,2) rs (2,0) .black
  have material : IsKRK q .white (2,2) rs (2,0) := ⟨p.1,by decide,notWeak,rfl⟩
  have sixRegion := KRKSevenSecond.global_region_iff.mpr (KRKSevenSecond.shape_iff.mpr ⟨.middle,rfl,region⟩)
  have six := (KRKSixGlobal.kernel_six_iff material rfl p.2.1).mpr (Or.inr ⟨sixRegion,p.2.2.2,p.2.2.1⟩)
  have eight : MateWithin .white 8 q := mateWithin_mono six (by decide)
  have notTerminal : ¬KRKMateGeometry.Terminal (2,2) rs (2,0) := by
    intro terminal
    have mate := (KRKMateGeometry.kernel_mate_iff material rfl p.2.1).mpr terminal
    obtain ⟨t,guard⟩ := p.2.2.1
    exact mate.2 ⟨_,⟨_,KRKCornerWeakBand.guard_legal material rfl guard,rfl⟩⟩
  exact ((KRKEightGlobal.kernel_eight_iff material rfl p.2.1).mp eight).resolve_left notTerminal

end EndgameChess.Rules.KRKEightDiagonalEntries
