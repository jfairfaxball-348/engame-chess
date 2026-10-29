import EndgameChess.Rules.KRKTwelveGeometry
import EndgameChess.Rules.KRKElevenNearBoundary
import EndgameChess.Rules.KRKTenCentralStripHolding

namespace EndgameChess.Rules.KRKTwelveSecondCorner
open EndgameChess.KK KRKNativeFrame KRKFourPlyEscape
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

private theorem eleven_middle_not_clear {sk rs t : Square} (distinct : sk ≠ rs) (notKing : sk ≠ t)
    (notRook : rs ≠ t) (far : 2 ≤ dInf sk t) (notCheck : ¬RookSees rs t sk t)
    (middle : KRKEightCentralStrip.MiddleStrip t) : ¬KRKElevenGeometry.Clear sk rs t := by
  intro clear
  let q := krkPos .white sk rs t .white
  have material : IsKRK q .white sk rs t := ⟨distinct,notKing,notRook,rfl⟩
  have nine := KRKElevenGeometry.sufficient material rfl far notCheck clear
  exact KRKTenCentralStripHolding.strong_no_twelve material rfl middle (mateWithin_mono nine (by decide))

theorem bad_neighbour_covered {sk rs wk t : Square} (distinct : sk ≠ rs)
    (clear : KRKTwelveGeometry.Clear sk rs wk) (distance : dInf wk t = 1)
    (bad : 2 ≤ KRKEdgeDepth.depth t ∨ KRKEightCentralStrip.MiddleStrip t) : Covered sk rs t := by
  by_cases king : dInf sk t ≤ 1
  · exact Or.inl king
  by_cases line : RookLine rs t
  · exact Or.inr line
  have notRook : t ≠ rs := by
    intro equal
    have safe := clear.1
    rcases safe with distant | guarded
    · rw [equal,dInf_comm] at distance; omega
    · rw [equal] at king; omega
  have far : 2 ≤ dInf sk t := by omega
  have notCheck : ¬RookSees rs t sk t := fun seen => line seen.1
  have guard : KRKCornerWeakBand.Guard sk rs wk t := ⟨distance,notRook,far,notCheck⟩
  have nine := clear.2.2 t guard
  rcases bad with deep | middle
  · have shallow := KRKTwelveGeometry.eleven_weak_depth nine
    omega
  · exact False.elim (eleven_middle_not_clear distinct (ne_of_dInf_pos (by omega)) notRook.symm far notCheck middle nine)

/-- Covering the five destinations outside the nine-ply weak-square domain
forces a fourth-file king/third-rank rook, or the transposed configuration. -/
theorem prison {sk rs : Square} (distinct : sk ≠ rs) (far : 2 ≤ dInf sk (2,2))
    (clear : KRKTwelveGeometry.Clear sk rs (2,2)) :
    (sk.1.val = 4 ∧ rs.2.val = 3) ∨ (sk.2.val = 4 ∧ rs.1.val = 3) := by
  have a := covered_box (bad_neighbour_covered distinct clear (t := (1,3)) (by decide) (Or.inr (by
    exact Or.inl ⟨Or.inl rfl,by decide,by decide⟩)))
  have b := covered_box (bad_neighbour_covered distinct clear (t := (2,3)) (by decide) (Or.inl (by decide)))
  have c := covered_box (bad_neighbour_covered distinct clear (t := (3,1)) (by decide) (Or.inr (by
    exact Or.inr ⟨Or.inl rfl,by decide,by decide⟩)))
  have d := covered_box (bad_neighbour_covered distinct clear (t := (3,2)) (by decide) (Or.inl (by decide)))
  have e := covered_box (bad_neighbour_covered distinct clear (t := (3,3)) (by decide) (Or.inl (by decide)))
  have safe := clear.1
  clear clear
  dsimp [SafeRook,dInf,absDiff] at safe far
  dsimp at a b c d e
  omega

/-- New second-interior-corner family, up to transposition. -/
def Horizontal (sk rs : Square) : Prop :=
  sk.1.val = 4 ∧ sk.2.val = 1 ∧ rs.2.val = 3 ∧ 4 ≤ rs.1.val

def Region (sk rs : Square) : Prop := Horizontal sk rs ∨ Horizontal (symSwap.f sk) (symSwap.f rs)

theorem horizontal_necessary {sk rs : Square} (distinct : sk ≠ rs) (sx : sk.1.val = 4)
    (ry : rs.2.val = 3) (clear : KRKTwelveGeometry.Clear sk rs (2,2)) : Horizontal sk rs := by
  have notTwo : rs.1.val ≠ 2 := by
    intro same
    have safe := clear.1
    dsimp [SafeRook,dInf,absDiff] at safe
    omega
  have guard : KRKCornerWeakBand.Guard sk rs (2,2) (2,1) := by
    simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,sx,ry]
    simp <;> omega
  let g := Frame.ofSym symSwap
  have notKing : sk ≠ ((2 : Fin 8),1) := ne_of_dInf_pos (by have h := guard.2.2.1; omega)
  have mapped := KRKElevenGeometry.frame_map g distinct notKing guard.2.1.symm guard.2.2.1 guard.2.2.2
    (clear.2.2 _ guard)
  have condition := KRKElevenNearBoundary.upper_necessary (sk := g.f sk) (rs := g.f rs)
    sx ry mapped
  have covered := covered_box (bad_neighbour_covered distinct clear (t := (3,2)) (by decide) (Or.inl (by decide)))
  have safe := clear.1
  dsimp [KRKElevenNearBoundary.UpperEntry,g,Frame.ofSym,symSwap] at condition
  dsimp [SafeRook,dInf,absDiff] at safe
  dsimp [Horizontal] at *
  omega

theorem necessary {sk rs : Square} (distinct : sk ≠ rs) (far : 2 ≤ dInf sk (2,2))
    (clear : KRKTwelveGeometry.Clear sk rs (2,2)) : Region sk rs := by
  rcases prison distinct far clear with ⟨sx,ry⟩ | ⟨sy,rx⟩
  · exact Or.inl (horizontal_necessary distinct sx ry clear)
  · have mapped := KRKTwelveGeometry.frame_map (Frame.ofSym symSwap) distinct clear
    exact Or.inr (horizontal_necessary (symSwap.ne_iff.mpr distinct) sy rx mapped)

theorem horizontal_clear {sk rs : Square} (region : Horizontal sk rs) :
    KRKTwelveGeometry.Clear sk rs (2,2) := by
  obtain ⟨sx,sy,ry,rx⟩ := region
  have distinct : sk ≠ rs := by simp only [ne_iff_coords,sy,ry]; omega
  have safe : SafeRook sk rs (2,2) := by dsimp [SafeRook,dInf,absDiff]; omega
  refine ⟨safe,⟨((1 : Fin 8),1),?_⟩,?_⟩
  · simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,sx,sy,ry]
    simp <;> omega
  · intro t guard
    have targets : t = ((1 : Fin 8),1) ∨ t = ((1 : Fin 8),2) ∨ t = ((2 : Fin 8),1) := by
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,sx,sy,ry] at guard
      simp only [square_eq_iff,Fin.ext_iff]
      dsimp at guard ⊢
      omega
    rcases targets with rfl | rfl | rfl
    · have inner : KRKTenGlobal.Region (3,1) rs (1,1) := by
        change KRKTenInteriorExact.Region (3,1) rs (1,1)
        refine ⟨rfl,Or.inl ⟨rfl,Or.inl (Or.inr (Or.inl ?_))⟩⟩
        exact ⟨rfl,rfl,Or.inl ry⟩
      apply KRKElevenGeometry.king_step_clear (ns := ((3 : Fin 8),1)) ?_ ?_ (by decide) inner
      · dsimp [dInf,absDiff]; omega
      · simp only [ne_iff_coords,ry]; dsimp; omega
    · have near : KRKTenGlobal.Region (3,2) rs (1,2) := by
        change KRKTenInteriorExact.Region (3,2) rs (1,2)
        exact ⟨rfl,Or.inr ⟨rfl,Or.inr (Or.inl ⟨rfl,rfl,ry,by change 2 ≤ rs.1.val; omega⟩)⟩⟩
      apply KRKElevenGeometry.king_step_clear (ns := ((3 : Fin 8),2)) ?_ ?_ (by decide) near
      · dsimp [dInf,absDiff]; omega
      · simp only [ne_iff_coords,ry]; dsimp; omega
    · let g := Frame.ofSym symSwap
      have upper : KRKElevenGeometry.Clear (g.f sk) (g.f rs) (g.f ((2 : Fin 8),1)) :=
        KRKElevenNearBoundary.upper_sufficient sx ry (Or.inr ⟨sy,by change 3 ≤ rs.1.val; omega⟩)
      have back := KRKElevenGeometry.frame_map g.inverse (g.ne_iff.mpr distinct)
        (g.ne_iff.mpr (ne_of_dInf_pos (by have h := guard.2.2.1; omega)))
        (g.ne_iff.mpr guard.2.1.symm) (by rw [g.distance]; exact guard.2.2.1)
        (fun h => guard.2.2.2 ((g.sees _ _ _ _).mp h)) upper
      simpa only [Frame.inverse,g.left_inv] using back

theorem sufficient {sk rs : Square} (region : Region sk rs) : KRKTwelveGeometry.Clear sk rs (2,2) := by
  rcases region with horizontal | vertical
  · exact horizontal_clear horizontal
  · have mapped := horizontal_clear vertical
    have apart : symSwap.f sk ≠ symSwap.f rs := by
      obtain ⟨sx,sy,ry,rx⟩ := vertical
      simp only [ne_iff_coords] at *
      omega
    have back := KRKTwelveGeometry.frame_map (Frame.ofSym symSwap) apart mapped
    simpa only [Frame.ofSym,symSwap.invol,show symSwap.f ((2 : Fin 8),2) = ((2 : Fin 8),2) from rfl] using back

theorem kernel_twelve_iff {q : Position} {σ : Colour} {sk rs : Square}
    (material : IsKRK q σ sk rs (2,2)) (turn : q.turn = σ.opp) (far : 2 ≤ dInf sk (2,2)) :
    MateWithin σ 12 q ↔ Region sk rs := by
  have notMate : ¬MatedK q := by
    intro mate
    have zero := KRKEdgeDepth.terminal_depth_zero ((KRKMateGeometry.kernel_mate_iff material turn far).mp mate)
    change 2 = 0 at zero
    contradiction
  exact (KRKTwelveGeometry.kernel_twelve_iff material turn notMate).trans
    ⟨necessary material.1 far,sufficient⟩

theorem kernel_exact_twelve {q : Position} {σ : Colour} {sk rs : Square}
    (material : IsKRK q σ sk rs (2,2)) (turn : q.turn = σ.opp) (far : 2 ≤ dInf sk (2,2)) :
    (MateWithin σ 12 q ∧ ¬MateWithin σ 11 q) ↔ Region sk rs := by
  have notTen := KRKTenSecondCorner.kernel_no_ten material turn far
  exact ⟨fun h => (kernel_twelve_iff material turn far).mp h.1,fun region =>
    ⟨(kernel_twelve_iff material turn far).mpr region,
      fun eleven => notTen (KRKTenGeometry.weak_eleven_ten material turn eleven)⟩⟩

end EndgameChess.Rules.KRKTwelveSecondCorner
