import EndgameChess.Rules.KRKTwelveCentralOppositionEntries

namespace EndgameChess.Rules.KRKTwelveCentralExact
open EndgameChess.KK KRKNativeFrame
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

def Protected (sk rs : Square) : Prop := sk = ((1 : Fin 8),5) ∧ rs = ((2 : Fin 8),4)

def Opposition (sk rs : Square) : Prop :=
  sk.1.val = 3 ∧ sk.2.val = 3 ∧ rs.1.val = 1 ∧ (rs.2.val ≤ 1 ∨ 5 ≤ rs.2.val)

def Region (sk rs : Square) : Prop :=
  KRKTwelveCentralStrip.RowFour sk rs ∨ Protected sk rs ∨ Opposition sk rs

theorem opposition_clear {sk rs : Square} (region : Opposition sk rs) :
    KRKTwelveGeometry.Clear sk rs (1,3) := by
  obtain ⟨sx,sy,rx,height⟩ := region
  have kingEq : sk = ((3 : Fin 8),3) := Prod.ext (Fin.ext sx) (Fin.ext sy)
  subst sk
  have distinct : ((3 : Fin 8),3) ≠ rs := by simp [ne_iff_coords,rx,show ((3 : Fin 8).val) = 3 from rfl]
  have safe : SafeRook ((3 : Fin 8),3) rs (1,3) := by dsimp [SafeRook,dInf,absDiff]; omega
  refine ⟨safe,⟨((0 : Fin 8),3),?_⟩,?_⟩
  · simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,rx]
    dsimp
    simp <;> omega
  · intro t guard
    have targets : t = ((0 : Fin 8),2) ∨ t = ((0 : Fin 8),3) ∨ t = ((0 : Fin 8),4) := by
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,rx] at guard
      simp only [square_eq_iff,Fin.ext_iff]
      dsimp at guard ⊢
      omega
    have edge : ∀ {j : Fin 8}, j = 2 ∨ j = 3 ∨ j = 4 →
        KRKCornerWeakBand.Guard ((3 : Fin 8),3) rs (1,3) (0,j) →
        KRKElevenGeometry.Clear ((3 : Fin 8),3) rs (0,j) := by
      intro j choice guard
      let g := Frame.ofSym symSwap
      have mapped : KRKElevenGeometry.Clear (g.f ((3 : Fin 8),3)) (g.f rs) (g.f ((0 : Fin 8),j)) := by
        rcases choice with rfl | rfl | rfl
        · exact KRKTwelveCentralOppositionEntries.second_eleven rx (by change rs.2.val ≠ 4; omega)
        · exact KRKTwelveCentralOppositionEntries.middle_eleven rx (by change rs.2.val ≠ 3; omega)
        · exact KRKTwelveCentralOppositionEntries.high_eleven rx (by change rs.2.val ≠ 4; omega)
      have back := KRKElevenGeometry.frame_map g.inverse (g.ne_iff.mpr distinct)
        (g.ne_iff.mpr (ne_of_dInf_pos (by have h := guard.2.2.1; omega)))
        (g.ne_iff.mpr guard.2.1.symm) (by rw [g.distance]; exact guard.2.2.1)
        (fun h => guard.2.2.2 ((g.sees _ _ _ _).mp h)) mapped
      simpa only [Frame.inverse,g.left_inv] using back
    rcases targets with rfl | rfl | rfl
    · exact edge (Or.inl rfl) guard
    · exact edge (Or.inr (Or.inl rfl)) guard
    · exact edge (Or.inr (Or.inr rfl)) guard

theorem necessary {sk rs : Square} (apart : sk ≠ rs) (far : 2 ≤ dInf sk (1,3))
    (clear : KRKTwelveGeometry.Clear sk rs (1,3)) : Region sk rs := by
  rcases KRKTwelveCentralStrip.candidate_necessary apart far clear with row | ⟨sy,sx,rx,_,_⟩ | opposition
  · exact Or.inl row
  · have shape := (KRKTwelveCentralUpper.upper_iff apart sy sx rx).mp clear
    exact Or.inr (Or.inl ⟨Prod.ext (Fin.ext shape.1) (Fin.ext sy),Prod.ext (Fin.ext rx) (Fin.ext shape.2)⟩)
  · exact Or.inr (Or.inr opposition)

theorem sufficient {sk rs : Square} (region : Region sk rs) : KRKTwelveGeometry.Clear sk rs (1,3) := by
  rcases region with row | ⟨rfl,rfl⟩ | opposition
  · exact KRKTwelveCentralStrip.row_four_clear row
  · exact KRKTwelveCentralUpper.protected_clear
  · exact opposition_clear opposition

theorem kernel_twelve_iff {q : Position} {σ : Colour} {sk rs : Square}
    (material : IsKRK q σ sk rs (1,3)) (turn : q.turn = σ.opp) (far : 2 ≤ dInf sk (1,3)) :
    MateWithin σ 12 q ↔ Region sk rs := by
  have notMate : ¬MatedK q := by
    intro mate
    have zero := KRKEdgeDepth.terminal_depth_zero ((KRKMateGeometry.kernel_mate_iff material turn far).mp mate)
    change 1 = 0 at zero
    contradiction
  exact (KRKTwelveGeometry.kernel_twelve_iff material turn notMate).trans ⟨necessary material.1 far,sufficient⟩

theorem kernel_exact_twelve {q : Position} {σ : Colour} {sk rs : Square}
    (material : IsKRK q σ sk rs (1,3)) (turn : q.turn = σ.opp) (far : 2 ≤ dInf sk (1,3)) :
    (MateWithin σ 12 q ∧ ¬MateWithin σ 11 q) ↔ Region sk rs := by
  have notTen := KRKTenCentralStrip.middle_kernel_no_ten material turn
    (Or.inl ⟨Or.inl rfl,by decide,by decide⟩) far
  exact ⟨fun h => (kernel_twelve_iff material turn far).mp h.1,fun region =>
    ⟨(kernel_twelve_iff material turn far).mpr region,
      fun eleven => notTen (KRKTenGeometry.weak_eleven_ten material turn eleven)⟩⟩

theorem framed_clear_iff (g : Frame) {sk rs wk : Square} (target : g.f wk = ((1 : Fin 8),3))
    (apart : sk ≠ rs) (far : 2 ≤ dInf sk wk) :
    KRKTwelveGeometry.Clear sk rs wk ↔ Region (g.f sk) (g.f rs) := by
  constructor
  · intro clear
    have mapped := KRKTwelveGeometry.frame_map g apart clear
    have mappedFar : 2 ≤ dInf (g.f sk) (g.f wk) := by rw [g.distance]; exact far
    rw [target] at mapped mappedFar
    exact necessary (g.ne_iff.mpr apart) mappedFar mapped
  · intro region
    have mapped := sufficient region
    have shaped : KRKTwelveGeometry.Clear (g.f sk) (g.f rs) (g.f wk) := by rwa [target]
    have back := KRKTwelveGeometry.frame_map g.inverse (g.ne_iff.mpr apart) shaped
    simpa only [Frame.inverse,g.left_inv] using back

end EndgameChess.Rules.KRKTwelveCentralExact
