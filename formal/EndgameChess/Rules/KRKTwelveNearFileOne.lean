import EndgameChess.Rules.KRKTwelveNearFileEntries

namespace EndgameChess.Rules.KRKTwelveNearFileOne
open EndgameChess.KK KRKNativeFrame
set_option maxHeartbeats 500000
set_option linter.unusedSimpArgs false

def Region (sk rs : Square) : Prop :=
  sk.1.val = 3 ∧ sk.2.val = 2 ∧ rs.1.val = 1 ∧ (rs.2.val = 0 ∨ 4 ≤ rs.2.val)

theorem high_no_clear {sk rs : Square} (apart : sk ≠ rs) (sx : sk.1.val = 3)
    (sy : sk.2.val = 3) (rx : rs.1.val = 1) : ¬KRKTwelveGeometry.Clear sk rs (1,2) := by
  intro clear
  have height : rs.2.val = 0 ∨ 4 ≤ rs.2.val := by
    have safe := clear.1
    dsimp [SafeRook,dInf,absDiff] at safe
    omega
  have guard : KRKCornerWeakBand.Guard sk rs (1,2) (2,1) := by
    simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,sx,sy,rx]
    simp <;> omega
  let g := Frame.ofSym symSwap
  have notKing : sk ≠ ((2 : Fin 8),1) := ne_of_dInf_pos (by have h := guard.2.2.1; omega)
  have mapped := KRKElevenGeometry.frame_map g apart notKing guard.2.1.symm guard.2.2.1 guard.2.2.2
    (clear.2.2 _ guard)
  have evaluated := (KRKElevenNearStrip.clear_iff (g.ne_iff.mpr apart) (g.ne_iff.mpr guard.2.1.symm)).mp mapped
  rcases evaluated with ⟨i,distance,_,shape⟩ | ⟨i,equal,condition⟩
  · cases i <;> dsimp [KRKElevenNearStrip.king,KRKElevenNearStrip.RookRegion,g,Frame.ofSym,symSwap,dInf,absDiff] at distance shape <;> omega
  · cases i <;> simp only [KRKElevenNearStrip.king,square_eq_iff,Fin.ext_iff] at equal <;>
      dsimp [g,Frame.ofSym,symSwap] at equal <;> omega

theorem necessary {sk rs : Square} (apart : sk ≠ rs) (sx : sk.1.val = 3)
    (sy : sk.2.val = 2 ∨ sk.2.val = 3) (rx : rs.1.val = 1)
    (clear : KRKTwelveGeometry.Clear sk rs (1,2)) : Region sk rs := by
  have low : sk.2.val = 2 := by
    rcases sy with two | three
    · exact two
    · exact False.elim (high_no_clear apart sx three rx clear)
  have safe := clear.1
  dsimp [SafeRook,dInf,absDiff] at safe
  exact ⟨sx,low,rx,by omega⟩

theorem sufficient {sk rs : Square} (region : Region sk rs) : KRKTwelveGeometry.Clear sk rs (1,2) := by
  obtain ⟨sx,sy,rx,height⟩ := region
  have distinct : sk ≠ rs := by simp [ne_iff_coords,sx,rx]
  have safe : SafeRook sk rs (1,2) := by dsimp [SafeRook,dInf,absDiff]; omega
  have kingEq : sk = ((3 : Fin 8),2) := Prod.ext (Fin.ext sx) (Fin.ext sy)
  subst sk
  refine ⟨safe,⟨((0 : Fin 8),2),?_⟩,?_⟩
  · simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,rx]
    simp <;> omega
  · intro t guard
    have targets : t = ((0 : Fin 8),1) ∨ t = ((0 : Fin 8),2) ∨ t = ((0 : Fin 8),3) := by
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords,rx] at guard
      simp only [square_eq_iff,Fin.ext_iff]
      dsimp at guard ⊢
      omega
    have edge : ∀ {j : Fin 8}, j = 1 ∨ j = 2 ∨ j = 3 →
        KRKCornerWeakBand.Guard ((3 : Fin 8),2) rs (1,2) (0,j) →
        KRKElevenGeometry.Clear ((3 : Fin 8),2) rs (0,j) := by
      intro j choice guard
      let g := Frame.ofSym symSwap
      have mapped : KRKElevenGeometry.Clear (g.f ((3 : Fin 8),2)) (g.f rs) (g.f ((0 : Fin 8),j)) := by
        rcases choice with rfl | rfl | rfl
        · exact KRKTwelveNearFileEntries.low_eleven rx (Or.inl rfl)
        · exact KRKTwelveNearFileEntries.low_eleven rx (Or.inr rfl)
        · exact KRKTwelveNearFileEntries.middle_eleven rx (by change rs.2.val ≠ 3; omega)
      have back := KRKElevenGeometry.frame_map g.inverse (g.ne_iff.mpr distinct)
        (g.ne_iff.mpr (ne_of_dInf_pos (by have h := guard.2.2.1; omega)))
        (g.ne_iff.mpr guard.2.1.symm) (by rw [g.distance]; exact guard.2.2.1)
        (fun h => guard.2.2.2 ((g.sees _ _ _ _).mp h)) mapped
      simpa only [Frame.inverse,g.left_inv] using back
    rcases targets with rfl | rfl | rfl
    · exact edge (Or.inl rfl) guard
    · exact edge (Or.inr (Or.inl rfl)) guard
    · exact edge (Or.inr (Or.inr rfl)) guard

theorem kernel_twelve_iff {q : Position} {σ : Colour} {sk rs : Square}
    (material : IsKRK q σ sk rs (1,2)) (turn : q.turn = σ.opp) (far : 2 ≤ dInf sk (1,2))
    (sx : sk.1.val = 3) (sy : sk.2.val = 2 ∨ sk.2.val = 3) (rx : rs.1.val = 1) :
    MateWithin σ 12 q ↔ Region sk rs := by
  have notMate : ¬MatedK q := by
    intro mate
    have zero := KRKEdgeDepth.terminal_depth_zero ((KRKMateGeometry.kernel_mate_iff material turn far).mp mate)
    change 1 = 0 at zero
    contradiction
  exact (KRKTwelveGeometry.kernel_twelve_iff material turn notMate).trans ⟨necessary material.1 sx sy rx,sufficient⟩

theorem kernel_exact_twelve {q : Position} {σ : Colour} {sk rs : Square}
    (material : IsKRK q σ sk rs (1,2)) (turn : q.turn = σ.opp) (far : 2 ≤ dInf sk (1,2))
    (sx : sk.1.val = 3) (sy : sk.2.val = 2 ∨ sk.2.val = 3) (rx : rs.1.val = 1) :
    (MateWithin σ 12 q ∧ ¬MateWithin σ 11 q) ↔
      sk.1.val = 3 ∧ sk.2.val = 2 ∧ rs.1.val = 1 ∧ (rs.2.val = 0 ∨ 6 ≤ rs.2.val) := by
  constructor
  · rintro ⟨twelve,notEleven⟩
    have region := (kernel_twelve_iff material turn far sx sy rx).mp twelve
    have notTen : ¬MateWithin σ 10 q := fun ten => notEleven (mateWithin_mono ten (by decide))
    have notMiddle : ¬(rs.2.val = 4 ∨ rs.2.val = 5) := by
      intro heights
      have tenRegion : KRKTenNearStrip.Region sk rs := Or.inr (Or.inr (Or.inl ⟨sx,region.2.1,rx,heights⟩))
      exact notTen ((KRKTenNearStrip.kernel_ten_iff material turn far).mpr tenRegion)
    exact ⟨sx,region.2.1,rx,by have bounds := region.2.2.2; omega⟩
  · rintro ⟨sx,sy,rx,height⟩
    refine ⟨(kernel_twelve_iff material turn far sx (Or.inl sy) rx).mpr ⟨sx,sy,rx,by omega⟩,?_⟩
    intro eleven
    have ten := KRKTenGeometry.weak_eleven_ten material turn eleven
    have shape := (KRKTenNearStrip.kernel_ten_iff material turn far).mp ten
    dsimp [KRKTenNearStrip.Region,KRKEightStrip.Region,KRKTenNearStrip.RowThree,
      KRKTenNearStrip.FileOne,KRKTenNearStrip.Upper] at shape
    omega

end EndgameChess.Rules.KRKTwelveNearFileOne
