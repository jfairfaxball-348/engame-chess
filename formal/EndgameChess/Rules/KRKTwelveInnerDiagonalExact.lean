import EndgameChess.Rules.KRKTwelveInnerDiagonal

namespace EndgameChess.Rules.KRKTwelveInnerDiagonalExact
open EndgameChess.KK KRKNativeFrame KRKFourPlyEscape
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false

def Region (rs : Square) : Prop :=
  rs = ((2 : Fin 8),2) ∨ rs = ((3 : Fin 8),2) ∨ rs = ((2 : Fin 8),3)

private theorem near_constraint {rs : Square} (apart : ((3 : Fin 8),3) ≠ rs)
    (clear : KRKTwelveGeometry.Clear (3,3) rs (1,1)) :
    rs.1.val = 1 ∨ rs.2.val = 2 ∨ (rs.2.val = 3 ∧ 2 ≤ rs.1.val) := by
  by_cases guard : KRKCornerWeakBand.Guard ((3 : Fin 8),3) rs (1,1) (1,2)
  · have evaluated := (KRKElevenNearStrip.clear_iff apart guard.2.1.symm).mp (clear.2.2 _ guard)
    rcases evaluated with ⟨i,distance,_,shape⟩ | ⟨i,equal,_⟩
    · cases i <;> dsimp [KRKElevenNearStrip.king,KRKElevenNearStrip.RookRegion,dInf,absDiff] at distance shape <;> omega
    · cases i <;> simp only [KRKElevenNearStrip.king,square_eq_iff,Fin.ext_iff] at equal <;> dsimp at equal <;> omega
  · by_cases line : RookLine rs ((1 : Fin 8),2)
    · have shape := line.2
      dsimp at shape
      omega
    · have notRook : ((1 : Fin 8),2) ≠ rs := by
        intro equal
        have safe := clear.1
        rw [←equal] at safe
        dsimp [SafeRook,dInf,absDiff] at safe
        omega
      exact False.elim (guard ⟨by decide,notRook,by decide,fun sees => line sees.1⟩)

theorem necessary {rs : Square} (apart : ((3 : Fin 8),3) ≠ rs)
    (clear : KRKTwelveGeometry.Clear (3,3) rs (1,1)) : Region rs := by
  have horizontal := near_constraint apart clear
  have mapped := KRKTwelveGeometry.frame_map (Frame.ofSym symSwap) apart clear
  have vertical := near_constraint ((Frame.ofSym symSwap).ne_iff.mpr apart) mapped
  have safe := clear.1
  simp only [ne_iff_coords] at apart
  dsimp [SafeRook,dInf,absDiff] at safe
  dsimp [Frame.ofSym,symSwap] at vertical
  dsimp [Region]
  simp only [square_eq_iff,Fin.ext_iff]
  dsimp at apart ⊢
  omega

private theorem bottom_eleven {rs : Square} (choice : rs = ((3 : Fin 8),2) ∨ rs = ((2 : Fin 8),3))
    {j : Fin 8} (edge : j = 0 ∨ j = 1 ∨ j = 2) : KRKElevenGeometry.Clear (3,3) rs (j,0) := by
  have apart : ((2 : Fin 8),2) ≠ rs := by rcases choice with rfl | rfl <;> decide
  have notWeak : rs ≠ (j,0) := by rcases choice with rfl | rfl <;> simp
  have far : 2 ≤ dInf ((2 : Fin 8),2) (j,0) := by dsimp [dInf,absDiff]; omega
  have old : KRKEightGlobal.Region (2,2) rs (j,0) := by
    rcases edge with rfl | rfl | rfl
    · apply KRKEightDiagonalEntries.corner_region
      rcases choice with rfl | rfl <;> decide
    · apply KRKEightDiagonalEntries.near_region apart
      rcases choice with rfl | rfl <;> exact Or.inl (by decide)
    · apply KRKEightDiagonalEntries.second_region
      rcases choice with rfl | rfl
      · exact Or.inr (Or.inl ⟨rfl,by decide⟩)
      · exact Or.inl (by decide)
  have ten := KRKTwelveNearFileEntries.eight_region_subset apart notWeak far old
  exact KRKElevenGeometry.king_step_clear (ns := ((2 : Fin 8),2)) (by decide) apart far ten

private theorem row_clear : KRKTwelveGeometry.Clear ((3 : Fin 8),3) ((3 : Fin 8),2) (1,1) := by
  refine ⟨Or.inr (by decide),⟨((0 : Fin 8),0),?_⟩,?_⟩
  · dsimp [KRKCornerWeakBand.Guard,RookSees,RookLine,OnSeg]
    decide
  · intro t guard
    have targets : t = ((0 : Fin 8),0) ∨ t = ((1 : Fin 8),0) ∨ t = ((2 : Fin 8),0) ∨
        t = ((0 : Fin 8),1) ∨ t = ((2 : Fin 8),1) := by
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords] at guard
      simp only [square_eq_iff,Fin.ext_iff]
      dsimp at guard ⊢
      omega
    have west : ∀ {j : Fin 8}, j = 0 ∨ j = 1 → KRKElevenGeometry.Clear (3,3) (3,2) (0,j) := by
      intro j edge
      let g := Frame.ofSym symSwap
      have source := bottom_eleven (Or.inr rfl) (j := j) (by rcases edge with rfl | rfl <;> simp)
      have back := KRKElevenGeometry.frame_map g (by decide) (by simp)
        (by simp) (by dsimp [dInf,absDiff]; omega)
        (by dsimp [RookSees,RookLine,OnSeg]; omega) source
      simpa only [g,Frame.ofSym,symSwap] using back
    rcases targets with rfl | rfl | rfl | rfl | rfl
    · exact bottom_eleven (Or.inl rfl) (Or.inl rfl)
    · exact bottom_eleven (Or.inl rfl) (Or.inr (Or.inl rfl))
    · exact bottom_eleven (Or.inl rfl) (Or.inr (Or.inr rfl))
    · exact west (Or.inr rfl)
    · let g := Frame.ofSym symSwap
      have entry : KRKElevenGeometry.Clear (3,3) (2,3) (1,2) :=
        (KRKElevenNearStrip.clear_iff (by decide) (by decide)).mpr
          (Or.inl ⟨.side,by decide,by decide,Or.inl ⟨rfl,by decide⟩⟩)
      have back := KRKElevenGeometry.frame_map g (by decide) (by decide) (by decide) (by decide)
        (by dsimp [RookSees,RookLine,OnSeg]; decide) entry
      simpa only [g,Frame.ofSym,symSwap] using back

theorem sufficient {rs : Square} (region : Region rs) : KRKTwelveGeometry.Clear (3,3) rs (1,1) := by
  rcases region with rfl | rfl | rfl
  · exact KRKTwelveInnerDiagonal.clear
  · exact row_clear
  · have mapped := KRKTwelveGeometry.frame_map (Frame.ofSym symSwap) (by decide) row_clear
    simpa only [Frame.ofSym,symSwap] using mapped

theorem clear_iff {rs : Square} (apart : ((3 : Fin 8),3) ≠ rs) :
    KRKTwelveGeometry.Clear (3,3) rs (1,1) ↔ Region rs := ⟨necessary apart,sufficient⟩

theorem kernel_twelve_iff {q : Position} {σ : Colour} {rs : Square}
    (material : IsKRK q σ (3,3) rs (1,1)) (turn : q.turn = σ.opp) : MateWithin σ 12 q ↔ Region rs := by
  have notMate : ¬MatedK q := by
    intro mate
    have zero := KRKEdgeDepth.terminal_depth_zero ((KRKMateGeometry.kernel_mate_iff material turn (by decide)).mp mate)
    change 1 = 0 at zero
    contradiction
  exact (KRKTwelveGeometry.kernel_twelve_iff material turn notMate).trans (clear_iff material.1)

theorem kernel_exact_twelve {q : Position} {σ : Colour} {rs : Square}
    (material : IsKRK q σ (3,3) rs (1,1)) (turn : q.turn = σ.opp) :
    (MateWithin σ 12 q ∧ ¬MateWithin σ 11 q) ↔ Region rs := by
  constructor
  · exact fun h => (kernel_twelve_iff material turn).mp h.1
  · intro region
    refine ⟨(kernel_twelve_iff material turn).mpr region,?_⟩
    intro eleven
    have ten := KRKTenGeometry.weak_eleven_ten material turn eleven
    have old := (KRKTenInner.kernel_ten_iff material turn (by decide)).mp ten
    dsimp [KRKTenInner.Region,KRKTenInner.Horizontal,KRKEightInner.Horizontal,
      KRKTenInner.SideExtra,KRKTenInner.HighExtra,symSwap] at old
    omega

end EndgameChess.Rules.KRKTwelveInnerDiagonalExact
