import EndgameChess.Rules.KRKTwelveInnerUpperEntries

namespace EndgameChess.Rules.KRKTwelveInnerUpperFour
open EndgameChess.KK KRKNativeFrame
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false

def Region (sk rs : Square) : Prop := sk.2.val = 4 ∧ rs.1.val = 2 ∧
  ((sk.1.val ≤ 1 ∧ 3 ≤ rs.2.val) ∨ (sk.1.val = 2 ∧ rs.2.val = 3))

theorem necessary {sk rs : Square} (apart : sk ≠ rs) (sx : sk.1.val ≤ 2)
    (sy : sk.2.val = 4) (rx : rs.1.val = 2) (clear : KRKTwelveGeometry.Clear sk rs (1,1)) : Region sk rs := by
  have safe := clear.1
  have high : 3 ≤ rs.2.val := by
    have cover := KRKFourPlyEscape.covered_box
      (KRKTwelveSecondCorner.bad_neighbour_covered apart clear (t := (2,2)) (by decide) (Or.inl (by decide)))
    dsimp [SafeRook,dInf,absDiff] at safe
    dsimp at cover
    omega
  have below : sk.1.val = 2 → rs.2.val < 4 := by
    intro two
    have bound := KRKTwelveInner.same_file_rook_below apart two (Or.inl sy) rx clear
    omega
  exact ⟨sy,rx,by omega⟩

private theorem west_eleven {k h j : Fin 8} (king : k.val ≤ 2) (height : 3 ≤ h.val)
    (allowed : k.val ≤ 1 ∨ h = 3) (choice : j = 1 ∨ j = 2)
    (actual : KRKCornerWeakBand.Guard (k,4) (2,h) (1,1) (0,j)) : KRKElevenGeometry.Clear (k,4) (2,h) (0,j) := by
  let g := Frame.ofSym symSwap
  have source : KRKElevenGeometry.Clear (4,k) (h,2) (j,0) := by
    rcases choice with rfl | rfl
    · exact KRKElevenGeometry.king_step_clear (ns := ((3 : Fin 8),1))
        (by dsimp [dInf,absDiff]; omega) (by simp) (by decide)
        (KRKTwelveInnerUpperEntries.low_near_ten (by omega))
    · apply KRKElevenGeometry.rook_step_clear (nr := ((2 : Fin 8),2))
      · simp only [RookSees,RookLine,OnSeg,ne_iff_coords]
        dsimp
        rcases allowed with low | three
        · simp_all [show ((4 : Fin 8).val) = 4 from rfl] <;> omega
        · rw [three]; simp [show ((4 : Fin 8).val) = 4 from rfl,show ((3 : Fin 8).val) = 3 from rfl]
      · simp
      · decide
      · exact KRKTwelveInnerUpperEntries.second_outer_ten king
  have apart : ((k,4) : Square) ≠ (2,h) := by
    simp only [ne_iff_coords]
    dsimp
    rcases allowed with low | three
    · omega
    · rw [three]; simp [show ((4 : Fin 8).val) = 4 from rfl,show ((3 : Fin 8).val) = 3 from rfl]
  have notKing : ((k,4) : Square) ≠ (0,j) := ne_of_dInf_pos (by have h := actual.2.2.1; omega)
  have mapped := KRKElevenGeometry.frame_map g (g.ne_iff.mpr apart) (g.ne_iff.mpr notKing)
    (g.ne_iff.mpr actual.2.1.symm)
    (by change 2 ≤ dInf (g.f (k,4)) (g.f (0,j)); rw [g.distance]; exact actual.2.2.1)
    (fun h => actual.2.2.2 ((g.sees _ _ _ _).mp h)) source
  simpa only [g,Frame.ofSym,symSwap] using mapped

private theorem slots_clear {k h : Fin 8} (bound : k.val ≤ 2) (height : 3 ≤ h.val)
    (allowed : k.val ≤ 1 ∨ h = 3) : KRKTwelveGeometry.Clear (k,4) (2,h) (1,1) := by
  refine ⟨Or.inl (by dsimp [dInf,absDiff]; omega),⟨((0 : Fin 8),0),?_⟩,?_⟩
  · simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords]
    dsimp
    rcases allowed with low | three
    · omega
    · rw [three]; (try dsimp); omega
  · intro t guard
    have targets : t = ((0 : Fin 8),0) ∨ t = ((1 : Fin 8),0) ∨ t = ((0 : Fin 8),1) ∨
        t = ((0 : Fin 8),2) ∨ t = ((1 : Fin 8),2) := by
      simp only [KRKCornerWeakBand.Guard,dInf,absDiff,RookSees,RookLine,OnSeg,ne_iff_coords] at guard
      simp only [square_eq_iff,Fin.ext_iff]
      dsimp at guard ⊢
      rcases allowed with low | three
      · omega
      · rw [three] at guard; (try dsimp at guard); omega
    rcases targets with rfl | rfl | rfl | rfl | rfl
    · exact KRKElevenGeometry.king_step_clear (ns := ((1 : Fin 8),3))
        (by dsimp [dInf,absDiff]; omega) (by simp) (by decide) (KRKTwelveInnerUpperEntries.upper_corner_ten height)
    · exact KRKElevenGeometry.king_step_clear (ns := ((1 : Fin 8),3))
        (by dsimp [dInf,absDiff]; omega) (by simp) (by decide) (KRKTwelveInnerUpperEntries.upper_near_ten height)
    · exact west_eleven bound height allowed (Or.inl rfl) guard
    · exact west_eleven bound height allowed (Or.inr rfl) guard
    · apply (KRKElevenNearStrip.clear_iff (by simp only [ne_iff_coords]; dsimp; rcases allowed with low | three <;> omega)
        guard.2.1.symm).mpr
      have slots : k = 0 ∨ k = 1 ∨ k = 2 := by simp only [Fin.ext_iff]; (try dsimp); omega
      rcases slots with zero | one | two
      · rw [zero]
        exact Or.inr ⟨.upperZero,rfl,Or.inl rfl⟩
      · rw [one]
        exact Or.inr ⟨.upperOne,rfl,Or.inl rfl⟩
      · rw [two]
        exact Or.inl ⟨.upperOne,by decide,by simp [KRKElevenNearStrip.king],⟨rfl,height⟩⟩

theorem sufficient {sk rs : Square} (region : Region sk rs) : KRKTwelveGeometry.Clear sk rs (1,1) := by
  obtain ⟨sy,rx,choice⟩ := region
  have kingEq : sk = (sk.1,(4 : Fin 8)) := Prod.ext rfl (Fin.ext sy)
  have rookEq : rs = ((2 : Fin 8),rs.2) := Prod.ext (Fin.ext rx) rfl
  rw [kingEq,rookEq]
  apply slots_clear
  · omega
  · omega
  · rcases choice with low | two
    · exact Or.inl low.1
    · exact Or.inr (Fin.ext two.2)

theorem clear_iff {sk rs : Square} (apart : sk ≠ rs) (sx : sk.1.val ≤ 2)
    (sy : sk.2.val = 4) (rx : rs.1.val = 2) :
    KRKTwelveGeometry.Clear sk rs (1,1) ↔ Region sk rs := ⟨necessary apart sx sy rx,sufficient⟩

theorem kernel_exact_twelve {q : Position} {σ : Colour} {sk rs : Square}
    (material : IsKRK q σ sk rs (1,1)) (turn : q.turn = σ.opp)
    (sx : sk.1.val ≤ 2) (sy : sk.2.val = 4) (rx : rs.1.val = 2) :
    (MateWithin σ 12 q ∧ ¬MateWithin σ 11 q) ↔ Region sk rs := by
  have far : 2 ≤ dInf sk (1,1) := by dsimp [dInf,absDiff]; omega
  have notMate : ¬MatedK q := by
    intro mate
    have zero := KRKEdgeDepth.terminal_depth_zero ((KRKMateGeometry.kernel_mate_iff material turn far).mp mate)
    change 1 = 0 at zero
    contradiction
  constructor
  · exact fun h => necessary material.1 sx sy rx ((KRKTwelveGeometry.kernel_twelve_iff material turn notMate).mp h.1)
  · intro region
    refine ⟨(KRKTwelveGeometry.kernel_twelve_iff material turn notMate).mpr (sufficient region),?_⟩
    intro eleven
    have old := (KRKTenInner.kernel_ten_iff material turn far).mp (KRKTenGeometry.weak_eleven_ten material turn eleven)
    dsimp [KRKTenInner.Region,KRKTenInner.Horizontal,KRKEightInner.Horizontal,
      KRKTenInner.SideExtra,KRKTenInner.HighExtra,symSwap] at old
    omega

end EndgameChess.Rules.KRKTwelveInnerUpperFour
