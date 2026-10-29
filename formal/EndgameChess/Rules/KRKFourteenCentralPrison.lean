import EndgameChess.Rules.KRKFourteenCentralEntries

namespace EndgameChess.Rules.KRKFourteenCentralPrison
open EndgameChess.KK KRKNativeFrame KRKFourPlyEscape
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false

def UpperRow (sk rs : Square) : Prop :=
  ((sk.1.val = 3 ∧ sk.2.val = 4) ∨ (sk.2.val = 5 ∧ 1 ≤ sk.1.val ∧ sk.1.val ≤ 3)) ∧
    rs.2.val = 3 ∧ 3 ≤ rs.1.val

def LowOpposition (sk rs : Square) : Prop :=
  sk.1.val = 3 ∧ sk.2.val = 3 ∧ rs.1.val = 1 ∧ (rs.2.val ≤ 2 ∨ 6 ≤ rs.2.val)

def UpperOpposition (sk rs : Square) : Prop :=
  sk.1.val = 3 ∧ sk.2.val = 4 ∧ (rs.1.val = 1 ∨ rs.2.val ≤ 2 ∨ 6 ≤ rs.2.val)

def LegalUpper (sk rs : Square) : Prop := UpperRow sk rs ∨ LowOpposition sk rs ∨ UpperOpposition sk rs

def Prison (sk rs : Square) : Prop := LegalUpper sk rs ∨
  (sk.1.val = 3 ∧ 2 ≤ sk.2.val ∧ sk.2.val ≤ 4 ∧ rs.2.val = 4) ∨
  (sk.1.val = 3 ∧ (sk.2.val = 3 ∨ sk.2.val = 4) ∧ rs.1.val = 1) ∨
  (sk.2.val = 5 ∧ sk.1.val ≤ 3 ∧ rs.1.val = 2)

private theorem blocked_covered {sk rs wk t : Square} (safe : SafeRook sk rs wk) (distance : dInf wk t = 1)
    (blocked : ¬KRKCornerWeakBand.Guard sk rs wk t) : Covered sk rs t := by
  by_cases king : dInf sk t ≤ 1
  · exact Or.inl king
  by_cases line : RookLine rs t
  · exact Or.inr line
  have notRook : t ≠ rs := by
    intro equal
    rcases safe with distant | guarded
    · rw [equal,dInf_comm] at distance; omega
    · rw [equal] at king; omega
  exact False.elim (blocked ⟨distance,notRook,by omega,fun seen => line seen.1⟩)

theorem legal_upper {sk rs : Square} (apart : sk ≠ rs) (far : 2 ≤ dInf sk (1,3))
    (clear : KRKFourteenGeometry.Clear sk rs (1,3)) (guard : KRKCornerWeakBand.Guard sk rs (1,3) (1,4)) :
    LegalUpper sk rs := by
  let g := Frame.ofSym symY
  have mapped := KRKThirteenGeometry.frame_map g apart
    (ne_of_dInf_pos (by have h := guard.2.2.1; omega)) guard.2.1.symm guard.2.2.1 guard.2.2.2 (clear.2.2 _ guard)
  have target : g.f ((1 : Fin 8),4) = ((1 : Fin 8),3) := rfl
  rw [target] at mapped
  have evaluated := (KRKThirteenCentralStrip.clear_iff (g.ne_iff.mpr apart)
    (by simpa only [target] using g.ne_iff.mpr guard.2.1.symm)).mp mapped
  have a := covered_box (KRKFourteenDeep.bad_neighbour_covered clear (t := (2,3)) (by decide) (by decide)
    (by dsimp [KRKTwelveDeepExact.SecondCorner]; decide))
  have b := covered_box (KRKFourteenDeep.bad_neighbour_covered clear (t := (2,4)) (by decide) (by decide)
    (by dsimp [KRKTwelveDeepExact.SecondCorner]; decide))
  have safe := clear.1
  clear clear mapped
  dsimp at a b
  dsimp [SafeRook,dInf,absDiff] at safe far
  rcases evaluated with ⟨i,distance,notRook,region⟩ | ⟨i,equal,condition⟩
  · cases i with
    | row =>
      dsimp [g,Frame.ofSym,symY,KRKThirteenCentralStrip.king,KRKThirteenCentralStrip.RookRegion,dInf,absDiff] at distance region
      have rook : rs.2.val = 3 ∧ 3 ≤ rs.1.val := by omega
      have shape : (sk.1.val = 3 ∧ sk.2.val = 4) ∨ (sk.2.val = 5 ∧ 1 ≤ sk.1.val ∧ sk.1.val ≤ 3) := by omega
      exact Or.inl ⟨shape,rook⟩
    | opposition =>
      dsimp [g,Frame.ofSym,symY,KRKThirteenCentralStrip.king,KRKThirteenCentralStrip.RookRegion,dInf,absDiff] at distance region
      have rook : rs.1.val = 1 ∧ (rs.2.val ≤ 2 ∨ 6 ≤ rs.2.val) := by omega
      have shape : sk.1.val = 3 ∧ (sk.2.val = 3 ∨ sk.2.val = 4) := by omega
      rcases shape.2 with three | four
      · exact Or.inr (Or.inl ⟨shape.1,three,rook⟩)
      · exact Or.inr (Or.inr ⟨shape.1,four,Or.inl rook.1⟩)
    | guarded =>
      dsimp [g,Frame.ofSym,symY,KRKThirteenCentralStrip.king,KRKThirteenCentralStrip.RookRegion,dInf,absDiff] at distance region
      simp only [square_eq_iff,Fin.ext_iff] at region
      dsimp at region
      omega
  · cases i with
    | row =>
      simp only [KRKThirteenCentralStrip.king,square_eq_iff,Fin.ext_iff] at equal
      dsimp [g,Frame.ofSym,symY,KRKThirteenCentralStrip.RookCondition] at equal condition
      have shape : sk.1.val = 3 ∧ sk.2.val = 5 ∧ rs.2.val = 3 ∧ 3 ≤ rs.1.val := by omega
      exact Or.inl ⟨Or.inr ⟨shape.2.1,by omega,by omega⟩,shape.2.2⟩
    | opposition =>
      simp only [KRKThirteenCentralStrip.king,square_eq_iff,Fin.ext_iff] at equal
      dsimp [g,Frame.ofSym,symY,KRKThirteenCentralStrip.RookCondition] at equal condition
      have shape : sk.1.val = 3 ∧ sk.2.val = 4 ∧ (rs.1.val = 1 ∨ rs.2.val ≤ 2 ∨ 6 ≤ rs.2.val) := by omega
      exact Or.inr (Or.inr shape)
    | guarded =>
      simp only [KRKThirteenCentralStrip.king,square_eq_iff,Fin.ext_iff] at equal
      dsimp [g,Frame.ofSym,symY] at equal
      omega

theorem prison {sk rs : Square} (apart : sk ≠ rs) (far : 2 ≤ dInf sk (1,3))
    (clear : KRKFourteenGeometry.Clear sk rs (1,3)) : Prison sk rs := by
  by_cases upper : KRKCornerWeakBand.Guard sk rs (1,3) (1,4)
  · exact Or.inl (legal_upper apart far clear upper)
  have a := covered_box (KRKFourteenDeep.bad_neighbour_covered clear (t := (2,3)) (by decide) (by decide)
    (by dsimp [KRKTwelveDeepExact.SecondCorner]; decide))
  have b := covered_box (KRKFourteenDeep.bad_neighbour_covered clear (t := (2,4)) (by decide) (by decide)
    (by dsimp [KRKTwelveDeepExact.SecondCorner]; decide))
  have c := covered_box (blocked_covered clear.1 (by decide) upper)
  have safe := clear.1
  clear clear upper
  dsimp at a b c
  dsimp [SafeRook,dInf,absDiff] at safe far
  rcases c with king | file | row
  · have shape : sk.2.val = 5 ∧ sk.1.val ≤ 2 ∧
        (rs.1.val = 2 ∨ (1 ≤ sk.1.val ∧ rs.2.val = 3 ∧ 3 ≤ rs.1.val)) := by omega
    rcases shape.2.2 with file | rook
    · exact Or.inr (Or.inr (Or.inr ⟨shape.1,by omega,file⟩))
    · exact Or.inl (Or.inl ⟨Or.inr ⟨shape.1,rook.1,by omega⟩,rook.2⟩)
  · have shape : sk.1.val = 3 ∧ (sk.2.val = 3 ∨ sk.2.val = 4) := by omega
    exact Or.inr (Or.inr (Or.inl ⟨shape.1,shape.2,file⟩))
  · by_cases file : rs.1.val = 2
    · have shape : (sk.1.val = 3 ∧ 2 ≤ sk.2.val ∧ sk.2.val ≤ 4) ∨
          (sk.2.val = 5 ∧ sk.1.val ≤ 3) := by omega
      rcases shape with low | high
      · exact Or.inr (Or.inl ⟨low.1,low.2.1,low.2.2,row⟩)
      · exact Or.inr (Or.inr (Or.inr ⟨high.1,high.2,file⟩))
    · have shape : sk.1.val = 3 ∧ 2 ≤ sk.2.val ∧ sk.2.val ≤ 4 := by omega
      exact Or.inr (Or.inl ⟨shape.1,shape.2.1,shape.2.2,row⟩)

end EndgameChess.Rules.KRKFourteenCentralPrison
