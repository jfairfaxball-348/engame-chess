import EndgameChess.Rules.KQK.Moves

namespace EndgameChess.Rules.KQK
open EndgameChess.KK

theorem between_near {s t : Square} (hd : dInf s t = 1) (r : Square) :
    isBetween s r t = false := by
  cases he : isBetween s r t
  · rfl
  · have hh := he
    simp only [isBetween,Bool.and_eq_true,bne_iff_ne,ne_eq,beq_iff_eq] at hh
    have h0 : dInf s r ≠ 0 := fun h => hh.1.1.1 (dInf_eq_zero_iff.mp h).symm
    have h1 : dInf r t ≠ 0 := fun h => hh.1.1.2 (dInf_eq_zero_iff.mp h)
    omega

/-- Every adjacent square is on a clear queen ray; other pieces cannot intervene. -/
theorem near_sees {s t a b : Square} (hd : dInf s t = 1) : QueenSees s t a b := by
  refine ⟨?_,between_near hd a,between_near hd b⟩
  by_cases hl : s.1.val = t.1.val ∨ s.2.val = t.2.val
  · exact Or.inr ⟨by simp only [dInf,absDiff] at hd; omega,hl⟩
  · left
    rw [diagGeom_iff_onDiag]
    refine ⟨ne_of_dInf_pos (by omega),?_⟩
    simp only [dInf,absDiff] at hd ⊢
    omega

theorem not_sees_of_not_line {qs t a b : Square}
    (hx : qs.1.val ≠ t.1.val) (hy : qs.2.val ≠ t.2.val)
    (hd : absDiff qs.1.val t.1.val ≠ absDiff qs.2.val t.2.val) :
    ¬ QueenSees qs t a b := by
  rintro ⟨hl,_,_⟩
  rcases hl with diag | line
  · exact hd ((diagGeom_iff_onDiag.mp diag).2)
  · rcases line.2 with h | h
    · exact hx h
    · exact hy h

/-- A protected queen immediately below the enemy edge king is checkmate.
This is a finishing configuration, not an exact-distance classification. -/
theorem edge_mated {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ.opp)
    (hw : wk.2.val = 7) (hx : qs.1.val = wk.1.val) (hy : qs.2.val = 6)
    (hp : dInf sk qs = 1) : MatedK q := by
  constructor
  · rw [ht,weak_check hq]
    right; apply near_sees
    simp only [dInf,absDiff]; omega
  · rintro ⟨r,hl⟩
    obtain ⟨t,hm,_,hd,hfar,hn⟩ := safe_reply hq ht (Or.inr hp) hl
    have hqt : dInf qs t ≤ 1 := by
      simp only [dInf,absDiff] at hd ⊢
      have bound := t.2.isLt
      omega
    have hqt0 : dInf qs t ≠ 0 := fun h => hm.2.2.1 (dInf_eq_zero_iff.mp h)
    exact hn (near_sees (by omega))

end EndgameChess.Rules.KQK
