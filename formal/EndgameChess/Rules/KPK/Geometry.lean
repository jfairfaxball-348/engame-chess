import EndgameChess.Rules.KPK.Moves

/-! A general geometric boundary: an unpromoted KPK position cannot be mate.
This says nothing about a subsequent promotion or forced winning play. -/
namespace EndgameChess.Rules.KPK
open EndgameChess.KK

/-- A checking pawn attacks no orthogonal neighbour of the checked king. -/
theorem pawn_not_orth {σ : Colour} {ps wk t : Square}
    (check : PawnSees σ ps wk)
    (orth : absDiff wk.1.val t.1.val + absDiff wk.2.val t.2.val = 1) :
    ¬ PawnSees σ ps t := by
  intro attack
  cases σ <;> simp only [PawnSees, dy, dx, forward, absDiff] at check attack orth <;> omega

theorem pawn_ne_orth {σ : Colour} {ps wk t : Square}
    (check : PawnSees σ ps wk)
    (orth : absDiff wk.1.val t.1.val + absDiff wk.2.val t.2.val = 1) : t ≠ ps := by
  intro e
  cases σ <;> simp only [PawnSees, dy, dx, forward, absDiff, e] at check orth <;> omega

/-- One of two orthogonal neighbours escapes both the strong king and the pawn. -/
theorem escape_square {σ : Colour} {sk ps wk : Square}
    (far : 2 ≤ dInf sk wk) (check : PawnSees σ ps wk) :
    ∃ t, dInf wk t = 1 ∧ 2 ≤ dInf sk t ∧ t ≠ ps ∧ ¬ PawnSees σ ps t := by
  obtain ⟨a, ha⟩ := exists_adj wk.1
  obtain ⟨b, hb⟩ := exists_adj wk.2
  let h : Square := (a, wk.2)
  let v : Square := (wk.1, b)
  have ho : absDiff wk.1.val h.1.val + absDiff wk.2.val h.2.val = 1 := by
    simp only [h, absDiff] at ha ⊢; omega
  have vo : absDiff wk.1.val v.1.val + absDiff wk.2.val v.2.val = 1 := by
    simp only [v, absDiff] at hb ⊢; omega
  have hd : dInf wk h = 1 := by simp only [h, dInf, absDiff] at ha ⊢; omega
  have vd : dInf wk v = 1 := by simp only [v, dInf, absDiff] at hb ⊢; omega
  by_cases hf : 2 ≤ dInf sk h
  · exact ⟨h, hd, hf, pawn_ne_orth check ho, pawn_not_orth check ho⟩
  · refine ⟨v, vd, ?_, pawn_ne_orth check vo, pawn_not_orth check vo⟩
    simp only [h, v, dInf, absDiff] at hf far ha hb ⊢
    omega

theorem checked_weak_has_move {q : Position} {σ : Colour} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (ht : q.turn = σ.opp)
    (far : 2 ≤ dInf sk wk) (check : inCheck q σ.opp = true) :
    ∃ r, Legal q r := by
  have sees : PawnSees σ ps wk := by
    rcases (weak_check h).mp check with adjacent | sees
    · omega
    · exact sees
  obtain ⟨t, step, safe, notPawn, notAttack⟩ := escape_square far sees
  obtain ⟨r, legal, _⟩ := weak_move h ht step notPawn safe notAttack
  exact ⟨r, legal⟩

/-- Neither side can already be mated in exact KPK with separated kings. -/
theorem not_mated {q : Position} {σ : Colour} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (far : 2 ≤ dInf sk wk) : ¬ MatedK q := by
  rintro ⟨check, noMoves⟩
  rcases colour_cases σ q.turn with turn | turn
  · rw [turn, strong_not_check h far] at check
    cases check
  · exact noMoves (checked_weak_has_move h turn far (by simpa only [turn] using check))

end EndgameChess.Rules.KPK
