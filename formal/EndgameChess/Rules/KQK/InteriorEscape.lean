import EndgameChess.Rules.KQK.Geometry

namespace EndgameChess.Rules.KQK
open EndgameChess.KK
set_option maxHeartbeats 4000000

/-- The four infinite queen lines, ignoring blockers. -/
def QueenRay (s t : Square) : Prop :=
  s.1.val = t.1.val ∨ s.2.val = t.2.val ∨
    s.1.val+s.2.val = t.1.val+t.2.val ∨
    s.1.val+t.2.val = t.1.val+s.2.val

theorem sees_ray {s t a b : Square} (h : QueenSees s t a b) : QueenRay s t := by
  rcases h.1 with diag | line
  · have hd := (diagGeom_iff_onDiag.mp diag).2
    simp only [QueenRay,absDiff] at hd ⊢; omega
  · rcases line.2 with hx | hy
    · exact Or.inl hx
    · exact Or.inr (Or.inl hy)

/-- A queen and a separated king cannot cover every neighbour of an
interior square when the queen is at distance at least two.
The proof is coordinate geometry on the eight local directions, not a
classification or enumeration of board positions. -/
theorem interior_escape_geometry {sk qs wk : Square}
    (hk : 2 ≤ dInf sk wk) (hq : 2 ≤ dInf qs wk)
    (hx0 : 1 ≤ wk.1.val) (hx7 : wk.1.val ≤ 6)
    (hy0 : 1 ≤ wk.2.val) (hy7 : wk.2.val ≤ 6) :
    ∃ t : Square, dInf wk t = 1 ∧ 2 ≤ dInf sk t ∧ ¬ QueenRay qs t := by
  classical
  by_cases escape : ∃ t : Square, dInf wk t = 1 ∧ 2 ≤ dInf sk t ∧ ¬ QueenRay qs t
  · exact escape
  apply False.elim
  have cover (t : Square) (hd : dInf wk t = 1) :
      dInf sk t ≤ 1 ∨ QueenRay qs t := by
    by_cases king : 2 ≤ dInf sk t
    · by_cases queen : QueenRay qs t
      · exact Or.inr queen
      · exact False.elim (escape ⟨t,hd,king,queen⟩)
    · exact Or.inl (by omega)
  let xm : Fin 8 := ⟨wk.1.val-1,by omega⟩
  let xp : Fin 8 := ⟨wk.1.val+1,by omega⟩
  let ym : Fin 8 := ⟨wk.2.val-1,by omega⟩
  let yp : Fin 8 := ⟨wk.2.val+1,by omega⟩
  have a := cover (xm,ym) (by simp only [dInf,absDiff,xm,ym]; omega)
  have b := cover (xm,wk.2) (by simp only [dInf,absDiff,xm]; omega)
  have c := cover (xm,yp) (by simp only [dInf,absDiff,xm,yp]; omega)
  have d := cover (wk.1,ym) (by simp only [dInf,absDiff,ym]; omega)
  have e := cover (wk.1,yp) (by simp only [dInf,absDiff,yp]; omega)
  have f := cover (xp,ym) (by simp only [dInf,absDiff,xp,ym]; omega)
  have g := cover (xp,wk.2) (by simp only [dInf,absDiff,xp]; omega)
  have h := cover (xp,yp) (by simp only [dInf,absDiff,xp,yp]; omega)
  have directions : sk.1.val+2 ≤ wk.1.val ∨ wk.1.val+2 ≤ sk.1.val ∨
      sk.2.val+2 ≤ wk.2.val ∨ wk.2.val+2 ≤ sk.2.val := by
    simp only [dInf,absDiff] at hk; omega
  rcases directions with left | right | below | above
  · have rd := d.resolve_left (by simp only [dInf,absDiff,ym]; omega)
    have re := e.resolve_left (by simp only [dInf,absDiff,yp]; omega)
    have rf := f.resolve_left (by simp only [dInf,absDiff,xp,ym]; omega)
    have rg := g.resolve_left (by simp only [dInf,absDiff,xp]; omega)
    have rh := h.resolve_left (by simp only [dInf,absDiff,xp,yp]; omega)
    clear a b c d e f g h cover hk escape left
    simp only [dInf,absDiff,QueenRay,xp,ym,yp] at hq rd re rf rg rh
    clear xm xp ym yp sk
    omega
  · have ra := a.resolve_left (by simp only [dInf,absDiff,xm,ym]; omega)
    have rb := b.resolve_left (by simp only [dInf,absDiff,xm]; omega)
    have rc := c.resolve_left (by simp only [dInf,absDiff,xm,yp]; omega)
    have rd := d.resolve_left (by simp only [dInf,absDiff,ym]; omega)
    have re := e.resolve_left (by simp only [dInf,absDiff,yp]; omega)
    clear a b c d e f g h cover hk escape right
    simp only [dInf,absDiff,QueenRay,xm,ym,yp] at hq ra rb rc rd re
    clear xm xp ym yp sk
    omega
  · have rb := b.resolve_left (by simp only [dInf,absDiff,xm]; omega)
    have rg := g.resolve_left (by simp only [dInf,absDiff,xp]; omega)
    have rc := c.resolve_left (by simp only [dInf,absDiff,xm,yp]; omega)
    have re := e.resolve_left (by simp only [dInf,absDiff,yp]; omega)
    have rh := h.resolve_left (by simp only [dInf,absDiff,xp,yp]; omega)
    clear a b c d e f g h cover hk escape below
    simp only [dInf,absDiff,QueenRay,xm,xp,yp] at hq rb rg rc re rh
    clear xm xp ym yp sk
    omega
  · have ra := a.resolve_left (by simp only [dInf,absDiff,xm,ym]; omega)
    have rb := b.resolve_left (by simp only [dInf,absDiff,xm]; omega)
    have rd := d.resolve_left (by simp only [dInf,absDiff,ym]; omega)
    have rf := f.resolve_left (by simp only [dInf,absDiff,xp,ym]; omega)
    have rg := g.resolve_left (by simp only [dInf,absDiff,xp]; omega)
    clear a b c d e f g h cover hk escape above
    simp only [dInf,absDiff,QueenRay,xm,xp,ym] at hq ra rb rd rf rg
    clear xm xp ym yp sk
    omega

theorem interior_reply_exists {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ.opp)
    (hfar : 2 ≤ dInf sk wk) (hc : inCheck q σ.opp = false)
    (hx0 : 1 ≤ wk.1.val) (hx7 : wk.1.val ≤ 6)
    (hy0 : 1 ≤ wk.2.val) (hy7 : wk.2.val ≤ 6) : ∃ r, Legal q r := by
  have qfar := queen_distant_of_not_check hq hc
  obtain ⟨t,step,far,ray⟩ := interior_escape_geometry hfar qfar hx0 hx7 hy0 hy7
  have ne : t ≠ qs := by intro e; rw [e,dInf_comm] at step; omega
  obtain ⟨r,hr,_,_⟩ := weak_move hq ht step ne far (fun h => ray (sees_ray h))
  exact ⟨r,hr⟩

/-- Every legal KQK stalemate lies on the board boundary. -/
theorem stalemate_boundary {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ.opp)
    (hfar : 2 ≤ dInf sk wk) (hc : inCheck q σ.opp = false)
    (hn : ¬∃ r, Legal q r) :
    wk.1.val = 0 ∨ wk.1.val = 7 ∨ wk.2.val = 0 ∨ wk.2.val = 7 := by
  by_cases edge : wk.1.val = 0 ∨ wk.1.val = 7 ∨ wk.2.val = 0 ∨ wk.2.val = 7
  · exact edge
  have bx := wk.1.isLt
  have by' := wk.2.isLt
  exact False.elim (hn (interior_reply_exists hq ht hfar hc
    (by omega) (by omega) (by omega) (by omega)))

end EndgameChess.Rules.KQK
