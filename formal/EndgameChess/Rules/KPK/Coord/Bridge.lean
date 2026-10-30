import EndgameChess.Rules.KPK.Coord.Game
import EndgameChess.Rules.KPK.KeySquares

/-! Bridge between kernel squares and the oriented, file-normalised coordinate
game. No outcome is assumed here: each statement is about move geometry. -/
namespace EndgameChess.Rules.KPK.Coord
open EndgameChess.KK

/-- Reflect files so that the pawn stands on one of the four left files. -/
def mx (ps : Square) (t : Square) : Nat := if ps.1.val ≤ 3 then t.1.val else 7 - t.1.val

theorem mx_le (ps t : Square) : mx ps t ≤ 7 := by
  simp only [mx]; split <;> omega

theorem mx_pawn (ps : Square) : mx ps ps ≤ 3 := by
  simp only [mx]; split <;> omega

theorem mx_congr {ps p' : Square} (files : ps.1 = p'.1) (t : Square) : mx ps t = mx p' t := by
  simp only [mx, files]

theorem height_val (σ : Colour) (t : Square) : height σ t ≤ 7 := height_le σ t

theorem square_eq_coords {σ : Colour} {ps s t : Square} :
    s = t ↔ mx ps s = mx ps t ∧ height σ s = height σ t := by
  rw [square_eq_oriented (σ := σ)]
  simp only [mx, Fin.ext_iff]
  split <;> omega

theorem near_iff (σ : Colour) (ps s t : Square) :
    dInf s t = 1 ↔ Near (mx ps s) (height σ s) (mx ps t) (height σ t) := by
  rw [dInf_oriented σ]
  have hs := height_le σ s
  have ht := height_le σ t
  simp only [Near, mx, absDiff]
  split <;> omega

theorem apart_iff (σ : Colour) (ps s t : Square) :
    2 ≤ dInf s t ↔ Apart (mx ps s) (height σ s) (mx ps t) (height σ t) := by
  rw [dInf_oriented σ]
  simp only [Apart, mx, absDiff]
  split <;> omega

theorem att_iff (σ : Colour) (ps t : Square) :
    PawnSees σ ps t ↔ Att (mx ps ps) (height σ ps) (mx ps t) (height σ t) := by
  rw [pawn_sees_oriented]
  simp only [Att, mx, absDiff]
  split <;> omega

/-- Every abstract square on the board comes from a kernel square. -/
theorem exists_square (σ : Colour) (ps : Square) {x y : Nat} (hx : x ≤ 7) (hy : y ≤ 7) :
    ∃ t : Square, mx ps t = x ∧ height σ t = y := by
  let file : Fin 8 := if ps.1.val ≤ 3 then ⟨x, by omega⟩ else ⟨7 - x, by omega⟩
  refine ⟨atHeight σ file ⟨y, by omega⟩, ?_, height_atHeight σ file ⟨y, by omega⟩⟩
  have first : (atHeight σ file ⟨y, by omega⟩).1 = file := by cases σ <;> rfl
  simp only [mx, first, file]
  split
  · simp
  · simp; omega

/-- The coordinate tuple of a KPK configuration. -/
structure Coords where
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  e : Nat
  f : Nat

def coords (σ : Colour) (sk ps wk : Square) : Coords :=
  ⟨mx ps sk, height σ sk, mx ps ps, height σ ps, mx ps wk, height σ wk⟩

/-- Exact material with separated kings and an unpromoted pawn. -/
structure Cfg (q : Position) (σ : Colour) (sk ps wk : Square) : Prop where
  material : IsKPK q σ sk ps wk
  far : 2 ≤ dInf sk wk
  low : 1 ≤ height σ ps
  high : height σ ps ≤ 6
  rights : q.castling = noRights

theorem fresh_cfg {q : Position} {σ : Colour} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk) : Cfg q σ sk ps wk := by
  have low := fresh.pawnLower
  have high := fresh.pawnUpper
  refine ⟨h, fresh.kings, ?_, ?_, fresh.rights⟩ <;> cases σ <;> simp only [height] <;> omega

theorem dom_of_cfg {q : Position} {σ : Colour} {sk ps wk : Square} (h : Cfg q σ sk ps wk) :
    Dom (mx ps sk) (height σ sk) (mx ps ps) (height σ ps) (mx ps wk) (height σ wk) := by
  refine ⟨mx_le _ _, height_le _ _, mx_pawn _, h.low, h.high, mx_le _ _, height_le _ _, ?_, ?_,
    (apart_iff σ ps sk wk).mp h.far⟩
  · intro same
    exact h.material.1 (square_eq_coords (σ := σ) (ps := ps).mpr same)
  · intro same
    exact h.material.2.2.1 ((square_eq_coords (σ := σ) (ps := ps).mpr same).symm)

theorem domS_of_cfg {q : Position} {σ : Colour} {sk ps wk : Square} (h : Cfg q σ sk ps wk)
    (safe : inCheck q q.turn.opp = false) (turn : q.turn = σ) :
    DomS (mx ps sk) (height σ sk) (mx ps ps) (height σ ps) (mx ps wk) (height σ wk) := by
  refine ⟨dom_of_cfg h, ?_⟩
  intro attack
  have check := (weak_check h.material).mpr (Or.inr ((att_iff σ ps wk).mpr attack))
  rw [turn, check] at safe
  cases safe

/-- A legal weak reply which keeps the pawn is an abstract weak step. -/
theorem weak_step_of_legal {q r : Position} {σ : Colour} {sk ps wk t : Square}
    (h : Cfg q σ sk ps wk) (turn : q.turn = σ.opp) (legal : Legal q r)
    (material : IsKPK r σ sk ps t) (step : dInf wk t = 1) :
    WeakStep (mx ps sk) (height σ sk) (mx ps ps) (height σ ps) (mx ps wk) (height σ wk)
      (mx ps t) (height σ t) := by
  have apart := LoneKing.kings_apart_after (by decide) material legal
  refine ⟨(near_iff σ ps wk t).mp step, mx_le _ _, height_le _ _, ?_, (apart_iff σ ps sk t).mp apart, ?_⟩
  · intro same
    exact material.2.2.1 ((square_eq_coords (σ := σ) (ps := ps).mpr same).symm)
  · intro attack
    have check := (weak_check material).mpr (Or.inr ((att_iff σ ps t).mpr attack))
    have safe := legal_mover_safe legal
    rw [turn, check] at safe
    cases safe

/-- An abstract weak step is realised by a legal quiet reply. -/
theorem legal_of_weak_step {q : Position} {σ : Colour} {sk ps wk : Square} {x y : Nat}
    (h : Cfg q σ sk ps wk) (turn : q.turn = σ.opp)
    (step : WeakStep (mx ps sk) (height σ sk) (mx ps ps) (height σ ps) (mx ps wk) (height σ wk) x y) :
    ∃ r t, Legal q r ∧ IsKPK r σ sk ps t ∧ r.turn = σ ∧ mx ps t = x ∧ height σ t = y ∧
      dInf wk t = 1 := by
  obtain ⟨near, hx, hy, notPawn, apart, notAttack⟩ := step
  obtain ⟨t, rfl, rfl⟩ := exists_square σ ps hx hy
  have one := (near_iff σ ps wk t).mpr near
  obtain ⟨r, legal, material, nextTurn⟩ := weak_move h.material turn one
    (fun same => notPawn ((square_eq_coords (σ := σ) (ps := ps)).mp same))
    ((apart_iff σ ps sk t).mpr apart) (fun sees => notAttack ((att_iff σ ps t).mp sees))
  exact ⟨r, t, legal, material, nextTurn, rfl, rfl, one⟩

/-- An abstract king step of the pawn owner is a legal quiet move. -/
theorem legal_of_king_step {q : Position} {σ : Colour} {sk ps wk : Square} {x y : Nat}
    (h : Cfg q σ sk ps wk) (turn : q.turn = σ)
    (step : KingStep (mx ps sk) (height σ sk) (mx ps ps) (height σ ps) (mx ps wk) (height σ wk) x y) :
    ∃ m t, isLegal q m = true ∧ m.src = sk ∧ IsKPK (play q m) σ t ps wk ∧
      (play q m).turn = σ.opp ∧ mx ps t = x ∧ height σ t = y := by
  obtain ⟨near, hx, hy, notPawn, apart⟩ := step
  obtain ⟨t, rfl, rfl⟩ := exists_square σ ps hx hy
  have one := (near_iff σ ps sk t).mpr near
  have far := (apart_iff σ ps t wk).mpr apart
  have ne : t ≠ ps := fun same => notPawn ((square_eq_coords (σ := σ) (ps := ps)).mp same)
  let m : Move := ⟨sk, t, none⟩
  have nsk : t ≠ sk := Ne.symm (ne_of_dInf_pos (by omega))
  have nwk : t ≠ wk := ne_of_dInf_pos (by omega)
  have empty : q.board t = none := by
    rw [h.material.2.2.2]; exact LoneKing.board_none.mpr ⟨nsk, ne, nwk⟩
  have source : q.board m.src = some ⟨q.turn, .king⟩ := by
    rw [turn, h.material.2.2.2]; exact LoneKing.board_sk
  have pseudo : isPseudo q m = true := by
    rw [isPseudo_of_king source]
    simp [m, targetOK, empty, kingGeom_iff.mpr one]
  have material := king_play_material h.material turn (m := m) rfl rfl one empty
  have safe : inCheck (play q m) q.turn = false := by
    rw [turn]; exact strong_not_check material far
  have legal : isLegal q m = true := by simp [isLegal, pseudo, safe]
  exact ⟨m, t, legal, rfl, material, by rw [play_turn, turn], rfl, rfl⟩

/-- The square one or two pawn steps ahead. -/
theorem push_of_free {q : Position} {σ : Colour} {sk ps wk : Square} {y : Nat}
    (h : Cfg q σ sk ps wk) (hy : y ≤ 7) (shape : y = height σ ps + 1)
    (free : Free (mx ps sk) (height σ sk) (mx ps wk) (height σ wk) (mx ps ps) y) :
    ∃ t, t.1 = ps.1 ∧ height σ t = y ∧ Push q σ ps t := by
  let t := atHeight σ ps.1 ⟨y, by omega⟩
  have file : t.1 = ps.1 := by cases σ <;> rfl
  have rank : height σ t = y := height_atHeight σ ps.1 ⟨y, by omega⟩
  have mxt : mx ps t = mx ps ps := mx_congr (ps := ps) (p' := ps) rfl t ▸ by simp only [mx, file]
  have nsk : t ≠ sk := by
    intro same
    exact free.1 ⟨by rw [← same, mxt], by rw [← same, rank]⟩
  have nwk : t ≠ wk := by
    intro same
    exact free.2 ⟨by rw [← same, mxt], by rw [← same, rank]⟩
  have nps : t ≠ ps := by
    intro same
    have := congrArg (height σ) same
    omega
  refine ⟨t, file, rank, ?_, ?_, Or.inl ?_⟩
  · simp only [dx, file]; omega
  · rw [h.material.2.2.2]; exact LoneKing.board_none.mpr ⟨nsk, nps, nwk⟩
  · cases σ <;> simp only [dy, forward, height] at rank shape ⊢ <;> omega

theorem double_of_free {q : Position} {σ : Colour} {sk ps wk : Square}
    (h : Cfg q σ sk ps wk) (one : height σ ps = 1)
    (free1 : Free (mx ps sk) (height σ sk) (mx ps wk) (height σ wk) (mx ps ps) (height σ ps + 1))
    (free2 : Free (mx ps sk) (height σ sk) (mx ps wk) (height σ wk) (mx ps ps) 3) :
    ∃ t, t.1 = ps.1 ∧ height σ t = 3 ∧ Push q σ ps t := by
  let t := atHeight σ ps.1 ⟨3, by omega⟩
  let u := atHeight σ ps.1 ⟨2, by omega⟩
  have file : t.1 = ps.1 := by cases σ <;> rfl
  have fileU : u.1 = ps.1 := by cases σ <;> rfl
  have rank : height σ t = 3 := height_atHeight σ ps.1 ⟨3, by omega⟩
  have rankU : height σ u = 2 := height_atHeight σ ps.1 ⟨2, by omega⟩
  have mxt : mx ps t = mx ps ps := by simp only [mx, file]
  have mxu : mx ps u = mx ps ps := by simp only [mx, fileU]
  have ne (v : Square) (mv : mx ps v = mx ps ps) (hv : height σ v ≠ 1) :
      (v ≠ sk ∧ v ≠ wk → v ≠ sk ∧ v ≠ ps ∧ v ≠ wk) := by
    rintro ⟨s, w⟩
    refine ⟨s, ?_, w⟩
    intro same
    exact hv (by rw [same, one])
  have nsk : t ≠ sk := fun same => free2.1 ⟨by rw [← same, mxt], by rw [← same, rank]⟩
  have nwk : t ≠ wk := fun same => free2.2 ⟨by rw [← same, mxt], by rw [← same, rank]⟩
  have nskU : u ≠ sk := fun same => free1.1 ⟨by rw [← same, mxu], by rw [← same, rankU, one]⟩
  have nwkU : u ≠ wk := fun same => free1.2 ⟨by rw [← same, mxu], by rw [← same, rankU, one]⟩
  refine ⟨t, file, rank, ?_, ?_, Or.inr ⟨?_, ?_, ?_⟩⟩
  · simp only [dx, file]; omega
  · rw [h.material.2.2.2]
    exact LoneKing.board_none.mpr (ne t mxt (by omega) ⟨nsk, nwk⟩)
  · cases σ <;> simp only [dy, forward, height] at rank one ⊢ <;> omega
  · cases σ <;> simp only [pawnRank, height] at one ⊢ <;> omega
  · rw [pathClear_iff]
    intro v between
    have shape : v = u := by
      apply (square_eq_oriented (σ := σ)).mpr
      have vh := height_le σ v
      simp only [isBetween, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, dInf, absDiff, dx, dy] at between
      obtain ⟨⟨⟨n1, n2⟩, cross⟩, sum⟩ := between
      have hf : ps.1.val = t.1.val := by rw [file]
      have fv : (v.1.val : Int) - ps.1.val = 0 := by
        have ht : (t.2.val : Int) - ps.2.val ≠ 0 := by
          cases σ <;> simp only [height] at rank one <;> omega
        have zero : ((v.1.val : Int) - ps.1.val) * ((t.2.val : Int) - ps.2.val) = 0 := by
          rw [cross]
          have : (t.1.val : Int) - ps.1.val = 0 := by omega
          rw [this, Int.mul_zero]
        rcases Int.mul_eq_zero.mp zero with zero | zero
        · exact zero
        · exact False.elim (ht zero)
      constructor
      · apply Fin.ext; rw [fileU]; omega
      · rw [rankU]
        have vne : ¬ v = ps := n1
        have vnt : ¬ v = t := n2
        have neps : v.2.val ≠ ps.2.val := fun e => vne (Prod.ext (Fin.ext (by omega)) (Fin.ext e))
        have net : v.2.val ≠ t.2.val := fun e => vnt (Prod.ext (Fin.ext (by omega)) (Fin.ext e))
        cases σ <;> simp only [height] at rank one ⊢ <;> omega
    subst shape
    rw [h.material.2.2.2]
    exact LoneKing.board_none.mpr (ne u mxu (by omega) ⟨nskU, nwkU⟩)

end EndgameChess.Rules.KPK.Coord
