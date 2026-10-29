import EndgameChess.Rules.KPK.SupportedPrefix
import EndgameChess.Rules.KPK.Coordinates

namespace EndgameChess.Rules.KPK
open EndgameChess.KK

/-- King on the seventh rank and an adjacent-file pawn on the sixth. -/
def SeventhKing (σ : Colour) (sk ps : Square) : Prop :=
  height σ sk = 6 ∧ height σ ps = 5 ∧ absDiff sk.1.val ps.1.val = 1

/-- The only weak-turn stalemate in this king/pawn band is the outside corner. -/
def SixthCornerStalemate (σ : Colour) (ps wk : Square) : Prop :=
  height σ wk = 7 ∧ (wk.1.val = 0 ∨ wk.1.val = 7) ∧ absDiff ps.1.val wk.1.val = 1

theorem seventh_king_protects_pawn {σ : Colour} {sk ps : Square}
    (band : SeventhKing σ sk ps) : dInf sk ps = 1 := by
  rw [dInf_oriented σ, band.1, band.2.1, band.2.2]
  decide

theorem seventh_king_advance {q : Position} {σ : Colour} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (band : SeventhKing σ sk ps) (far : 2 ≤ dInf sk wk) :
    Push q σ ps (atHeight σ ps.1 6) ∧ SupportedSeventh σ sk (atHeight σ ps.1 6) := by
  have rank : height σ (atHeight σ ps.1 6) = 6 := height_atHeight σ ps.1 6
  have support : SupportedSeventh σ sk (atHeight σ ps.1 6) := ⟨band.1, rank, band.2.2⟩
  have protect : dInf sk (atHeight σ ps.1 6) = 1 := by
    rw [dInf_oriented σ, band.1, rank]
    change max (absDiff sk.1.val ps.1.val) (absDiff 6 6) = 1
    rw [band.2.2]; decide
  have notKing : atHeight σ ps.1 6 ≠ sk := by
    intro same; rw [same, dInf_eq_zero_iff.mpr rfl] at protect; cases protect
  have notPawn : atHeight σ ps.1 6 ≠ ps := by
    intro same; rw [same, band.2.1] at rank; cases rank
  have notWeak : atHeight σ ps.1 6 ≠ wk := by intro same; rw [same] at protect; omega
  refine ⟨⟨by simp [dx, atHeight], ?_, Or.inl ?_⟩, support⟩
  · rw [h.2.2.2]; exact LoneKing.board_none.mpr ⟨notKing, notPawn, notWeak⟩
  · have oldRank := band.2.1
    cases σ <;> simp only [atHeight, height, dy, forward] at oldRank ⊢ <;> omega

theorem seventh_king_advance_legal {q : Position} {σ : Colour} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (turn : q.turn = σ)
    (band : SeventhKing σ sk ps) (far : 2 ≤ dInf sk wk) :
    isLegal q ⟨ps, atHeight σ ps.1 6, none⟩ = true := by
  apply (pawn_legal_iff h turn rfl far).mpr
  refine ⟨(seventh_king_advance h band far).1, ?_⟩
  apply (promo_none_iff σ ps _).mpr
  rw [height_atHeight]; decide

theorem seventh_king_weak_reply {q r : Position} {σ : Colour} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (turn : q.turn = σ.opp)
    (band : SeventhKing σ sk ps) (legal : Legal q r) :
    ∃ t, IsKPK r σ sk ps t ∧ r.turn = σ ∧ 2 ≤ dInf sk t := by
  obtain ⟨t, material, nextTurn, _⟩ := LoneKing.safe_reply h turn
    (Or.inr (seventh_king_protects_pawn band)) legal
  exact ⟨t, material, nextTurn, LoneKing.kings_apart_after (by decide) material legal⟩

theorem sixth_corner_no_moves {q : Position} {σ : Colour} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (turn : q.turn = σ.opp)
    (band : SeventhKing σ sk ps) (far : 2 ≤ dInf sk wk)
    (corner : SixthCornerStalemate σ ps wk) : ¬ ∃ r, Legal q r := by
  rintro ⟨r, legal⟩
  obtain ⟨t, material, _, step⟩ := LoneKing.safe_reply h turn
    (Or.inr (seventh_king_protects_pawn band)) legal
  have nextFar := LoneKing.kings_apart_after (by decide) material legal
  have notAttack : ¬ PawnSees σ ps t := by
    intro attack
    have check := (weak_check material).mpr (Or.inr attack)
    have safe := legal_mover_safe legal
    rw [turn, check] at safe; cases safe
  rw [pawn_sees_oriented] at notAttack
  obtain ⟨kingRank, pawnRank, supportFiles⟩ := band
  obtain ⟨top, edge, pawnFiles⟩ := corner
  have ht := height_le σ t
  rcases edge with edge | edge <;>
    simp only [dInf_oriented σ, kingRank, pawnRank, top, absDiff] at step nextFar far notAttack supportFiles pawnFiles <;>
    omega

set_option maxHeartbeats 2000000 in
theorem seventh_king_escape {σ : Colour} {sk ps wk : Square}
    (band : SeventhKing σ sk ps) (far : 2 ≤ dInf sk wk)
    (notCorner : ¬ SixthCornerStalemate σ ps wk) :
    ∃ t, dInf wk t = 1 ∧ 2 ≤ dInf sk t ∧ t ≠ ps ∧ ¬ PawnSees σ ps t := by
  obtain ⟨kingRank, pawnRank, supportFiles⟩ := band
  have bound := height_le σ wk
  let backHeight : Fin 8 := ⟨if height σ wk = 0 then 1 else height σ wk - 1, by split <;> omega⟩
  let back := atHeight σ wk.1 backHeight
  have backRank : height σ back = backHeight.val := height_atHeight σ wk.1 backHeight
  have step : dInf wk back = 1 := by
    rw [dInf_oriented σ, backRank]
    simp only [back, atHeight, backHeight, absDiff]
    split <;> omega
  have apart : 2 ≤ dInf sk back := by
    rw [dInf_oriented σ, kingRank, backRank]
    simp only [back, atHeight, backHeight, absDiff]
    rw [dInf_oriented σ, kingRank] at far
    simp only [absDiff] at far
    split <;> omega
  have notPawn : back ≠ ps := by
    intro same
    have protect := seventh_king_protects_pawn ⟨kingRank, pawnRank, supportFiles⟩
    rw [same] at apart
    omega
  by_cases attack : PawnSees σ ps back
  · have attackShape := (pawn_sees_oriented σ ps back).mp attack
    have top : height σ wk = 7 := by
      rw [backRank, pawnRank] at attackShape
      dsimp [backHeight] at attackShape
      split at attackShape <;> omega
    have adjacent : absDiff ps.1.val wk.1.val = 1 := attackShape.2
    have interior : 1 ≤ wk.1.val ∧ wk.1.val ≤ 6 := by
      have notEdge : ¬ (wk.1.val = 0 ∨ wk.1.val = 7) := fun edge => notCorner ⟨top, edge, adjacent⟩
      omega
    let outFile : Fin 8 := ⟨if wk.1.val < ps.1.val then wk.1.val - 1 else wk.1.val + 1, by split <;> omega⟩
    let out := atHeight σ outFile 7
    have outRank : height σ out = 7 := height_atHeight σ outFile 7
    refine ⟨out, ?_, ?_, ?_, ?_⟩
    · rw [dInf_oriented σ, top, outRank]
      simp only [out, atHeight, outFile, absDiff]
      split <;> omega
    · rw [dInf_oriented σ, kingRank, outRank]
      rw [dInf_oriented σ, kingRank, top] at far
      simp only [out, atHeight, outFile, absDiff] at far adjacent supportFiles ⊢
      split <;> omega
    · intro same
      rw [same, pawnRank] at outRank
      cases outRank
    · rw [pawn_sees_oriented, outRank, pawnRank]
      omega
  · exact ⟨back, step, apart, notPawn, attack⟩

theorem seventh_king_moves_iff {q : Position} {σ : Colour} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (turn : q.turn = σ.opp)
    (band : SeventhKing σ sk ps) (far : 2 ≤ dInf sk wk) :
    (∃ r, Legal q r) ↔ ¬ SixthCornerStalemate σ ps wk := by
  constructor
  · intro moves corner; exact sixth_corner_no_moves h turn band far corner moves
  · intro notCorner
    obtain ⟨t, step, apart, notPawn, notAttack⟩ := seventh_king_escape band far notCorner
    obtain ⟨r, legal, _⟩ := weak_move h turn step notPawn apart notAttack
    exact ⟨r, legal⟩

end EndgameChess.Rules.KPK
