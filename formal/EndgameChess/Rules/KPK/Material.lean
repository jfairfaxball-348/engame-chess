import EndgameChess.Rules.LoneKing.Moves

/-! Exact KPK material and directional attacks. No outcome criterion is assumed. -/
namespace EndgameChess.Rules.KPK
open EndgameChess.KK

abbrev IsKPK := LoneKing.Material .pawn
abbrev pawnBoard := LoneKing.board .pawn

def pos (σ : Colour) (sk ps wk : Square) (turn : Colour) : Position :=
  ⟨pawnBoard σ sk ps wk, turn, noRights, none⟩

/-- Local fresh-root legality, without an initial-position reachability premise.
The clock/history are supplied separately by `FreshGame.fresh`. -/
structure FreshLegal (q : Position) (sk ps wk : Square) : Prop where
  rights : q.castling = noRights
  ep : q.ep = none
  kings : 2 ≤ dInf sk wk
  pawnLower : 1 ≤ ps.2.val
  pawnUpper : ps.2.val ≤ 6
  previousSafe : inCheck q q.turn.opp = false

/-- Signed rank increase and one-file separation; occupancy is irrelevant to attack. -/
def PawnSees (σ : Colour) (ps t : Square) : Prop :=
  dy ps t = forward σ ∧ (dx ps t).natAbs = 1

theorem pawn_attacks (b : Board) (σ : Colour) (ps t : Square) :
    attacksFrom b ⟨σ, .pawn⟩ ps t = true ↔ PawnSees σ ps t := by
  simp [attacksFrom, pawnCaptureGeom, PawnSees, Bool.and_eq_true]

theorem strong_check {q : Position} {σ : Colour} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) : inCheck q σ = true ↔ dInf wk sk = 1 :=
  LoneKing.strong_check (by decide) h

theorem weak_check {q : Position} {σ : Colour} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) :
    inCheck q σ.opp = true ↔ dInf sk wk = 1 ∨ PawnSees σ ps wk := by
  rw [LoneKing.weak_check (by decide) h, pawn_attacks]

theorem no_enemy_pawn {q : Position} {σ : Colour} {sk ps wk s : Square}
    (h : IsKPK q σ sk ps wk) : q.board s ≠ some ⟨σ.opp, .pawn⟩ := by
  intro hs
  rw [h.2.2.2] at hs
  rcases LoneKing.board_some hs with ⟨_, e⟩ | ⟨_, e⟩ | ⟨_, e⟩
  · have kind := congrArg Piece.kind e; cases kind
  · have hc := congrArg Piece.colour e
    exact opp_ne σ hc.symm
  · have kind := congrArg Piece.kind e; cases kind

/-- There is precisely one pawn, and it belongs to the named strong side. -/
theorem pawn_at {q : Position} {σ c : Colour} {sk ps wk s : Square}
    (h : IsKPK q σ sk ps wk) (source : q.board s = some ⟨c, .pawn⟩) :
    c = σ ∧ s = ps := by
  rw [h.2.2.2] at source
  rcases LoneKing.board_some source with ⟨_, e⟩ | ⟨square, piece⟩ | ⟨_, e⟩
  · have kind := congrArg Piece.kind e; cases kind
  · exact ⟨congrArg Piece.colour piece, square⟩
  · have kind := congrArg Piece.kind e; cases kind

theorem pawn_material_kind {k : PieceType} {q : Position} {σ : Colour}
    {sk xs wk a ps b : Square} (h : LoneKing.Material k q σ sk xs wk)
    (pawn : IsKPK q σ a ps b) : k = .pawn := by
  have source : q.board ps = some ⟨σ, .pawn⟩ := by
    rw [pawn.2.2.2]; exact LoneKing.board_xs pawn.1
  rw [h.2.2.2] at source
  rcases LoneKing.board_some source with ⟨_, e⟩ | ⟨_, e⟩ | ⟨_, e⟩
  · have kind := congrArg Piece.kind e; cases kind
  · exact (congrArg Piece.kind e).symm
  · have kind := congrArg Piece.kind e; cases kind

/-- Any permitted target for the pawn side is empty: the only enemy is a king. -/
theorem strong_target_empty {q : Position} {σ : Colour} {sk ps wk t : Square}
    (h : IsKPK q σ sk ps wk) (ht : q.turn = σ) :
    targetOK q t = true ↔ q.board t = none := by
  constructor
  · intro ok
    cases he : q.board t with
    | none => rfl
    | some pc =>
      have target := targetOK_some ok he
      rw [h.2.2.2] at he
      rcases LoneKing.board_some he with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
      · exact False.elim (target.1 ht.symm)
      · exact False.elim (target.1 ht.symm)
      · exact False.elim (target.2 rfl)
  · intro he; simp [targetOK, he]

theorem strong_not_check {q : Position} {σ : Colour} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (far : 2 ≤ dInf sk wk) : inCheck q σ = false := by
  cases he : inCheck q σ
  · rfl
  · have near := (strong_check h).mp he
    rw [dInf_comm] at near
    omega

theorem strong_turn_no_pawn_check {q : Position} {σ : Colour} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk) (ht : q.turn = σ) :
    ¬ PawnSees σ ps wk := by
  intro sees
  have hc := (weak_check h).mpr (Or.inr sees)
  have safe := fresh.previousSafe
  rw [ht, hc] at safe
  cases safe

end EndgameChess.Rules.KPK
