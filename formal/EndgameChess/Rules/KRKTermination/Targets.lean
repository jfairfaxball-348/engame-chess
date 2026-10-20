import EndgameChess.Rules.KRKSetup.SharperWeak
import EndgameChess.Rules.RawClock.Definitions
namespace EndgameChess.Rules
open EndgameChess.KK

/-- Exact KRK has no pawn source; its only occupied legal target is the strong rook. -/
theorem krk_material_targets {q : Position} {σ : Colour} {sk rs wk : Square} {m : Move}
    (hk : IsKRK q σ sk rs wk) (hp : isPseudo q m = true) :
    q.board m.src ≠ some ⟨q.turn, .pawn⟩ ∧
    (∀ pc, q.board m.dst = some pc → m.dst = rs ∧ pc = ⟨σ, .rook⟩ ∧ q.turn ≠ σ) := by
  constructor
  · intro pawn
    rw [hk.2.2.2] at pawn
    rcases krkBoard_some pawn with ⟨_, bad⟩ | ⟨_, bad⟩ | ⟨_, bad⟩
    all_goals
      have badKind := congrArg Piece.kind bad
      cases badKind
  · intro pc dest
    obtain ⟨colour, kind⟩ := targetOK_some (targetOK_of_isPseudo hp) dest
    rw [hk.2.2.2] at dest
    rcases krkBoard_some dest with ⟨squareEq, rfl⟩ | ⟨squareEq, rfl⟩ | ⟨squareEq, rfl⟩
    · exact False.elim (kind rfl)
    · exact ⟨squareEq, rfl, Ne.symm colour⟩
    · exact False.elim (kind rfl)
end EndgameChess.Rules
