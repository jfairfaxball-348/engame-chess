import EndgameChess.Rules.Reach

/-!
# Rules kernel K3 — Article 5.2.2 as an explicit rule definition (gap G3)

FIDE 2023, Art. 5.2.2 (verbatim):

> The game is drawn when a position has arisen in which neither player can checkmate the
> opponent's king with any series of legal moves. The game is said to end in a 'dead
> position'. This immediately ends the game, provided that the move producing the position
> was in accordance with Article 3 and Articles 4.2 – 4.7.

**`Rule5_2_2` is a normative encoding, not a theorem.** Lean cannot prove what the Laws
*say*. Here the rule's content is written down once, as a named definition, so that every
corollary which uses it visibly depends on this definition. The reading:
- "a position has arisen" means `Arisen` (reached from the initial position by legal
  moves, Art. 3.10.3);
- "neither player can checkmate … with any series of legal moves" means `DeadK` (no
  kernel-reachable position is checkmate);
- "drawn … immediately" means the result is `draw`.

The proviso about Articles 4.2–4.7 (the physical act of moving) is outside the model.
-/

namespace EndgameChess.Rules

open EndgameChess.KK

inductive GameResult
  | whiteWins
  | blackWins
  | draw
  deriving DecidableEq, Repr

/-- **Rule encoding of FIDE 2023 Art. 5.2.2** (normative definition, not a theorem): the
game is drawn, immediately, in an arisen dead position. -/
def Rule5_2_2 (q : Position) (r : GameResult) : Prop :=
  Arisen q ∧ DeadK q ∧ r = .draw

/-- Under the rule encoding `Rule5_2_2`, every arisen K vs K position is an immediate draw. -/
theorem kk_drawn_by_rule {q : Position} {w b : Square} (ha : Arisen q) (hk : IsKK q w b) :
    Rule5_2_2 q .draw :=
  ⟨ha, arisen_KK_dead ha hk, rfl⟩

/-- Under the rule encoding `Rule5_2_2`, every arisen K+B vs K position (either
orientation) is an immediate draw. -/
theorem kbk_drawn_by_rule {q : Position} {σ : Colour} {sk bs wk : Square} (ha : Arisen q)
    (hk : IsKBK q σ sk bs wk) : Rule5_2_2 q .draw :=
  ⟨ha, arisen_KBK_dead ha hk, rfl⟩

end EndgameChess.Rules
