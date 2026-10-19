import EndgameChess.Rules.ForcingDefinitions

/-! S033 / EC-C022: abstract additive rule layer, not a concrete FIDE history model.
Paper: proofs/EC-C022_RULE_LAYER_PROJECTION.md. Frozen definitions are unchanged. -/
namespace EndgameChess.Rules.HistoryLayer
open EndgameChess.KK

universe u

/-- Actual board steps must project soundly and cover every raw legal reply,
including children which terminate in a draw. Proof fields apply when ongoing. -/
structure Layer (State : Type u) where
  erase : State → Position
  BoardStep : State → State → Prop
  Ongoing : State → Prop
  CanClaim : State → Prop
  step_sound : ∀ {s t}, Ongoing s → BoardStep s t → Legal (erase s) (erase t)
  reply_complete : ∀ {s} {r}, Ongoing s → Legal (erase s) r →
    ∃ t, BoardStep s t ∧ erase t = r
  ongoing_not_dead : ∀ {s}, Ongoing s → ¬ DeadK (erase s)

/-- Exact named-colour board mate is terminal, with no extra claim turn. -/
def Goal {State : Type u} (L : Layer State) (σ : Colour) (s : State) : Prop :=
  MateGoal σ (L.erase s)

/-- Finite budget in board plies. A successful claim is a terminal draw,
not a BoardStep; a defender's available current or intended claim blocks forcing. -/
def RuleMateWithin {State : Type u} (L : Layer State) (σ : Colour) : Nat → State → Prop
  | 0, s => Goal L σ s
  | n + 1, s => Goal L σ s ∨ (L.Ongoing s ∧
      (((L.erase s).turn = σ ∧ ∃ t, L.BoardStep s t ∧ RuleMateWithin L σ n t) ∨
       ((L.erase s).turn = σ.opp ∧ ¬ L.CanClaim s ∧
        (∃ t, L.BoardStep s t) ∧ ∀ t, L.BoardStep s t → RuleMateWithin L σ n t)))

/-- A rule-layer named-colour mate certificate with a uniform finite ply bound. -/
def RuleForceMate {State : Type u} (L : Layer State) (σ : Colour) (s : State) : Prop :=
  ∃ n, RuleMateWithin L σ n s

end EndgameChess.Rules.HistoryLayer
