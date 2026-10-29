import EndgameChess.Rules.HistoryLayer.Projection
import EndgameChess.Rules.KRKStrategy.Line
import EndgameChess.Rules.RawClock.Definitions

/-! Fresh-root rules states: no reachability trace from the initial chess
position is required. Only future legal play supplies clock/history data. -/
namespace EndgameChess.Rules.FreshGame
open EndgameChess.KK

structure State where
  board : Position
  past : List Position
  clock : Nat

def fresh (q : Position) : State := ⟨q,[],0⟩

noncomputable def occurrences (s : State) : Nat := by
  classical
  exact 1+(s.past.filter (fun q => decide (RawRepetition.key q = RawRepetition.key s.board))).length

def afterMove (s : State) (m : Move) : State :=
  ⟨play s.board m,s.board::s.past,if RawClock.zeroing s.board m then 0 else s.clock+1⟩

/-- Checkmate remains a separate terminal goal, with priority over draws. -/
def Ongoing (s : State) : Prop :=
  ¬ DeadK s.board ∧ (∃ r, Legal s.board r) ∧ s.clock < 150 ∧ occurrences s < 5

def BoardStep (s t : State) : Prop :=
  Ongoing s ∧ ∃ m, isLegal s.board m = true ∧ t = afterMove s m

def CurrentClaim (s : State) : Prop := 100 ≤ s.clock ∨ 3 ≤ occurrences s

def CanClaim (s : State) : Prop :=
  CurrentClaim s ∨ ∃ m, isLegal s.board m = true ∧ CurrentClaim (afterMove s m)

def layer : HistoryLayer.Layer State where
  erase := State.board
  BoardStep := BoardStep
  Ongoing := Ongoing
  CanClaim := CanClaim
  step_sound := by
    rintro s t _ ⟨_,m,hm,rfl⟩
    exact ⟨m,hm,rfl⟩
  reply_complete := by
    rintro s r ongoing ⟨m,hm,rfl⟩
    exact ⟨afterMove s m,⟨ongoing,m,hm,rfl⟩,rfl⟩
  ongoing_not_dead := fun h => h.1

abbrev Within (σ : Colour) (n : Nat) (s : State) := HistoryLayer.RuleMateWithin layer σ n s
abbrev Win (σ : Colour) (s : State) := HistoryLayer.RuleForceMate layer σ s

theorem step_legal {s t : State} (h : BoardStep s t) : Legal s.board t.board :=
  layer.step_sound h.1 h

theorem clock_step_le {s t : State} (h : BoardStep s t) : t.clock ≤ s.clock+1 := by
  obtain ⟨_,m,_,rfl⟩ := h
  dsimp [afterMove]
  split <;> omega

end EndgameChess.Rules.FreshGame
