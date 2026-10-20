import EndgameChess.Rules.RawHistoryLayer.Definitions
import EndgameChess.Rules.RawClock.Append
import EndgameChess.Rules.KRKLive.Main
namespace EndgameChess.Rules.KRKTermination
open EndgameChess.KK
open RawHistoryLayer

/-- Exact KRK, or an already terminal admitted endpoint. -/
def Region (σ : Colour) (s : State) : Prop :=
  (∃ sk rs wk, IsKRK (erase s) σ sk rs wk) ∨ ¬Ongoing s

/-- Remaining board-ply fuel; every terminal endpoint has zero fuel. -/
noncomputable def fuel (s : State) : Nat := by
  classical
  exact if Ongoing s then 150 - RawClock.clock s.val.trace else 0

/-- A forward finite path through actual initial-rooted admitted states. -/
inductive Path : Nat → State → State → Prop
  | refl (s : State) : Path 0 s s
  | cons {n : Nat} {s u t : State} : BoardStep s u → Path n u t → Path (n+1) s t

/-- Maximal means the last admitted endpoint has no board-step successor. -/
def Maximal (s : State) : Prop := ¬∃ t, BoardStep s t
end EndgameChess.Rules.KRKTermination
