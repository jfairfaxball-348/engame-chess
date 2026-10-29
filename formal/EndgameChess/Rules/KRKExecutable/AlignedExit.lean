import EndgameChess.Rules.KRKExecutable.OppositionActions

/-!
KRK04: the READY lower-band aligned branch is not an opaque first move.
This extracts the **existing** checked opposition action, plus its all-defender
one-reply postcondition, under the precise aligned-READY premises.

This is NOT the constructive full `ExitBound`, an executable `restoration_bound`
dispatcher or a total winning policy. In particular, an initial rook margin of
two or three files does not meet `oppositionFollow_sound`'s four-file input.
-/
namespace EndgameChess.Rules.KRKExecutable
open EndgameChess.KK EndgameChess.Rules

/-- Executable target for the checking rook slide in aligned READY. -/
def alignedReadyDestination (rs wk : Square) : Square :=
  oppositionCheckDestination rs wk

/-- On aligned READY, the fixed rook slide is legal. It either immediately
mates or EVERY legal defender reply moves the weak king exactly one rank up
and by at most one file. This is intentionally only the first pair of the
existential `KRKCentral.exit_step_bound` argument. -/
theorem alignedReadyCheck_sound {q : Position} {σ : Colour}
    {sk rs wk : Square}
    (hq : Matches q σ ⟨sk,rs,wk,true⟩)
    (hsy : sk.2.val+1=rs.2.val)
    (hband : wk.2.val=rs.2.val+1)
    (halign : sk.1.val=wk.1.val)
    (hf : 2≤absDiff rs.1.val wk.1.val) :
    ∃ c, Legal q c ∧
      Matches c σ ⟨sk,alignedReadyDestination rs wk,wk,false⟩ ∧
      (MateGoal σ c ∨
        ((∃ r, Legal c r) ∧ ∀ r, Legal c r →
          ∃ t, Matches r σ ⟨sk,alignedReadyDestination rs wk,t,true⟩ ∧
            t.2.val=wk.2.val+1 ∧ absDiff t.1.val wk.1.val≤1)) := by
  have ho : Opposed sk wk := ⟨halign, by omega⟩
  have hy : rs.2.val ≠ wk.2.val := by omega
  simpa only [alignedReadyDestination] using
    (oppositionCheck_sound hq ho hf hy)

end EndgameChess.Rules.KRKExecutable
