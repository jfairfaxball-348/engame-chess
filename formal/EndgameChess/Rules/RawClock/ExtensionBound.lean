import EndgameChess.Rules.RawTrace.ExtensionDefinitions
import EndgameChess.Rules.RawClock.StepBound

/-! S038 / EC-C025: no terminal filter or endpoint-clock assumption. -/
namespace EndgameChess.Rules.RawClock

/-- Every actual n-ply extension increases the raw counter by at most n. -/
theorem clock_le_extension {n : Nat} {s t : RawTrace.State}
    (h : RawTrace.Extends n s t) : clock t.trace ≤ clock s.trace + n := by
  induction h with
  | refl s => exact Nat.le_refl _
  | @snoc n s u t prior step ih =>
    obtain ⟨m, hm, rfl⟩ := step
    have hedge := append_clock_le u m hm
    exact Nat.le_trans hedge (by simpa only [Nat.add_assoc] using (Nat.add_le_add_right ih 1))

end EndgameChess.Rules.RawClock
