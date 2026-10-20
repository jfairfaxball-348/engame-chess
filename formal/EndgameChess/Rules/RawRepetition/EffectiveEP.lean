import EndgameChess.Rules.RawRepetition.Definitions

/-! S044 / EC-C028: existence and exact target consistency, with real legality. -/
namespace EndgameChess.Rules.RawRepetition

open EndgameChess.KK

/-- None exactly without a legal event; every some target has an actual witness. -/
theorem effectiveEP_spec (q : Position) :
    (effectiveEP q = none ↔ ¬ ∃ m, LegalEP q m) ∧
      (∀ dst, effectiveEP q = some dst ↔ ∃ m, LegalEP q m ∧ m.dst = dst) := by
  classical
  by_cases available : ∃ m, LegalEP q m
  · obtain ⟨m, hm⟩ := available
    have witness : ∃ move, LegalEP q move := ⟨m, hm⟩
    have flag : q.ep = some m.dst := hm.2.2.1
    have selected : effectiveEP q = q.ep := by simp [effectiveEP, witness]
    constructor
    · simp [selected, flag, witness]
    · intro dst
      constructor
      · intro target
        have destination : m.dst = dst :=
          Option.some.inj (flag.symm.trans (selected.symm.trans target))
        exact ⟨m, hm, destination⟩
      · rintro ⟨move, event, rfl⟩
        exact selected.trans event.2.2.1
  · constructor
    · simp [effectiveEP, available]
    · intro dst
      constructor
      · intro target
        simp [effectiveEP, available] at target
      · rintro ⟨m, event, _⟩
        exact False.elim (available ⟨m, event⟩)

end EndgameChess.Rules.RawRepetition
