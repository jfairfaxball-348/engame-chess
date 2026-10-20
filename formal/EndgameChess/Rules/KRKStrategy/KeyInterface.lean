import EndgameChess.Rules.RawRepetition.KeyCongruence
import EndgameChess.Rules.KRKBound.Pair
namespace EndgameChess.Rules
open EndgameChess.KK

/-- Equal normalized raw keys preserve the exact root interface used by forcing. -/
theorem strategy_key_interface {q r : Position} (hk : RawRepetition.key q = RawRepetition.key r) :
    q.turn = r.turn ∧ (∀ c, inCheck q c = inCheck r c) ∧
    (∀ z, Legal q z ↔ Legal r z) ∧ (∀ σ, MateGoal σ q ↔ MateGoal σ r) := by
  have hb : q.board = r.board := by
    simpa only [RawRepetition.key, RawRepetition.normalizeEP] using congrArg Position.board hk
  have ht : q.turn = r.turn := by
    simpa only [RawRepetition.key, RawRepetition.normalizeEP] using congrArg Position.turn hk
  have hc : ∀ c, inCheck q c = inCheck r c := by
    intro c
    simp only [inCheck, hb]
  have hl : ∀ z, Legal q z ↔ Legal r z := by
    intro z
    constructor
    · rintro ⟨m, hm, he⟩
      obtain ⟨sameLegal, samePlay⟩ := RawRepetition.key_legal_congr q r hk m
      exact ⟨m, sameLegal ▸ hm, he.trans (samePlay hm)⟩
    · rintro ⟨m, hm, he⟩
      obtain ⟨sameLegal, samePlay⟩ := RawRepetition.key_legal_congr r q hk.symm m
      exact ⟨m, sameLegal ▸ hm, he.trans (samePlay hm)⟩
  refine ⟨ht, hc, hl, ?_⟩
  intro σ
  simp only [MateGoal, MatedK, ht, hc, hl]
end EndgameChess.Rules
