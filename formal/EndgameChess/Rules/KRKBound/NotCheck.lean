import EndgameChess.Rules.KRKBound.PositiveSetup
namespace EndgameChess.Rules
open EndgameChess.KK
set_option maxHeartbeats 3000000

/-- Clock-free KRK wins on the strong turn whenever the lone king is not in
check. The setup strategy is finite and covers every legal defending reply. -/
theorem krk_strong_bound_of_not_check {q : Position} {σ : Colour} {sk rs wk : Square}
    (hk : IsKRK q σ sk rs wk) (ht : q.turn = σ)
    (hc : inCheck q σ.opp = false) : MateWithin σ 508 q := by
  have hn : ¬ (dInf sk wk = 1 ∨ RookSees rs wk sk wk) := by
    intro h
    rw [(inCheck_weak_krk hk.1 hk.2.1 hk.2.2.1 hk.2.2.2).2 h] at hc
    cases hc
  have h0 : dInf sk wk ≠ 0 := fun h => hk.2.1 (dInf_eq_zero_iff.1 h)
  have hd : 2 ≤ dInf sk wk := by have := fun h => hn (Or.inl h); omega
  obtain ⟨g, _, hg⟩ := krk_setup_axis hd
  have hq : Matches q σ ⟨sk, rs, wk, true⟩ := ⟨hk, ht⟩
  have hcanon : Matches (krkPos σ (g.f sk) (g.f rs) (g.f wk) σ) σ
      ((⟨sk, rs, wk, true⟩ : KRKState).map g) :=
    ⟨⟨g.ne_iff.2 hk.1, g.ne_iff.2 hk.2.1, g.ne_iff.2 hk.2.2.1, rfl⟩, rfl⟩
  apply krk_bound_transport g hcanon rfl
  · simpa only [KRKState.map_map] using hq
  · apply positive_setup_bound hcanon hg
    rw [g.sees_iff]
    exact fun h => hn (Or.inr h)
end EndgameChess.Rules
