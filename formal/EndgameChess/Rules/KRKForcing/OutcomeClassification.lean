import EndgameChess.Rules.KRKForcing.SafeSetup

/-! S030 / EC-C011: clock-free weak-turn terminal/capture classification. -/
namespace EndgameChess.Rules
open EndgameChess.KK

/-- On the weak turn, named-colour forcing is actual mate or a nonempty reply
set with no legal rook capture to KK. Stalemate and any capture are excluded. -/
theorem krk_weak_force_iff {q : Position} {σ : Colour} {sk rs wk : Square}
    (hk : IsKRK q σ sk rs wk) (ht : q.turn = σ.opp) :
    ForceMate σ q ↔ MatedK q ∨ ((∃ r, Legal q r) ∧
      ∀ r, Legal q r → ¬ ∃ w b, IsKK r w b) := by
  classical
  constructor
  · intro hw
    by_cases hne : ∃ r, Legal q r
    · right
      refine ⟨hne, fun r hr hkk => ?_⟩
      obtain ⟨w, b, hb⟩ := hkk
      exact dead_reply_not_forceMate ht hr (dead_of_legal_into_KK hr hb) hw
    · exact Or.inl ((forceMate_no_moves_iff hne).1 hw).2
  · rintro (hm | ⟨hne, hall⟩)
    · exact forceMate_of_goal ⟨ht, hm⟩
    · apply forceMate_defend ht hne
      intro r hr
      rcases lone_move_cases hk ht hr with ⟨t, hkr, htr⟩ | hkk
      · exact krk_strong_arrival_force hkr htr ⟨q, hr⟩
      · exact False.elim (hall r hr hkk)

/-- Equivalent geometric interface: a nonterminal weak turn wins precisely
when the rook is distant or protected and a legal reply exists. -/
theorem krk_weak_force_safe_iff {q : Position} {σ : Colour} {sk rs wk : Square}
    (hk : IsKRK q σ sk rs wk) (ht : q.turn = σ.opp) :
    ForceMate σ q ↔ MatedK q ∨ (SafeRook sk rs wk ∧ ∃ r, Legal q r) := by
  classical
  constructor
  · intro hw
    rcases (krk_weak_force_iff hk ht).1 hw with hm | ⟨hne, _⟩
    · exact Or.inl hm
    · exact Or.inr ⟨krk_force_weak_safe hk ht hw, hne⟩
  · rintro (hm | ⟨hs, hne⟩)
    · exact forceMate_of_goal ⟨ht, hm⟩
    · apply forceMate_defend ht hne
      intro r hr
      obtain ⟨t, hmt, _⟩ := krk_safe_reply hk ht hs hr
      exact krk_strong_arrival_force hmt.1 hmt.2 ⟨q, hr⟩

end EndgameChess.Rules
