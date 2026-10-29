import EndgameChess.Rules.KQK.StrongEntry
import EndgameChess.Rules.KQK.CaptureBoundary

namespace EndgameChess.Rules.KQK
open EndgameChess.KK

theorem weak_force_safe_iff {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ.opp) :
    ForceMate σ q ↔ MatedK q ∨ (SafeQueen sk qs wk ∧ ∃ r, Legal q r) := by
  constructor
  · intro win
    by_cases moves : ∃ r, Legal q r
    · exact Or.inr ⟨force_weak_safe hq ht win,moves⟩
    · exact Or.inl ((forceMate_no_moves_iff moves).mp win).2
  · rintro (mate | ⟨safe,moves⟩)
    · exact forceMate_of_goal ⟨ht,mate⟩
    · exact ⟨98,safe_weak_entry_bound hq ht safe moves⟩

/-- Deadness is distinct from drawnness: an exposed queen may be captured
although another cooperative noncapturing reply still permits mate. -/
theorem weak_dead_iff {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ.opp) :
    DeadK q ↔ ¬ MatedK q ∧ ∀ r, Legal q r → ∃ w b, IsKK r w b := by
  constructor
  · intro dead
    refine ⟨fun mate => dead ⟨q,ReachK.refl q,mate⟩,?_⟩
    intro r hr
    rcases LoneKing.weak_cases hq ht hr with ⟨t,hm,hrt⟩ | kk
    · have live := forceMate_not_dead (show ForceMate σ r from ⟨97,strong_arrival_bound hm hrt ⟨q,hr⟩⟩)
      exact False.elim (live (fun ⟨u,reach,mate⟩ => dead ⟨u,reachK_cons hr reach,mate⟩))
    · exact kk
  · exact fun ⟨mate,all⟩ => dead_of_succ_KK mate all

/-- Complete board forcing criterion; the same winning cases have the
proved sub100 bounds required by the fresh clock layer. -/
theorem board_outcome_iff {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk)
    (legalArrival : q.turn = σ → inCheck q σ.opp = false) :
    ForceMate σ q ↔ q.turn = σ ∨ MatedK q ∨
      (SafeQueen sk qs wk ∧ ∃ r, Legal q r) := by
  rcases colour_cases σ q.turn with strong | weak
  · exact ⟨fun _ => Or.inl strong,fun _ => ⟨97,strong_entry_bound hq strong (legalArrival strong)⟩⟩
  · constructor
    · intro win; exact Or.inr ((weak_force_safe_iff hq weak).mp win)
    · rintro (wrong | criterion)
      · exact False.elim (opp_ne σ (wrong.symm.trans weak))
      · exact (weak_force_safe_iff hq weak).mpr criterion

end EndgameChess.Rules.KQK
