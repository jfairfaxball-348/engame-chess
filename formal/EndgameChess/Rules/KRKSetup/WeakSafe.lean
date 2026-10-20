import EndgameChess.Rules.KRKSetup.Arrival
namespace EndgameChess.Rules
open EndgameChess.KK
variable {B : Nat}
set_option maxHeartbeats 3000000


/-- Every legal safe weak reply is a strong legal arrival at the common B+4 budget. -/
theorem setup_weak_safe_budget {q : Position} {σ : Colour} {sk rs wk : Square}
    (hwall : KRKWallBudget σ B) (hq : Matches q σ ⟨sk, rs, wk, false⟩)
    (safe : SafeRook sk rs wk) (moves : ∃ r, Legal q r) : MateWithin σ (B + 5) q := by
  apply mateWithin_defend hq.2 moves
  intro r legal
  obtain ⟨w, hm, _⟩ := krk_safe_reply hq.1 hq.2 safe legal
  exact setup_arrival_budget hwall hm.1 hm.2 ⟨q, legal⟩

end EndgameChess.Rules
