import EndgameChess.Rules.KRKSetup.ClearEntry
namespace EndgameChess.Rules
open EndgameChess.KK
variable {B : Nat}
set_option maxHeartbeats 3000000

theorem setup_clear_axis_entry_budget {σ : Colour} (hwall : KRKWallBudget σ B)
    (g : BoardSym) {q : Position} {sk rs wk : Square}
    (hq : Matches q σ ⟨sk, rs, wk, true⟩)
    (hgap : (g.f sk).2.val + 2 ≤ (g.f wk).2.val)
    (hx : (g.f rs).1.val ≠ (g.f sk).1.val ∨ (g.f sk).2.val < (g.f rs).2.val)
    (hf : 2 ≤ absDiff (g.f rs).1.val (g.f wk).1.val) : MateWithin σ (B + 2) q := by
  have hc : Matches (krkPos σ (g.f sk) (g.f rs) (g.f wk) σ) σ
      ((⟨sk, rs, wk, true⟩ : KRKState).map g) :=
    ⟨⟨g.ne_iff.2 hq.1.1, g.ne_iff.2 hq.1.2.1, g.ne_iff.2 hq.1.2.2.1, rfl⟩, rfl⟩
  apply krk_bound_transport g hc rfl
  · simpa only [KRKState.map_map] using hq
  · exact setup_clear_entry_budget hwall hc hgap hx hf
end EndgameChess.Rules
