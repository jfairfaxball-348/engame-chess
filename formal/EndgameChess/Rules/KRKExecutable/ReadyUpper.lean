import EndgameChess.Rules.KRKExecutable.PrepController
import EndgameChess.Rules.KRKCentral.RankTwo

/-!
KRK01: Ready wall -> next rook rank, with concrete coordinate target and
strict decrease of the paired PREPARATION + HEIGHT potential.

This is a partial bound certificate, not a whole KRK game policy.
-/
namespace EndgameChess.Rules.KRKExecutable
open EndgameChess.KK EndgameChess.Rules.KRKCentral

def wallPotential (sk rs wk : Square) : Nat :=
  12 * (7 - rs.2.val) + prepRank sk rs wk

/-- With a READY strong king and a two-rank upper weak-king gap, the
exact rook-advance coordinate produces a legal move, a nonempty weak
reply set and a strictly lower wallPotential after EVERY legal reply. -/
theorem readyUpperDestination_sound {q : Position} {σ : Colour}
    {sk rs wk : Square}
    (hq : Matches q σ ⟨sk, rs, wk, true⟩)
    (hsy : sk.2.val + 1 = rs.2.val)
    (hw : rs.2.val + 2 ≤ wk.2.val)
    (hs : sk.1.val = 3 ∨ sk.1.val = 4)
    (hf : 2 ≤ absDiff rs.1.val wk.1.val) :
    ∃ c, Legal q c ∧
      Matches c σ ⟨sk, rankAdvanceDestination rs (by omega), wk, false⟩ ∧
      (∃ v, Legal c v) ∧
      ∀ v, Legal c v →
        ∃ t, Matches v σ ⟨sk, rankAdvanceDestination rs (by omega), t, true⟩ ∧
          (rankAdvanceDestination rs (by omega)).2.val < t.2.val ∧
          wallPotential sk (rankAdvanceDestination rs (by omega)) t <
            wallPotential sk rs wk := by
  obtain ⟨nr, c, hfile, hrank, hl, hm, hne, hall⟩ :=
    rank_two_pair hq (by omega) hw hf
  have heq : nr = rankAdvanceDestination rs (by omega) := by
    apply Prod.ext
    · apply Fin.ext
      change nr.1.val = rs.1.val
      exact congrArg Fin.val hfile
    · apply Fin.ext
      change nr.2.val = rs.2.val + 1
      exact hrank
  have hc : centreDistance sk.1.val = 0 := by
    rcases hs with hx | hx
    · simp [centreDistance, hx]
    · simp [centreDistance, hx]
  have hprep0 : prepDistance rs.2.val sk = 0 := by
    simp only [prepDistance, hc, Nat.max_zero]
    omega
  have hprep1 : prepDistance nr.2.val sk = 1 := by
    simp only [prepDistance, hc, Nat.max_zero]
    omega
  have hzero : prepRank sk rs wk = 0 := by
    simp only [prepRank, hprep0, Nat.mul_zero, Nat.zero_add,
      prepMarginDebt, if_pos hf]
  have hnext : ∀ t : Square, prepRank sk nr t ≤ 3 := by
    intro t
    simp only [prepRank, hprep1, prepMarginDebt]
    split <;> omega
  rw [heq] at hm
  refine ⟨c, hl, hm, hne, ?_⟩
  intro v hv
  obtain ⟨t, hmt, hyt, _⟩ := hall v hv
  have rankdrop : wallPotential sk nr t < wallPotential sk rs wk := by
    simp only [wallPotential, hzero]
    have near := hnext t
    have raise : nr.2.val = rs.2.val + 1 := hrank
    omega
  rw [heq] at hmt hyt rankdrop
  exact ⟨t, hmt, hyt, rankdrop⟩

end EndgameChess.Rules.KRKExecutable
