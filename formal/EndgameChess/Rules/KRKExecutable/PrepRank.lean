import EndgameChess.Rules.KRKExecutable.Prep

/-!
A computable, phase-local centralisation rank. NOT the noncomputable
`KRKStrategy.strategyRank`, and not a complete KRK game-theoretic rank.
-/
namespace EndgameChess.Rules.KRKExecutable
open EndgameChess.KK EndgameChess.Rules.KRKCentral

def prepMarginDebt (rs wk : Square) : Nat :=
  if 2 ≤ absDiff rs.1.val wk.1.val then 0 else 1

def prepRank (sk rs wk : Square) : Nat :=
  2 * prepDistance rs.2.val sk + prepMarginDebt rs wk

/-- Zero rank is exactly READY's margin and prepDistance precondition. -/
theorem prepRank_zero_iff {sk rs wk : Square} :
    prepRank sk rs wk = 0 ↔
    prepDistance rs.2.val sk = 0 ∧ 2 ≤ absDiff rs.1.val wk.1.val := by
  by_cases h : 2 ≤ absDiff rs.1.val wk.1.val
  · simp only [prepRank, prepMarginDebt, if_pos h, Nat.add_zero]
    omega
  · simp only [prepRank, prepMarginDebt, if_neg h]
    omega

/-- Every prepared king action reduces the rank after ANY new weak-king file. -/
theorem prepRank_king_drop {sk su rs wk t : Square}
    (hstep : prepDistance rs.2.val su + 1 = prepDistance rs.2.val sk)
    (hmargin : 2 ≤ absDiff rs.1.val wk.1.val) :
    prepRank su rs t < prepRank sk rs wk := by
  by_cases hafter : 2 ≤ absDiff rs.1.val t.1.val
  · simp only [prepRank, prepMarginDebt, if_pos hmargin, if_pos hafter,
      Nat.add_zero]
    omega
  · simp only [prepRank, prepMarginDebt, if_pos hmargin, if_neg hafter]
    omega

/-- Any rook tempo that repairs the margin without moving the wall rank
strictly reduces the same rank, regardless of the defender's move. -/
theorem prepRank_repair_drop {sk rs nr wk t : Square}
    (hnear : ¬ 2 ≤ absDiff rs.1.val wk.1.val)
    (hrank : nr.2 = rs.2)
    (hfar : 2 ≤ absDiff nr.1.val t.1.val) :
    prepRank sk nr t < prepRank sk rs wk := by
  have sameRank : nr.2.val = rs.2.val := congrArg Fin.val hrank
  simp only [prepRank, prepMarginDebt, if_neg hnear, if_pos hfar, Nat.add_zero]
  rw [sameRank]
  omega

end EndgameChess.Rules.KRKExecutable
