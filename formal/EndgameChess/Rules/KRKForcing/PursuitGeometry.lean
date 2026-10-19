import EndgameChess.Rules.KRKForcing.WallActions

/-! Symbolic file arithmetic for bounded two-tempo normalization. -/
namespace EndgameChess.Rules
open EndgameChess.KK

theorem pursuit_tempo_return_margin (d : Bool) {sk wk t : Square} {rs : Fin 8}
    (hx : pursuitFile d wk = pursuitFile d sk + 2)
    (ht : pursuitFile d t = pursuitFile d sk + 1)
    (hr : rs = wallFarFile wk.1) :
    3 ≤ absDiff (wallWaitFile rs t.1).val wk.1.val := by
  subst hr
  cases d <;> simp only [pursuitFile, Bool.false_eq_true, ↓reduceIte] at hx ht
  all_goals
    by_cases hw : 4 ≤ wk.1.val
    · by_cases ht' : 4 ≤ t.1.val
      · simp +decide [wallFarFile, wallWaitFile, hw, ht', absDiff]; omega
      · simp +decide [wallFarFile, wallWaitFile, hw, ht', absDiff]; omega
    · by_cases ht' : 4 ≤ t.1.val
      · simp +decide [wallFarFile, wallWaitFile, hw, ht', absDiff]; omega
      · simp +decide [wallFarFile, wallWaitFile, hw, ht', absDiff]; omega

end EndgameChess.Rules
