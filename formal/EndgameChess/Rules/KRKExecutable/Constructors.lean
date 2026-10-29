import EndgameChess.Rules.KRKForcing.WallActions
import EndgameChess.Rules.KRKForcing.RankAdvance

/-!
KRK01 constructive extraction (new non-frozen module).

These coordinate functions are computable: no Classical.choose, abstract rank,
minimax, tablebase, or board enumeration. They package the **specific** moves
already verified by frozen KRK theorems, and DO NOT form a total KRK policy.
-/
namespace EndgameChess.Rules.KRKExecutable
open EndgameChess.KK

/-- Executable rook destination of the frozen all-reply wall-tempo lemma. -/
def rookWaitDestination (rs wk : Square) : Square :=
  (wallWaitFile rs.1 wk.1, rs.2)

/-- The executable coordinate, not an existentially chosen rook move,
preserves the wall after every actual legal weak reply. -/
theorem rookWaitDestination_sound {q : Position} {σ : Colour}
    {sk rs wk : Square}
    (hq : Matches q σ ⟨sk, rs, wk, true⟩)
    (hb : sk.2.val < rs.2.val) (hw : rs.2.val < wk.2.val) :
    ∃ c, Legal q c ∧
      Matches c σ ⟨sk, rookWaitDestination rs wk, wk, false⟩ ∧
      (∃ r, Legal c r) ∧
      ∀ r, Legal c r →
        ∃ t, Matches r σ ⟨sk, rookWaitDestination rs wk, t, true⟩ ∧
          rs.2.val < t.2.val := by
  have choice := wall_wait_choice rs.1 wk.1
  have diff : rookWaitDestination rs wk ≠ rs := by
    intro same
    have hf : wallWaitFile rs.1 wk.1 = rs.1 := congrArg Prod.fst same
    exact choice.1 hf
  obtain ⟨c, hl, hm, hne, hall⟩ :=
    krk_wall_rook_move hq hb hw (nr := rookWaitDestination rs wk)
      rfl diff choice.2
  refine ⟨c, hl, hm, hne, ?_⟩
  intro r hr
  obtain ⟨t, ht, hwall, _⟩ := hall r hr
  exact ⟨t, ht, hwall⟩

/-- Executable upward rook target at a certified rank wall. -/
def rankAdvanceDestination (rs : Square) (h : rs.2.val < 7) : Square :=
  (rs.1, ⟨rs.2.val + 1, by omega⟩)

/-- The concrete rook-up move decreases its physical wall rank and every
legal defender reply retains the frozen distant-barrier postcondition. -/
theorem rankAdvanceDestination_sound {q : Position} {σ : Colour}
    {sk rs wk : Square}
    (hk : IsKRK q σ sk rs wk) (ht : q.turn = σ)
    (hb : sk.2.val < rs.2.val)
    (hw : rs.2.val + 2 ≤ wk.2.val)
    (hf : 3 ≤ absDiff rs.1.val wk.1.val) :
    ∃ c, Legal q c ∧
      Matches c σ ⟨sk, rankAdvanceDestination rs (by omega), wk, false⟩ ∧
      7 - (rankAdvanceDestination rs (by omega)).2.val < 7 - rs.2.val ∧
      (∃ v, Legal c v) ∧
      ∀ v, Legal c v →
        ∃ t, Matches v σ ⟨sk, rankAdvanceDestination rs (by omega), t, true⟩ ∧
          DistantBarrier sk (rankAdvanceDestination rs (by omega)) t := by
  obtain ⟨nr, c, hfile, hrank, legal, matches, nonempty, drop, replies⟩ :=
    krk_rank_advance hk ht hb hw hf
  have equal : nr = rankAdvanceDestination rs (by omega) := by
    apply Prod.ext
    · apply Fin.ext
      exact hfile
    · apply Fin.ext
      exact hrank
  subst nr
  exact ⟨c, legal, matches, drop, nonempty, replies⟩

end EndgameChess.Rules.KRKExecutable
