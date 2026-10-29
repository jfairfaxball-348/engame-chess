import EndgameChess.Rules.KRKExecutable.ReadyUpper

/-!
Executable proof-directed wall-climb dispatch. This operates ONLY when the
strong side already has a strict oriented rook wall. The `none` branch is a
narrow-band HANDOFF, not a drawn or won terminal verdict. The later protected
cut/guarded phase remains to be extracted.
-/
namespace EndgameChess.Rules.KRKExecutable
open EndgameChess.KK EndgameChess.Rules.KRKCentral

/-- A fixed coordinate choice, with NO search and NO classical choice. -/
def wallNext (sk rs wk : Square) : Option (Square × Square) :=
  if 0 < prepRank sk rs wk then
    some (prepNext sk rs wk)
  else if h : rs.2.val + 2 ≤ wk.2.val then
    some (sk, rankAdvanceDestination rs (by omega))
  else
    none

/-- For every non-handoff strong-turn oriented wall, `wallNext` provides
a concrete legal move and every legal weak reply has strictly smaller
wallPotential and still lies above the rook wall. -/
theorem wallNext_sound {q : Position} {σ : Colour}
    {sk rs wk : Square}
    (hq : Matches q σ ⟨sk, rs, wk, true⟩)
    (hb : sk.2.val < rs.2.val)
    (hw : rs.2.val < wk.2.val)
    (ha : wallNext sk rs wk ≠ none) :
    ∃ c su nr, wallNext sk rs wk = some (su, nr) ∧
      Legal q c ∧ Matches c σ ⟨su, nr, wk, false⟩ ∧
      (∃ v, Legal c v) ∧
      ∀ v, Legal c v →
        ∃ t, Matches v σ ⟨su, nr, t, true⟩ ∧
          nr.2.val < t.2.val ∧
          wallPotential su nr t < wallPotential sk rs wk := by
  by_cases hpositive : 0 < prepRank sk rs wk
  · obtain ⟨c, hl, hm, hne, hall⟩ :=
      prepNext_sound hq hb hw hpositive
    have hrank : (prepNext sk rs wk).2.2.val = rs.2.val := by
      unfold prepNext
      split <;> rfl
    refine ⟨c, (prepNext sk rs wk).1, (prepNext sk rs wk).2,
      by simp [wallNext, hpositive], hl, hm, hne, ?_⟩
    intro v hv
    obtain ⟨t, hmt, hyt, hdrop⟩ := hall v hv
    have htotal : wallPotential (prepNext sk rs wk).1
        (prepNext sk rs wk).2 t < wallPotential sk rs wk := by
      simp only [wallPotential]
      rw [hrank]
      omega
    exact ⟨t, hmt, hyt, htotal⟩
  · have hzero : prepRank sk rs wk = 0 := by omega
    obtain ⟨hprep, hmargin⟩ := (prepRank_zero_iff).mp hzero
    have hsy : sk.2.val + 1 = rs.2.val := by
      simp only [prepDistance] at hprep
      omega
    have hc : sk.1.val = 3 ∨ sk.1.val = 4 := by
      unfold prepDistance centreDistance at hprep
      split_ifs at hprep <;> omega
    by_cases hgap : rs.2.val + 2 ≤ wk.2.val
    · obtain ⟨c, hl, hm, hne, hall⟩ :=
        readyUpperDestination_sound hq hsy hgap hc hmargin
      refine ⟨c, sk, rankAdvanceDestination rs (by omega),
        by simp [wallNext, hpositive, hgap], hl, hm, hne, ?_⟩
      intro v hv
      exact hall v hv
    · have hnone : wallNext sk rs wk = none := by
        simp [wallNext, hpositive, hgap]
      exact False.elim (ha hnone)

end EndgameChess.Rules.KRKExecutable
