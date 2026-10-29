import EndgameChess.Rules.KRKExecutable.PrepRank
import EndgameChess.Rules.KRKExecutable.Constructors

/-!
A concrete, total-on-its-domain controller for KRK wall preparation.
This is NOT a full KRK mating strategy: READY is a handoff, not checkmate.
-/
namespace EndgameChess.Rules.KRKExecutable
open EndgameChess.KK EndgameChess.Rules.KRKCentral

/-- Exact king/rook coordinates selected by the preparation controller.
The branch is determined solely by the rook/weak king file margin. -/
def prepNext (sk rs wk : Square) : Square × Square :=
  if 2 ≤ absDiff rs.1.val wk.1.val then
    (prepDestination sk rs, rs)
  else
    (sk, (wallFarFile wk.1, rs.2))

/-- A positive preparation rank admits this concrete, computable first
move. Every *actual legal weak reply* preserves the wall and decreases
prepRank strictly. The result is not a 97/98-ply mate policy. -/
theorem prepNext_sound {q : Position} {σ : Colour} {sk rs wk : Square}
    (hq : Matches q σ ⟨sk, rs, wk, true⟩)
    (hb : sk.2.val < rs.2.val) (hw : rs.2.val < wk.2.val)
    (hpositive : 0 < prepRank sk rs wk) :
    ∃ c, Legal q c ∧
      Matches c σ ⟨(prepNext sk rs wk).1, (prepNext sk rs wk).2, wk, false⟩ ∧
      (∃ v, Legal c v) ∧
      ∀ v, Legal c v →
        ∃ t, Matches v σ ⟨(prepNext sk rs wk).1,
          (prepNext sk rs wk).2, t, true⟩ ∧
          (prepNext sk rs wk).2.2.val < t.2.val ∧
          prepRank (prepNext sk rs wk).1 (prepNext sk rs wk).2 t <
            prepRank sk rs wk := by
  by_cases hmargin : 2 ≤ absDiff rs.1.val wk.1.val
  · have hn : 0 < prepDistance rs.2.val sk := by
      simp only [prepRank, prepMarginDebt, if_pos hmargin,
        Nat.add_zero] at hpositive
      omega
    obtain ⟨c, hl, hm, hdrop, hne, hall⟩ :=
      prepDestination_sound hq hb hw hn hmargin
    have hnxt : prepNext sk rs wk = (prepDestination sk rs, rs) := by
      simp only [prepNext, if_pos hmargin]
    rw [hnxt]
    refine ⟨c, hl, hm, hne, ?_⟩
    intro v hv
    obtain ⟨t, hmt, hyt⟩ := hall v hv
    exact ⟨t, hmt, hyt, prepRank_king_drop hdrop hmargin⟩
  · let nr : Square := (wallFarFile wk.1, rs.2)
    have hfar : 4 ≤ absDiff nr.1.val wk.1.val := wall_far_margin wk.1
    have hdistinct : nr ≠ rs := by
      intro he
      have hf : nr.1.val = rs.1.val := congrArg (fun x : Square => x.1.val) he
      simp only [hf] at hfar
      omega
    obtain ⟨c, hl, hm, hne, hall⟩ :=
      krk_wall_rook_move hq hb hw (nr := nr) rfl hdistinct (by omega)
    have hnxt : prepNext sk rs wk = (sk, nr) := by
      simp only [prepNext, if_neg hmargin, nr]
    rw [hnxt]
    refine ⟨c, hl, hm, hne, ?_⟩
    intro v hv
    obtain ⟨t, hmt, hyt, hfile, _⟩ := hall v hv
    exact ⟨t, hmt, hyt, prepRank_repair_drop hmargin rfl hfile⟩

end EndgameChess.Rules.KRKExecutable
