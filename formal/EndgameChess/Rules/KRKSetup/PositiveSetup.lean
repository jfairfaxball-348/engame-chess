import EndgameChess.Rules.KRKSetup.BackRank
namespace EndgameChess.Rules
open EndgameChess.KK
variable {B : Nat}
set_option maxHeartbeats 3000000

theorem setup_positive_budget {q : Position} {σ : Colour} {sk rs wk : Square}
    (hwall : KRKWallBudget σ B)
    (hq : Matches q σ ⟨sk, rs, wk, true⟩)
    (hg : sk.2.val + 2 ≤ wk.2.val) (hn : ¬ RookSees rs wk sk wk) : MateWithin σ (B + 4) q := by
  by_cases hy : rs.2.val = sk.2.val
  · by_cases hpos : 0 < sk.2.val
    · exact mateWithin_mono (setup_same_rank_budget hwall hq hg hy hpos hn) (by omega)
    have hs : sk.2.val = 0 := by omega
    have hr : rs.2.val = 0 := by omega
    have hw : 2 ≤ wk.2.val := by omega
    by_cases hf : 2 ≤ absDiff rs.1.val wk.1.val
    · apply mateWithin_mono (setup_clear_entry_budget hwall hq hg (Or.inl ?_) hf) (by omega)
      have hh := ne_iff_coords.1 hq.1.1
      dsimp only at hh
      omega
    by_cases hx : 2 ≤ absDiff sk.1.val wk.1.val
    · let g : BoardSym := if sk.1.val + 2 ≤ wk.1.val then symSwap else symAnti
      have hgap : (g.f sk).2.val + 2 ≤ (g.f wk).2.val := by
        dsimp [g]; split
        · assumption
        · simp only [symAnti, absDiff] at *; omega
      have hoff : (g.f rs).2.val ≠ (g.f sk).2.val := by
        have hh := ne_iff_coords.1 hq.1.1
        dsimp only at hh
        dsimp [g]; split <;> simp only [symSwap, symAnti] <;> omega
      have hc : Matches (krkPos σ (g.f sk) (g.f rs) (g.f wk) σ) σ
          ((⟨sk, rs, wk, true⟩ : KRKState).map g) :=
        ⟨⟨g.ne_iff.2 hq.1.1, g.ne_iff.2 hq.1.2.1, g.ne_iff.2 hq.1.2.2.1, rfl⟩, rfl⟩
      apply krk_bound_transport g hc rfl
      · simpa only [KRKState.map_map] using hq
      · exact setup_offrank_budget hwall hc hgap hoff (by rwa [g.sees_iff])
    · exact setup_backrank_budget hwall hq hs hr hw (by omega) (by omega) hn
  · exact setup_offrank_budget hwall hq hg hy hn
end EndgameChess.Rules
