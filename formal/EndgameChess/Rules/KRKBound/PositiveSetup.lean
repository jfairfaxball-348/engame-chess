import EndgameChess.Rules.KRKBound.BackRank
namespace EndgameChess.Rules
open EndgameChess.KK
set_option maxHeartbeats 3000000

theorem positive_setup_bound {q : Position} {σ : Colour} {sk rs wk : Square}
    (hq : Matches q σ ⟨sk, rs, wk, true⟩)
    (hg : sk.2.val + 2 ≤ wk.2.val) (hn : ¬ RookSees rs wk sk wk) : MateWithin σ 508 q := by
  by_cases hy : rs.2.val = sk.2.val
  · by_cases hpos : 0 < sk.2.val
    · exact mateWithin_mono (krk_same_rank_retreat_bound hq hg hy hpos hn) (by decide)
    have hs : sk.2.val = 0 := by omega
    have hr : rs.2.val = 0 := by omega
    have hw : 2 ≤ wk.2.val := by omega
    by_cases hf : 2 ≤ absDiff rs.1.val wk.1.val
    · apply mateWithin_mono (krk_clear_vertical_entry_bound hq hg (Or.inl ?_) hf) (by decide)
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
      · exact krk_offrank_setup_bound hc hgap hoff (by rwa [g.sees_iff])
    · exact krk_backrank_setup_bound hq hs hr hw (by omega) (by omega) hn
  · exact krk_offrank_setup_bound hq hg hy hn
end EndgameChess.Rules
