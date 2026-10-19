import EndgameChess.Rules.KRKForcing.SameRankSetup

/-! S030 / EC-C021: arbitrary strong-turn legal-arrival KRK forcing. -/
namespace EndgameChess.Rules
open EndgameChess.KK
set_option maxHeartbeats 2000000

private theorem positive_setup_force {q : Position} {σ : Colour} {sk rs wk : Square}
    (hq : Matches q σ ⟨sk, rs, wk, true⟩)
    (hg : sk.2.val + 2 ≤ wk.2.val) (hn : ¬ RookSees rs wk sk wk) : ForceMate σ q := by
  by_cases hy : rs.2.val = sk.2.val
  · by_cases hpos : 0 < sk.2.val
    · exact krk_same_rank_retreat_force hq hg hy hpos hn
    have hs : sk.2.val = 0 := by omega
    have hr : rs.2.val = 0 := by omega
    have hw : 2 ≤ wk.2.val := by omega
    by_cases hf : 2 ≤ absDiff rs.1.val wk.1.val
    · apply krk_clear_vertical_entry_force hq hg (Or.inl ?_) hf
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
      apply krk_force_transport g hc rfl
      · simpa only [KRKState.map_map] using hq
      · exact krk_offrank_setup_force hc hgap hoff (by rwa [g.sees_iff])
    · exact krk_backrank_setup_force hq hs hr hw (by omega) (by omega) hn
  · exact krk_offrank_setup_force hq hg hy hn

/-- Clock-free KRK wins on the strong turn whenever the lone king is not in
check. The setup strategy is finite and covers every legal defending reply. -/
theorem krk_strong_force_of_not_check {q : Position} {σ : Colour} {sk rs wk : Square}
    (hk : IsKRK q σ sk rs wk) (ht : q.turn = σ)
    (hc : inCheck q σ.opp = false) : ForceMate σ q := by
  have hn : ¬ (dInf sk wk = 1 ∨ RookSees rs wk sk wk) := by
    intro h
    rw [(inCheck_weak_krk hk.1 hk.2.1 hk.2.2.1 hk.2.2.2).2 h] at hc
    cases hc
  have h0 : dInf sk wk ≠ 0 := fun h => hk.2.1 (dInf_eq_zero_iff.1 h)
  have hd : 2 ≤ dInf sk wk := by have := fun h => hn (Or.inl h); omega
  obtain ⟨g, _, hg⟩ := krk_setup_axis hd
  have hq : Matches q σ ⟨sk, rs, wk, true⟩ := ⟨hk, ht⟩
  have hcanon : Matches (krkPos σ (g.f sk) (g.f rs) (g.f wk) σ) σ
      ((⟨sk, rs, wk, true⟩ : KRKState).map g) :=
    ⟨⟨g.ne_iff.2 hk.1, g.ne_iff.2 hk.2.1, g.ne_iff.2 hk.2.2.1, rfl⟩, rfl⟩
  apply krk_force_transport g hcanon rfl
  · simpa only [KRKState.map_map] using hq
  · apply positive_setup_force hcanon hg
    rw [g.sees_iff]
    exact fun h => hn (Or.inr h)

/-- Any exact strong-turn KRK produced by a kernel-legal move forces mate,
for either colour and arbitrary flags. No clock/repetition or distance claim. -/
theorem krk_strong_arrival_force {q : Position} {σ : Colour} {sk rs wk : Square}
    (hk : IsKRK q σ sk rs wk) (ht : q.turn = σ)
    (ha : ∃ p, Legal p q) : ForceMate σ q := by
  obtain ⟨p, hl⟩ := ha
  have hp : p.turn = σ.opp := by rw [← ht, turn_of_legal hl, opp_opp]
  have hc := legal_mover_safe hl
  rw [hp] at hc
  exact krk_strong_force_of_not_check hk ht hc

end EndgameChess.Rules
