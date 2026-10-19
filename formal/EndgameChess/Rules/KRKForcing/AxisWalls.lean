import EndgameChess.Rules.KRKForcing.StrategyTransport
import EndgameChess.Rules.KRKForcing.WallEntry

/-! S030 / EC-C020: winning walls in either coordinate and direction. -/
namespace EndgameChess.Rules
open EndgameChess.KK

def symSwap : BoardSym where
  f s := (s.2, s.1)
  invol _ := rfl
  dInf_eq s t := by simp only [dInf, absDiff]; omega
  line_iff s t := by simp only [RookLine]; omega
  seg_iff s r t := by simp only [OnSeg]; omega

def symAnti : BoardSym where
  f s := (⟨7 - s.2.val, by omega⟩, ⟨7 - s.1.val, by omega⟩)
  invol s := by rw [square_eq_iff]; dsimp only; omega
  dInf_eq s t := by simp only [dInf, absDiff]; omega
  line_iff s t := by simp only [RookLine]; omega
  seg_iff s r t := by simp only [OnSeg]; omega

private theorem canonical_matches (g : BoardSym) {q : Position} {σ : Colour}
    {sk rs wk : Square} (hq : Matches q σ ⟨sk, rs, wk, true⟩) :
    Matches (krkPos σ (g.f sk) (g.f rs) (g.f wk) σ) σ
      ((⟨sk, rs, wk, true⟩ : KRKState).map g) := by
  exact ⟨⟨g.ne_iff.2 hq.1.1, g.ne_iff.2 hq.1.2.1,
    g.ne_iff.2 hq.1.2.2.1, rfl⟩, rfl⟩

/-- The S029 wall wins after any proved involutive rook/king isometry. -/
theorem krk_axis_wall_force (g : BoardSym) {q : Position} {σ : Colour}
    {sk rs wk : Square} (hq : Matches q σ ⟨sk, rs, wk, true⟩)
    (hb : (g.f sk).2.val < (g.f rs).2.val)
    (hw : (g.f rs).2.val < (g.f wk).2.val) : ForceMate σ q := by
  have hc := canonical_matches g hq
  apply krk_force_transport g hc rfl
  · simpa only [KRKState.map_map] using hq
  · exact krk_rank_wall_force hc hb hw

/-- The direct distant-entry family also transports with every reply. -/
theorem krk_axis_entry_force (g : BoardSym) {q : Position} {σ : Colour}
    {sk rs wk : Square} (hq : Matches q σ ⟨sk, rs, wk, true⟩)
    (hgap : (g.f sk).2.val + 2 ≤ (g.f wk).2.val)
    (hx : (g.f rs).1.val ≠ (g.f sk).1.val)
    (hf : 2 ≤ absDiff (g.f rs).1.val (g.f wk).1.val) : ForceMate σ q := by
  have hc := canonical_matches g hq
  apply krk_force_transport g hc rfl
  · simpa only [KRKState.map_map] using hq
  · exact krk_vertical_wall_entry_force hc hgap hx hf

/-- Any separated pair has a positive rank gap of two in one of four frames. -/
theorem krk_setup_axis {sk wk : Square} (hd : 2 ≤ dInf sk wk) :
    ∃ g : BoardSym, (g = symId ∨ g = symY ∨ g = symSwap ∨ g = symAnti) ∧
      (g.f sk).2.val + 2 ≤ (g.f wk).2.val := by
  by_cases hu : sk.2.val + 2 ≤ wk.2.val
  · exact ⟨symId, Or.inl rfl, hu⟩
  by_cases hl : wk.2.val + 2 ≤ sk.2.val
  · exact ⟨symY, Or.inr (Or.inl rfl), by simp only [symY]; omega⟩
  by_cases hr : sk.1.val + 2 ≤ wk.1.val
  · exact ⟨symSwap, Or.inr (Or.inr (Or.inl rfl)), hr⟩
  refine ⟨symAnti, Or.inr (Or.inr (Or.inr rfl)), ?_⟩
  simp only [symAnti, dInf, absDiff] at *
  omega

/-- Facts justified by a kernel arrival, without a global reachability assumption. -/
theorem krk_strong_arrival_geometry {p q : Position} {σ : Colour} {sk rs wk : Square}
    (hl : Legal p q) (hk : IsKRK q σ sk rs wk) (ht : q.turn = σ) :
    2 ≤ dInf sk wk ∧ ¬ RookSees rs wk sk wk := by
  have hp : p.turn = σ.opp := by rw [← ht, turn_of_legal hl, opp_opp]
  have hc := legal_mover_safe hl
  rw [hp] at hc
  have hn : ¬ (dInf sk wk = 1 ∨ RookSees rs wk sk wk) := by
    intro h
    rw [(inCheck_weak_krk hk.1 hk.2.1 hk.2.2.1 hk.2.2.2).2 h] at hc
    cases hc
  have h0 : dInf sk wk ≠ 0 := fun h => hk.2.1 (dInf_eq_zero_iff.1 h)
  exact ⟨by have := fun h => hn (Or.inl h); omega, fun h => hn (Or.inr h)⟩

end EndgameChess.Rules
