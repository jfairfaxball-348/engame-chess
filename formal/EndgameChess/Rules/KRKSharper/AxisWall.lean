import EndgameChess.Rules.KRKBound.Transport
import EndgameChess.Rules.KRKSharper.Wall
namespace EndgameChess.Rules
open EndgameChess.KK
private theorem canonical_matches (g : BoardSym) {q : Position} {σ : Colour}
    {sk rs wk : Square} (hq : Matches q σ ⟨sk, rs, wk, true⟩) :
    Matches (krkPos σ (g.f sk) (g.f rs) (g.f wk) σ) σ
      ((⟨sk, rs, wk, true⟩ : KRKState).map g) := by
  exact ⟨⟨g.ne_iff.2 hq.1.1, g.ne_iff.2 hq.1.2.1,
    g.ne_iff.2 hq.1.2.2.1, rfl⟩, rfl⟩

/-- The credited coordinate wall budget is preserved after any proved involutive rook/king isometry. -/
theorem krk_axis_wall_bound_sharper (g : BoardSym) {q : Position} {σ : Colour}
    {sk rs wk : Square} (hq : Matches q σ ⟨sk, rs, wk, true⟩)
    (hb : (g.f sk).2.val < (g.f rs).2.val)
    (hw : (g.f rs).2.val < (g.f wk).2.val) : MateWithin σ (73 * (7 - (g.f rs).2.val)) q := by
  have hc := canonical_matches g hq
  apply krk_bound_transport g hc rfl
  · simpa only [KRKState.map_map] using hq
  · exact krk_rank_wall_bound_sharper hc hb hw

end EndgameChess.Rules
