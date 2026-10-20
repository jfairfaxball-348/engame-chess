import EndgameChess.Rules.KRKBound.WeakWall
namespace EndgameChess.Rules
open EndgameChess.KK
set_option maxHeartbeats 3000000
theorem bound_same_rank_no_file {sk rs wk : Square}
    (hneq : sk ≠ rs) (hrow : rs.2.val = sk.2.val)
    (hg : sk.2.val + 2 ≤ wk.2.val) (hn : ¬ RookSees rs wk sk wk) :
    rs.1.val ≠ wk.1.val := by
  intro e
  apply hn
  refine ⟨⟨?_, Or.inl e⟩, ?_, not_onSeg_end _ _⟩
  · omega
  · have hh := ne_iff_coords.1 hneq
    simp only [OnSeg] at *; omega

end EndgameChess.Rules
