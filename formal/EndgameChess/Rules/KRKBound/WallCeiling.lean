import EndgameChess.Rules.KRKBound.Wall
namespace EndgameChess.Rules
open EndgameChess.KK

theorem krk_wall_ceiling {q : Position} {σ : Colour} {sk rs wk : Square}
    (hq : Matches q σ ⟨sk, rs, wk, true⟩)
    (hb : sk.2.val < rs.2.val) (hw : rs.2.val < wk.2.val) :
    MateWithin σ 504 q := by
  exact mateWithin_mono (krk_rank_wall_bound hq hb hw) (by omega)
end EndgameChess.Rules
