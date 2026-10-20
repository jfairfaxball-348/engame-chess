import EndgameChess.Rules.KRKBound.OffRank
namespace EndgameChess.Rules
open EndgameChess.KK
set_option maxHeartbeats 3000000

theorem bound_weak_wall {q : Position} {σ : Colour} {sk rs wk : Square}
    (hm : Matches q σ ⟨sk, rs, wk, false⟩)
    (hb : sk.2.val < rs.2.val) (hw : rs.2.val < wk.2.val)
    (hs : SafeRook sk rs wk) (hne : ∃ r, Legal q r) : MateWithin σ 505 q := by
  apply mateWithin_defend hm.2 hne
  intro r hr
  obtain ⟨t, ht, _, hbar⟩ := krk_safe_rank_reply hm.1 hm.2 hs hb hw hr
  exact krk_wall_ceiling ht hb hbar
end EndgameChess.Rules
