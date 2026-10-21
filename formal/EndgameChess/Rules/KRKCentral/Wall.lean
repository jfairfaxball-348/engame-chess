import EndgameChess.Rules.KRKCentral.Prep

namespace EndgameChess.Rules.KRKCentral
open EndgameChess.KK
set_option maxHeartbeats 4000000

/-- Uniform93-ply bound for EVERY exact strong-turn strict KRK rank wall,
both colours, arbitrary kernel flags and every actual defensive reply. -/
theorem wall93 {σ : Colour} {q : Position} {sk rs wk : Square}
    (hq : Matches q σ ⟨sk,rs,wk,true⟩)
    (hb : sk.2.val<rs.2.val) (hw : rs.2.val<wk.2.val) :
    MateWithin σ 93 q := by
  have hd : centreDistance sk.1.val≤3 := by
    unfold centreDistance; split <;> (try split) <;> omega
  have ht : prepDistance rs.2.val sk≤max (rs.2.val-1) 3 := by
    unfold prepDistance; omega
  apply mateWithin_mono (prep_bound hq hb hw)
  simp only [readyCost,prepCost]
  split <;> omega

end EndgameChess.Rules.KRKCentral
