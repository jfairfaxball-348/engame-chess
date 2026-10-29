import EndgameChess.Rules.KQK.Symmetry
import EndgameChess.Rules.KQK.Prison

namespace EndgameChess.Rules.KQK
open EndgameChess.KK

/-- Use a canonical reflected board to prove a bound for the original board.
The transformation concerns geometry and board strategies only. -/
theorem unframe_bound (g : QueenSym) {q : Position} {σ : Colour}
    {sk qs wk : Square} {n : Nat} (hq : IsKQK q σ sk qs wk)
    (win : MateWithin σ n (pos σ (g.f sk) (g.f qs) (g.f wk) q.turn)) :
    MateWithin σ n q := by
  have source : IsKQK (pos σ (g.f sk) (g.f qs) (g.f wk) q.turn)
      σ (g.f sk) (g.f qs) (g.f wk) :=
    ⟨g.toBoardSym.ne_iff.mpr hq.1,g.toBoardSym.ne_iff.mpr hq.2.1,
      g.toBoardSym.ne_iff.mpr hq.2.2.1,rfl⟩
  have target : IsKQK q σ (g.f (g.f sk)) (g.f (g.f qs)) (g.f (g.f wk)) := by
    simpa only [g.invol] using hq
  exact bound_transport g source rfl target rfl win

theorem framed_edge_wall_bound (g : QueenSym) {q : Position} {σ : Colour}
    {sk qs wk : Square} (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (he : EdgeWall (g.f sk) (g.f qs) (g.f wk)) : MateWithin σ 25 q := by
  apply unframe_bound g hq
  apply edge_wall_twenty_five
  · exact ⟨g.toBoardSym.ne_iff.mpr hq.1,g.toBoardSym.ne_iff.mpr hq.2.1,
      g.toBoardSym.ne_iff.mpr hq.2.2.1,rfl⟩
  · exact ht
  · exact he

theorem framed_prison_bound (g : QueenSym) {q : Position} {σ : Colour}
    {sk qs wk : Square} (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (hp : Prison (g.f qs) (g.f wk)) (hfar : 2 ≤ dInf sk wk) :
    MateWithin σ 21 q := by
  apply unframe_bound g hq
  apply prison_bound
  · exact ⟨g.toBoardSym.ne_iff.mpr hq.1,g.toBoardSym.ne_iff.mpr hq.2.1,
      g.toBoardSym.ne_iff.mpr hq.2.2.1,rfl⟩
  · exact ht
  · exact hp
  · rwa [g.dInf_eq]

end EndgameChess.Rules.KQK
