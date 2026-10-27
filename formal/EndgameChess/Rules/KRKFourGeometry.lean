import EndgameChess.Rules.KRKFramedHistory
import EndgameChess.Rules.KRKFourPlyCornerKernel
import EndgameChess.Rules.KRKInteriorLowerBound

namespace EndgameChess.Rules.KRKFourGeometry
open EndgameChess.KK KRKThreePly KRKLastReply KRKMateGeometry KRKNativeFrame
set_option maxHeartbeats 500000

theorem three_map (g : Frame) {sk rs wk : Square} (three : Three sk rs wk) :
    Three (g.f sk) (g.f rs) (g.f wk) := by
  rcases three with now | ⟨t, distance, apart, far, last⟩ | ⟨t, sees, king, weak, last⟩
  · exact Or.inl ((g.immediate _ _ _).mpr now)
  · exact Or.inr (Or.inl ⟨g.f t, by rwa [g.distance], g.ne_iff.mpr apart,
      by rwa [g.distance], (g.last _ _ _).mpr last⟩)
  · exact Or.inr (Or.inr ⟨g.f t, (g.sees _ _ _ _).mpr sees,
      g.ne_iff.mpr king, g.ne_iff.mpr weak, (g.last _ _ _).mpr last⟩)

theorem three_iff (g : Frame) {sk rs wk : Square} :
    Three (g.f sk) (g.f rs) (g.f wk) ↔ Three sk rs wk := by
  constructor
  · intro three
    simpa only [Frame.inverse, g.left_inv] using three_map g.inverse three
  · exact three_map g

/-- Canonical nonterminal four-ply destination regions. Middle edge files
use the last-reply slots or direct opposition with a rook at least three ranks inward. -/
def Shape (sk rs wk : Square) : Prop :=
  (wk.1.val = 0 ∧ KRKFourPlyCorner.CornerFour sk rs) ∨
  (wk.1.val = 1 ∧ KRKFourPlyNearCorner.NearFour sk rs) ∨
  (2 ≤ wk.1.val ∧ wk.1.val ≤ 3 ∧
    (LastReply sk rs wk ∨ (sk.1.val = wk.1.val ∧ sk.2.val = 2 ∧ 3 ≤ rs.2.val)))

private theorem canonical_shape_iff {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp)
    (far : 2 ≤ dInf sk wk) (rank : wk.2.val = 0) (high : wk.1.val ≤ 3)
    (notMate : ¬MatedK q) (nonempty : ∃ r, Legal q r) :
    MateWithin σ 4 q ↔ Shape sk rs wk := by
  by_cases corner : wk.1.val = 0
  · simpa [Shape, corner, notMate, nonempty] using
      (KRKFourPlyCorner.weak_four_iff material turn far corner rank)
  by_cases near : wk.1.val = 1
  · simpa [Shape, near, notMate, nonempty] using
      (KRKFourPlyNearCorner.weak_four_iff material turn far near rank)
  have low : 2 ≤ wk.1.val := by omega
  have classification : MateWithin σ 4 q ↔ MatedK q ∨ LastReply sk rs wk ∨
      (sk.1.val = wk.1.val ∧ sk.2.val = 2 ∧ 3 ≤ rs.2.val) := by
    by_cases second : wk.1.val = 2
    · exact KRKFourPlySecond.weak_four_iff material turn far rank second
    · exact KRKFourPlyMiddle.weak_four_iff material turn far rank (by omega) (by omega)
  simpa only [Shape, corner, near, low, high, notMate, false_and, false_or, true_and] using classification

/-- Transport only the weak reply geometry and its complete three-ply child
regions to a coordinate frame. Actual history and castling flags are not mapped. -/
theorem framed_shape_necessary {q : Position} {σ : Colour} {sk rs wk : Square} (g : Frame)
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp)
    (far : 2 ≤ dInf sk wk) (notMate : ¬MatedK q)
    (rank : (g.f wk).2.val = 0) (high : (g.f wk).1.val ≤ 3)
    (win : MateWithin σ 4 q) : Shape (g.f sk) (g.f rs) (g.f wk) := by
  have safe := krk_force_weak_safe material turn ⟨4, win⟩
  have defended : (∃ r, Legal q r) ∧ ∀ r, Legal q r → MateWithin σ 3 r := by
    rcases win with goal | ⟨_, chosen | defended⟩
    · exact False.elim (notMate goal.2)
    · exact False.elim (opp_ne σ (chosen.1.symm.trans turn))
    · exact defended.2
  obtain ⟨r, legal⟩ := defended.1
  obtain ⟨t, _, step⟩ := krk_safe_reply material turn safe legal
  have mappedStep := g.map_step step
  let p := krkPos σ (g.f sk) (g.f rs) (g.f wk) σ.opp
  have mapped : IsKRK p σ (g.f sk) (g.f rs) (g.f wk) :=
    ⟨g.ne_iff.mpr material.1, g.ne_iff.mpr material.2.1, g.ne_iff.mpr material.2.2.1, rfl⟩
  have matched : Matches p σ ⟨g.f sk, g.f rs, g.f wk, false⟩ := ⟨mapped, rfl⟩
  obtain ⟨v, edge, _⟩ := step_sound matched mappedStep
  have nonempty : ∃ r, Legal p r := ⟨v, edge⟩
  have noMate : ¬MatedK p := fun mate => mate.2 nonempty
  have mappedSafe : SafeRook (g.f sk) (g.f rs) (g.f wk) := by
    simpa only [SafeRook, g.distance] using safe
  have winP : MateWithin σ 4 p := by
    apply mateWithin_defend rfl nonempty
    intro v edge
    obtain ⟨u, next, move⟩ := krk_safe_reply mapped rfl mappedSafe edge
    have back := g.inverse.map_step move
    change StepM ⟨g.r (g.f sk), g.r (g.f rs), g.r (g.f wk), false⟩
      ⟨g.r (g.f sk), g.r (g.f rs), g.r u, true⟩ at back
    simp only [g.left_inv] at back
    obtain ⟨r, legal, nextR⟩ := step_sound (show Matches q σ ⟨sk, rs, wk, false⟩ from ⟨material, turn⟩) back
    obtain ⟨childFar, notCheck⟩ := krk_strong_arrival_geometry legal nextR.1 nextR.2
    have three := (strong_three_iff nextR.1 nextR.2 childFar notCheck).mp (defended.2 r legal)
    have forward : Three (g.f sk) (g.f rs) u := by
      simpa only [g.right_inv] using three_map g three
    obtain ⟨childFarP, notCheckP⟩ := krk_strong_arrival_geometry edge next.1 next.2
    exact (strong_three_iff next.1 next.2 childFarP notCheckP).mpr forward
  exact (canonical_shape_iff mapped rfl (by rwa [g.distance]) rank high noMate nonempty).mp winP

/-- Every nonterminal weak four-ply winning board has an edge weak king
and one of the complete, normalized destination regions. -/
theorem global_shape_necessary {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp)
    (far : 2 ≤ dInf sk wk) (notMate : ¬MatedK q) (win : MateWithin σ 4 q) :
    KRKEdgeDepth.depth wk = 0 ∧ Shape ((normalize wk).f sk) ((normalize wk).f rs) ((normalize wk).f wk) := by
  have depth : KRKEdgeDepth.depth wk = 0 := by
    by_cases zero : KRKEdgeDepth.depth wk = 0
    · exact zero
    · exact False.elim (KRKFourPlyEscape.weak_interior_not_four material turn far (by omega) win)
  have normal := normalize_spec depth
  exact ⟨depth, framed_shape_necessary (normalize wk) material turn far notMate normal.1 normal.2 win⟩


/-- Converse geometric transport for a live weak destination. Actual weak
moves are mapped one at a time; no actual castling flags or trace are mapped. -/
theorem framed_shape_sufficient {q : Position} {σ : Colour} {sk rs wk : Square} (g : Frame)
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp)
    (far : 2 ≤ dInf sk wk) (safe : SafeRook sk rs wk) (nonempty : ∃ r, Legal q r)
    (rank : (g.f wk).2.val = 0) (high : (g.f wk).1.val ≤ 3)
    (shape : Shape (g.f sk) (g.f rs) (g.f wk)) : MateWithin σ 4 q := by
  obtain ⟨r,legal⟩ := nonempty
  obtain ⟨t,_,step⟩ := krk_safe_reply material turn safe legal
  let p := krkPos σ (g.f sk) (g.f rs) (g.f wk) σ.opp
  have mapped : IsKRK p σ (g.f sk) (g.f rs) (g.f wk) :=
    ⟨g.ne_iff.mpr material.1,g.ne_iff.mpr material.2.1,g.ne_iff.mpr material.2.2.1,rfl⟩
  have matched : Matches p σ ⟨g.f sk,g.f rs,g.f wk,false⟩ := ⟨mapped,rfl⟩
  obtain ⟨v,edge,_⟩ := step_sound matched (g.map_step step)
  have live : ∃ r, Legal p r := ⟨v,edge⟩
  have noMate : ¬MatedK p := fun mate => mate.2 live
  have winP := (canonical_shape_iff mapped rfl (by rwa [g.distance]) rank high noMate live).mpr shape
  have all : ∀ r, Legal p r → MateWithin σ 3 r := by
    rcases winP with goal | ⟨_,chosen | defended⟩
    · exact False.elim (noMate goal.2)
    · exact False.elim (opp_ne σ chosen.1.symm)
    · exact defended.2.2
  apply mateWithin_defend turn ⟨r,legal⟩
  intro r edge
  obtain ⟨u,next,move⟩ := krk_safe_reply material turn safe edge
  obtain ⟨v,legalP,nextP⟩ := step_sound matched (g.map_step move)
  obtain ⟨farP,notCheckP⟩ := krk_strong_arrival_geometry legalP nextP.1 nextP.2
  have threeP := (strong_three_iff nextP.1 nextP.2 farP notCheckP).mp (all v legalP)
  have three := (three_iff g).mp threeP
  obtain ⟨farR,notCheckR⟩ := krk_strong_arrival_geometry edge next.1 next.2
  exact (strong_three_iff next.1 next.2 farR notCheckR).mpr three

theorem global_shape_sufficient {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp)
    (far : 2 ≤ dInf sk wk) (safe : SafeRook sk rs wk) (nonempty : ∃ r, Legal q r)
    (depth : KRKEdgeDepth.depth wk = 0)
    (shape : Shape ((normalize wk).f sk) ((normalize wk).f rs) ((normalize wk).f wk)) : MateWithin σ 4 q := by
  have normal := normalize_spec depth
  exact framed_shape_sufficient (normalize wk) material turn far safe nonempty normal.1 normal.2 shape

end EndgameChess.Rules.KRKFourGeometry
