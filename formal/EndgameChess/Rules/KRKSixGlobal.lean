import EndgameChess.Rules.KRKFrameBound

namespace EndgameChess.Rules.KRKSixGlobal
open EndgameChess.KK KRKNativeFrame KRKMateGeometry
set_option maxHeartbeats 300000

/-- All canonical edge files, evaluated by coordinate regions. -/
def EdgeRegion (sk rs wk : Square) : Prop :=
  (wk.1.val = 0 ∧ KRKSixCorner.Region sk rs) ∨
  (wk.1.val = 1 ∧ KRKSixNear.Region sk rs) ∨
  (wk.1.val = 2 ∧ KRKSixSecond.Region sk rs) ∨
  (wk.1.val = 3 ∧ KRKSixMiddle.Region sk rs wk)

def Region (sk rs wk : Square) : Prop :=
  if KRKEdgeDepth.depth wk = 0 then
    EdgeRegion ((normalize wk).f sk) ((normalize wk).f rs) ((normalize wk).f wk)
  else KRKSixInwardCorner.GlobalRegion sk rs wk

private theorem live_not_terminal {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp) (far : 2 ≤ dInf sk wk)
    (live : ∃ t, KRKCornerWeakBand.Guard sk rs wk t) : ¬Terminal sk rs wk := by
  intro terminal
  have mate := (KRKMateGeometry.kernel_mate_iff material turn far).mpr terminal
  obtain ⟨t,guard⟩ := live
  have legal := KRKCornerWeakBand.guard_legal material turn guard
  exact mate.2 ⟨_,⟨_,legal,rfl⟩⟩

theorem canonical_necessary {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp) (far : 2 ≤ dInf sk wk)
    (rank : wk.2.val = 0) (high : wk.1.val ≤ 3) (clear : KRKSixGeometry.Clear sk rs wk) :
    EdgeRegion sk rs wk := by
  have notTerminal := live_not_terminal material turn far clear.2.1
  have every : ∀ t, StepM ⟨sk,rs,wk,false⟩ ⟨sk,rs,t,true⟩ → KRKFiveGeometry.Clear sk rs t :=
    fun t step => clear.2.2 t (KRKCornerWeakBand.step_guard step)
  have files : wk.1.val = 0 ∨ wk.1.val = 1 ∨ wk.1.val = 2 ∨ wk.1.val = 3 := by omega
  rcases files with file | file | file | file
  · exact Or.inl ⟨file,(KRKSixCorner.corner_six_necessary material.1 file rank far clear.1 clear.2.1 every).resolve_left notTerminal⟩
  · exact Or.inr (Or.inl ⟨file,(KRKSixNear.necessary material.1 file rank far clear.1 every).resolve_left notTerminal⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨file,(KRKSixSecond.necessary material.1 file rank far clear.1 every).resolve_left notTerminal⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨file,(KRKSixMiddle.central_six_necessary material.1 rank
      (by omega) (by omega) far clear.1 every).resolve_left notTerminal⟩))

theorem canonical_sufficient {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp) (far : 2 ≤ dInf sk wk)
    (rank : wk.2.val = 0) (region : EdgeRegion sk rs wk)
    (safe : SafeRook sk rs wk) (live : ∃ t, KRKCornerWeakBand.Guard sk rs wk t) : MateWithin σ 6 q := by
  rcases region with ⟨file,region⟩ | ⟨file,region⟩ | ⟨file,region⟩ | ⟨file,sy,region⟩
  · exact (KRKSixCorner.kernel_six_iff material turn far file rank).mpr (Or.inr ⟨region,safe,live⟩)
  · exact (KRKSixNear.kernel_six_iff material turn far file rank).mpr (Or.inr ⟨region,safe,live⟩)
  · exact (KRKSixSecond.kernel_six_iff material turn far file rank).mpr (Or.inr ⟨region,safe,live⟩)
  · apply mateWithin_mono (show MateWithin σ 4 q from ?_) (by decide)
    apply (KRKFourPlyMiddle.weak_four_iff material turn far rank (by omega) (by omega)).mpr
    rcases region with ⟨sx,rx,ry⟩ | ⟨sx,rx,ry⟩ | ⟨sx,ry⟩
    · exact Or.inr (Or.inl ((KRKThreePly.last_middle_iff rank (by omega) (by omega)).mpr ⟨sy,ry,Or.inr ⟨sx,rx⟩⟩))
    · exact Or.inr (Or.inl ((KRKThreePly.last_middle_iff rank (by omega) (by omega)).mpr ⟨sy,ry,Or.inl ⟨sx,rx⟩⟩))
    · exact Or.inr (Or.inr ⟨sx,sy,ry⟩)

theorem edge_clear_iff {sk rs wk : Square} (distinct : sk ≠ rs) (notKing : sk ≠ wk) (notRook : rs ≠ wk)
    (far : 2 ≤ dInf sk wk) (edge : KRKEdgeDepth.depth wk = 0) :
    KRKSixGeometry.Clear sk rs wk ↔
      EdgeRegion ((normalize wk).f sk) ((normalize wk).f rs) ((normalize wk).f wk) ∧
        SafeRook sk rs wk ∧ ∃ t, KRKCornerWeakBand.Guard sk rs wk t := by
  let g := normalize wk
  let q := krkPos .white (g.f sk) (g.f rs) (g.f wk) .black
  have material : IsKRK q .white (g.f sk) (g.f rs) (g.f wk) :=
    ⟨g.ne_iff.mpr distinct,g.ne_iff.mpr notKing,g.ne_iff.mpr notRook,rfl⟩
  have mappedFar : 2 ≤ dInf (g.f sk) (g.f wk) := by rwa [g.distance]
  have normal := normalize_spec edge
  constructor
  · intro clear
    have mapped := KRKFrameBound.six_map g distinct clear
    exact ⟨canonical_necessary material rfl mappedFar normal.1 normal.2 mapped,clear.1,clear.2.1⟩
  · rintro ⟨region,safe,⟨t,guard⟩⟩
    have mappedSafe : SafeRook (g.f sk) (g.f rs) (g.f wk) := by simpa only [SafeRook,g.distance] using safe
    have step : StepM ⟨sk,rs,wk,false⟩ ⟨sk,rs,t,true⟩ := StepM.lone guard.1 guard.2.1 guard.2.2.1 guard.2.2.2
    have mappedLive := KRKCornerWeakBand.step_guard (g.map_step step)
    have win := canonical_sufficient material rfl mappedFar normal.1 region mappedSafe ⟨g.f t,mappedLive⟩
    have notMate : ¬MatedK q := fun mate => (live_not_terminal material rfl mappedFar ⟨g.f t,mappedLive⟩)
      ((KRKMateGeometry.kernel_mate_iff material rfl mappedFar).mp mate)
    have mapped := (KRKSixGeometry.kernel_six_iff material rfl notMate).mp win
    have back := KRKFrameBound.six_map g.inverse (g.ne_iff.mpr distinct) mapped
    simpa only [Frame.inverse,g.left_inv] using back

/-- Complete clock-free six-ply weak-turn geometry on every square and
orientation. Coordinates alone are normalized; native kernel flags remain. -/
theorem kernel_six_iff {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp) (far : 2 ≤ dInf sk wk) :
    MateWithin σ 6 q ↔ Terminal sk rs wk ∨
      (Region sk rs wk ∧ SafeRook sk rs wk ∧ ∃ t, KRKCornerWeakBand.Guard sk rs wk t) := by
  by_cases mate : MatedK q
  · have terminal := (KRKMateGeometry.kernel_mate_iff material turn far).mp mate
    exact ⟨fun _ => Or.inl terminal,fun _ => Or.inl ⟨turn,mate⟩⟩
  have notTerminal : ¬Terminal sk rs wk := fun h => mate ((KRKMateGeometry.kernel_mate_iff material turn far).mpr h)
  simp only [notTerminal,false_or]
  by_cases edge : KRKEdgeDepth.depth wk = 0
  · simp only [Region,edge,↓reduceIte]
    exact (KRKSixGeometry.kernel_six_iff material turn mate).trans
      (edge_clear_iff material.1 material.2.1 material.2.2.1 far edge)
  · simp only [Region,edge,↓reduceIte]
    have inside : 0 < KRKEdgeDepth.depth wk := by omega
    constructor
    · intro win
      have clear := (KRKSixGeometry.kernel_six_iff material turn mate).mp win
      exact ⟨(KRKSixInwardCorner.global_kernel_six_iff material turn far inside).mp win,clear.1,clear.2.1⟩
    · rintro ⟨region,_,_⟩
      exact (KRKSixInwardCorner.global_kernel_six_iff material turn far inside).mpr region

/-- The already evaluated nonterminal four-ply coordinate region. -/
def EarlierFour (sk rs wk : Square) : Prop := KRKEdgeDepth.depth wk = 0 ∧
  KRKFourGeometry.Shape ((normalize wk).f sk) ((normalize wk).f rs) ((normalize wk).f wk)

/-- Exact distance six over the complete board: subtract the explicit
four-ply coordinate region, using weak-turn parity to exclude five. -/
theorem kernel_exact_six_iff {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp) (far : 2 ≤ dInf sk wk) :
    (MateWithin σ 6 q ∧ ¬MateWithin σ 5 q) ↔
      Region sk rs wk ∧ SafeRook sk rs wk ∧
        (∃ t, KRKCornerWeakBand.Guard sk rs wk t) ∧ ¬EarlierFour sk rs wk := by
  constructor
  · rintro ⟨six,notFive⟩
    have notFour : ¬MateWithin σ 4 q := fun win => notFive (mateWithin_mono win (by decide))
    have notMate : ¬MatedK q := fun mate => notFour (Or.inl ⟨turn,mate⟩)
    have notTerminal : ¬Terminal sk rs wk := fun terminal =>
      notMate ((KRKMateGeometry.kernel_mate_iff material turn far).mpr terminal)
    obtain ⟨region,safe,live⟩ := ((kernel_six_iff material turn far).mp six).resolve_left notTerminal
    refine ⟨region,safe,live,?_⟩
    rintro ⟨depth,shape⟩
    obtain ⟨t,guard⟩ := live
    have legal := KRKCornerWeakBand.guard_legal material turn guard
    exact notFour (KRKFourGeometry.global_shape_sufficient material turn far safe ⟨_,⟨_,legal,rfl⟩⟩ depth shape)
  · rintro ⟨region,safe,live,notEarlier⟩
    refine ⟨(kernel_six_iff material turn far).mpr (Or.inr ⟨region,safe,live⟩),?_⟩
    intro five
    have notMate : ¬MatedK q := fun mate => (live_not_terminal material turn far live)
      ((KRKMateGeometry.kernel_mate_iff material turn far).mp mate)
    exact notEarlier (KRKFourGeometry.global_shape_necessary material turn far notMate
      (KRKFourPlyEscape.weak_five_to_four material turn five))

end EndgameChess.Rules.KRKSixGlobal
