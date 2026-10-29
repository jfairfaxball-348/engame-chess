import EndgameChess.Rules.KRKEightEdge

namespace EndgameChess.Rules.KRKEightGlobal
open EndgameChess.KK KRKNativeFrame KRKMateGeometry
set_option maxHeartbeats 400000

/-- Completely evaluated eight-ply geometry over the full board. -/
def Region (sk rs wk : Square) : Prop :=
  if KRKEdgeDepth.depth wk = 0 then
    KRKEightEdge.Region ((normalize wk).f sk) ((normalize wk).f rs) ((normalize wk).f wk)
  else KRKEightInteriorExact.Region sk rs wk

theorem edge_clear_iff {sk rs wk : Square} (apart : sk ≠ rs) (edge : KRKEdgeDepth.depth wk = 0) :
    KRKEightGeometry.Clear sk rs wk ↔
      KRKEightEdge.Region ((normalize wk).f sk) ((normalize wk).f rs) ((normalize wk).f wk) := by
  let g := normalize wk
  have spec := normalize_spec edge
  constructor
  · intro clear
    exact (KRKEightEdge.clear_iff spec.1 spec.2 (g.ne_iff.mpr apart)).mp
      (KRKCastleEight.frame_map g apart clear)
  · intro region
    have mapped := (KRKEightEdge.clear_iff spec.1 spec.2 (g.ne_iff.mpr apart)).mpr region
    change KRKEightGeometry.Clear (g.f sk) (g.f rs) (g.f wk) at mapped
    have back := KRKCastleEight.frame_map g.inverse (g.ne_iff.mpr apart) mapped
    simpa only [Frame.inverse,g.left_inv] using back

theorem kernel_eight_iff {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp) (far : 2 ≤ dInf sk wk) :
    MateWithin σ 8 q ↔ Terminal sk rs wk ∨ Region sk rs wk := by
  by_cases mate : MatedK q
  · have terminal := (KRKMateGeometry.kernel_mate_iff material turn far).mp mate
    exact ⟨fun _ => Or.inl terminal,fun _ => Or.inl ⟨turn,mate⟩⟩
  have notTerminal : ¬Terminal sk rs wk := fun h => mate ((KRKMateGeometry.kernel_mate_iff material turn far).mpr h)
  simp only [notTerminal,false_or]
  by_cases edge : KRKEdgeDepth.depth wk = 0
  · simp only [Region,edge,↓reduceIte]
    exact (KRKEightGeometry.kernel_eight_iff material turn mate).trans (edge_clear_iff material.1 edge)
  · simp only [Region,edge,↓reduceIte]
    exact KRKEightInteriorExact.kernel_eight_iff material turn far (by omega)

theorem region_live {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp) (far : 2 ≤ dInf sk wk)
    (region : Region sk rs wk) : ∃ r,Legal q r := by
  by_cases edge : KRKEdgeDepth.depth wk = 0
  · simp only [Region,edge,↓reduceIte] at region
    have clear := (edge_clear_iff material.1 edge).mpr region
    obtain ⟨t,guard⟩ := clear.2.1
    exact ⟨_,⟨_,KRKCornerWeakBand.guard_legal material turn guard,rfl⟩⟩
  · apply Classical.byContradiction
    intro noMoves
    have eight := (kernel_eight_iff material turn far).mpr (Or.inr region)
    have goal := (forceMate_no_moves_iff noMoves).mp ⟨8,eight⟩
    have zero := KRKEdgeDepth.terminal_depth_zero ((KRKMateGeometry.kernel_mate_iff material turn far).mp goal.2)
    exact edge zero

def EarlierSix (sk rs wk : Square) : Prop :=
  Terminal sk rs wk ∨ (KRKSixGlobal.Region sk rs wk ∧ SafeRook sk rs wk ∧
    ∃ t, KRKCornerWeakBand.Guard sk rs wk t)

theorem kernel_exact_eight_iff {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp) (far : 2 ≤ dInf sk wk) :
    (MateWithin σ 8 q ∧ ¬MateWithin σ 7 q) ↔ Region sk rs wk ∧ ¬EarlierSix sk rs wk := by
  constructor
  · rintro ⟨eight,notSeven⟩
    have notSix : ¬MateWithin σ 6 q := fun six => notSeven (mateWithin_mono six (by decide))
    have earlier : ¬EarlierSix sk rs wk := fun h => notSix ((KRKSixGlobal.kernel_six_iff material turn far).mpr h)
    have notTerminal : ¬Terminal sk rs wk := fun terminal => earlier (Or.inl terminal)
    exact ⟨((kernel_eight_iff material turn far).mp eight).resolve_left notTerminal,earlier⟩
  · rintro ⟨region,notEarlier⟩
    refine ⟨(kernel_eight_iff material turn far).mpr (Or.inr region),?_⟩
    intro seven
    exact notEarlier ((KRKSixGlobal.kernel_six_iff material turn far).mp
      (KRKSixGeometry.weak_seven_six material turn seven))

end EndgameChess.Rules.KRKEightGlobal
