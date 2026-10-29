import EndgameChess.Rules.KRKTwelveEdge

namespace EndgameChess.Rules.KRKTwelveGlobal
open EndgameChess.KK KRKNativeFrame KRKMateGeometry
set_option maxHeartbeats 400000

/-- Completely evaluated twelve-ply geometry over the full board. -/
def Region (sk rs wk : Square) : Prop :=
  if KRKEdgeDepth.depth wk = 0 then
    KRKTwelveEdge.Region ((normalize wk).f sk) ((normalize wk).f rs) ((normalize wk).f wk)
  else KRKTwelveInteriorExact.Region sk rs wk

theorem edge_clear_iff {sk rs wk : Square} (apart : sk ≠ rs) (edge : KRKEdgeDepth.depth wk = 0) :
    KRKTwelveGeometry.Clear sk rs wk ↔
      KRKTwelveEdge.Region ((normalize wk).f sk) ((normalize wk).f rs) ((normalize wk).f wk) := by
  let g := normalize wk
  have spec := normalize_spec edge
  constructor
  · intro clear
    exact (KRKTwelveEdge.clear_iff spec.1 spec.2 (g.ne_iff.mpr apart)).mp
      (KRKTwelveGeometry.frame_map g apart clear)
  · intro region
    have mapped := (KRKTwelveEdge.clear_iff spec.1 spec.2 (g.ne_iff.mpr apart)).mpr region
    change KRKTwelveGeometry.Clear (g.f sk) (g.f rs) (g.f wk) at mapped
    have back := KRKTwelveGeometry.frame_map g.inverse (g.ne_iff.mpr apart) mapped
    simpa only [Frame.inverse,g.left_inv] using back

theorem kernel_twelve_iff {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp) (far : 2 ≤ dInf sk wk) :
    MateWithin σ 12 q ↔ Terminal sk rs wk ∨ Region sk rs wk := by
  by_cases mate : MatedK q
  · have terminal := (KRKMateGeometry.kernel_mate_iff material turn far).mp mate
    exact ⟨fun _ => Or.inl terminal,fun _ => Or.inl ⟨turn,mate⟩⟩
  have notTerminal : ¬Terminal sk rs wk := fun h => mate ((KRKMateGeometry.kernel_mate_iff material turn far).mpr h)
  simp only [notTerminal,false_or]
  by_cases edge : KRKEdgeDepth.depth wk = 0
  · simp only [Region,edge,↓reduceIte]
    exact (KRKTwelveGeometry.kernel_twelve_iff material turn mate).trans (edge_clear_iff material.1 edge)
  · simp only [Region,edge,↓reduceIte]
    exact KRKTwelveInteriorExact.kernel_twelve_iff material turn far (by omega)

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
    have eight := (kernel_twelve_iff material turn far).mpr (Or.inr region)
    have goal := (forceMate_no_moves_iff noMoves).mp ⟨12,eight⟩
    have zero := KRKEdgeDepth.terminal_depth_zero ((KRKMateGeometry.kernel_mate_iff material turn far).mp goal.2)
    exact edge zero


def EarlierTen (sk rs wk : Square) : Prop :=
  Terminal sk rs wk ∨ KRKTenGlobal.Region sk rs wk

theorem kernel_exact_twelve_iff {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp) (far : 2 ≤ dInf sk wk) :
    (MateWithin σ 12 q ∧ ¬MateWithin σ 11 q) ↔ Region sk rs wk ∧ ¬EarlierTen sk rs wk := by
  constructor
  · rintro ⟨ten,notNine⟩
    have notEight : ¬MateWithin σ 10 q := fun eight => notNine (mateWithin_mono eight (by decide))
    have earlier : ¬EarlierTen sk rs wk := fun h => notEight ((KRKTenGlobal.kernel_ten_iff material turn far).mpr h)
    have notTerminal : ¬Terminal sk rs wk := fun terminal => earlier (Or.inl terminal)
    exact ⟨((kernel_twelve_iff material turn far).mp ten).resolve_left notTerminal,earlier⟩
  · rintro ⟨region,notEarlier⟩
    refine ⟨(kernel_twelve_iff material turn far).mpr (Or.inr region),?_⟩
    intro nine
    exact notEarlier ((KRKTenGlobal.kernel_ten_iff material turn far).mp
      (KRKTenGeometry.weak_eleven_ten material turn nine))

end EndgameChess.Rules.KRKTwelveGlobal
