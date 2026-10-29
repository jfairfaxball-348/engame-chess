import EndgameChess.Rules.KRKElevenGeometry

namespace EndgameChess.Rules.KRKTwelveGeometry
open EndgameChess.KK
set_option maxHeartbeats 400000

/-- Intermediate twelve-ply geometry. The next geometric evaluation must
resolve these guards; this is not full material-class closure. -/
def Clear (sk rs wk : Square) : Prop :=
  SafeRook sk rs wk ∧ (∃ t,KRKCornerWeakBand.Guard sk rs wk t) ∧
    ∀ t,KRKCornerWeakBand.Guard sk rs wk t → KRKElevenGeometry.Clear sk rs t

theorem kernel_twelve_iff {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp) (notMate : ¬MatedK q) :
    MateWithin σ 12 q ↔ Clear sk rs wk := by
  constructor
  · intro win
    have safe := krk_force_weak_safe material turn ⟨12,win⟩
    have data : (∃ r,Legal q r) ∧ ∀ r,Legal q r → MateWithin σ 11 r := by
      rcases win with goal | ⟨_,chosen | defended⟩
      · exact False.elim (notMate goal.2)
      · exact False.elim (opp_ne σ (chosen.1.symm.trans turn))
      · exact defended.2
    obtain ⟨r,edge⟩ := data.1
    obtain ⟨t,_,step⟩ := krk_safe_reply material turn safe edge
    refine ⟨safe,⟨t,KRKCornerWeakBand.step_guard step⟩,?_⟩
    intro t guard
    have legal := KRKCornerWeakBand.guard_legal material turn guard
    have next := KRKOppositionHistory.weak_material_after material turn safe legal
    have nextTurn : (play q ⟨wk,t,none⟩).turn = σ := by rw [play_turn,turn,opp_opp]
    obtain ⟨far,notCheck⟩ := krk_strong_arrival_geometry ⟨_,legal,rfl⟩ next nextTurn
    exact (KRKElevenGeometry.kernel_eleven_iff next nextTurn far notCheck).mp (data.2 _ ⟨_,legal,rfl⟩)
  · rintro ⟨safe,⟨t,guard⟩,all⟩
    have legal := KRKCornerWeakBand.guard_legal material turn guard
    apply mateWithin_defend turn ⟨_,⟨_,legal,rfl⟩⟩
    intro r edge
    obtain ⟨t,next,step⟩ := krk_safe_reply material turn safe edge
    obtain ⟨far,notCheck⟩ := krk_strong_arrival_geometry edge next.1 next.2
    exact (KRKElevenGeometry.kernel_eleven_iff next.1 next.2 far notCheck).mpr (all t (KRKCornerWeakBand.step_guard step))

theorem strong_twelve_eleven {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ) (win : MateWithin σ 12 q) : MateWithin σ 11 q := by
  rcases win with goal | ⟨_,chosen | defended⟩
  · exact Or.inl goal
  · obtain ⟨_,r,⟨m,legal,rfl⟩,child⟩ := chosen
    obtain ⟨ns,nr,next⟩ := krk_strong_material material turn legal
    have nextTurn : (play q m).turn = σ.opp := by rw [play_turn,turn]
    exact mateWithin_choose turn ⟨m,legal,rfl⟩ (KRKTenGeometry.weak_eleven_ten next nextTurn child)
  · exact False.elim (opp_ne σ (turn.symm.trans defended.1))

theorem weak_thirteen_twelve {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp) (win : MateWithin σ 13 q) : MateWithin σ 12 q := by
  have safe := krk_force_weak_safe material turn ⟨13,win⟩
  rcases win with goal | ⟨_,chosen | defended⟩
  · exact Or.inl goal
  · exact False.elim (opp_ne σ (chosen.1.symm.trans turn))
  · apply mateWithin_defend turn defended.2.1
    intro r edge
    obtain ⟨t,next,_⟩ := krk_safe_reply material turn safe edge
    exact strong_twelve_eleven next.1 next.2 (defended.2.2 r edge)

theorem ten_region_depth {sk rs wk : Square} (region : KRKTenGlobal.Region sk rs wk) :
    KRKEdgeDepth.depth wk ≤ 1 := by
  by_cases edge : KRKEdgeDepth.depth wk = 0
  · omega
  · simp only [KRKTenGlobal.Region,edge,↓reduceIte,KRKTenInteriorExact.Region] at region
    omega

theorem eleven_weak_depth {sk rs wk : Square} (clear : KRKElevenGeometry.Clear sk rs wk) :
    KRKEdgeDepth.depth wk ≤ 1 := by
  rcases clear with immediate | ⟨_,_,_,_,region⟩ | ⟨_,_,_,_,_,_,_,region⟩
  · have edge := KRKFourPlyEscape.three_depth_zero (Or.inl immediate); omega
  · exact ten_region_depth region
  · exact ten_region_depth region

theorem frame_map (g : KRKNativeFrame.Frame) {sk rs wk : Square} (distinct : sk ≠ rs)
    (clear : Clear sk rs wk) : Clear (g.f sk) (g.f rs) (g.f wk) := by
  obtain ⟨safe,⟨t,guard⟩,all⟩ := clear
  have mappedSafe : SafeRook (g.f sk) (g.f rs) (g.f wk) := by simpa only [SafeRook,g.distance] using safe
  have step : StepM ⟨sk,rs,wk,false⟩ ⟨sk,rs,t,true⟩ := StepM.lone guard.1 guard.2.1 guard.2.2.1 guard.2.2.2
  refine ⟨mappedSafe,⟨g.f t,KRKCornerWeakBand.step_guard (g.map_step step)⟩,?_⟩
  intro u next
  have back := g.inverse.map_step (StepM.lone next.1 next.2.1 next.2.2.1 next.2.2.2)
  change StepM ⟨g.r (g.f sk),g.r (g.f rs),g.r (g.f wk),false⟩
    ⟨g.r (g.f sk),g.r (g.f rs),g.r u,true⟩ at back
  simp only [g.left_inv] at back
  have guardBack := KRKCornerWeakBand.step_guard back
  have far := guardBack.2.2.1
  have mapped := KRKElevenGeometry.frame_map g distinct (ne_of_dInf_pos (by omega)) guardBack.2.1.symm
    far guardBack.2.2.2 (all _ guardBack)
  simpa only [g.right_inv] using mapped

end EndgameChess.Rules.KRKTwelveGeometry
