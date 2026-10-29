import EndgameChess.Rules.KRKNineSlots
import EndgameChess.Rules.KRKNineEntry

namespace EndgameChess.Rules.KRKNineGeometry
open EndgameChess.KK KRKNativeFrame
open KRKNineSlots (Kind point frame)
set_option maxHeartbeats 400000

def KingPoints (sk rs wk : Square) : Prop :=
  let g := frame wk
  ∃ i : Kind, dInf (g.f sk) (point i) = 1 ∧ point i ≠ g.f rs ∧ 2 ≤ dInf (point i) (g.f wk) ∧
    KRKEightGlobal.Region (g.r (point i)) rs wk

def RookRays (sk rs wk : Square) : Prop :=
  let g := frame wk
  ∃ i : Kind, g.f sk = point i ∧ ∃ a : KRKCornerSlotBarriers.Axis, ∃ v : Fin 8,
    RookSees (g.f rs) (a.target (g.f rs) v) (g.f sk) (g.f wk) ∧
      a.target (g.f rs) v ≠ g.f sk ∧ a.target (g.f rs) v ≠ g.f wk ∧
      KRKEightGlobal.Region sk (g.r (a.target (g.f rs) v)) wk

/-- Forty fixed king points and rook-line intersections with the fully
evaluated eight-ply regions. Original native flags are retained. -/
def Clear (sk rs wk : Square) : Prop :=
  KRKImmediate.MateNow sk rs wk ∨ KingPoints sk rs wk ∨ RookRays sk rs wk

theorem entry_sufficient {q : Position} {σ : Colour} {wk ns nr : Square} {m : Move}
    (turn : q.turn = σ) (legal : isLegal q m = true) (next : IsKRK (play q m) σ ns nr wk)
    (region : KRKEightGlobal.Region ns nr wk) : MateWithin σ 9 q := by
  have nextTurn : (play q m).turn = σ.opp := by rw [play_turn,turn]
  have eight := (KRKEightGlobal.kernel_eight_iff next nextTurn (KRKEdgeDepth.arrival_far ⟨m,legal,rfl⟩ next)).mpr
    (Or.inr region)
  exact mateWithin_choose turn ⟨m,legal,rfl⟩ eight

theorem sufficient {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ)
    (far : 2 ≤ dInf sk wk) (notCheck : ¬RookSees rs wk sk wk) (clear : Clear sk rs wk) : MateWithin σ 9 q := by
  rcases clear with immediate | points | rays
  · obtain ⟨r,edge,goal⟩ := (KRKImmediate.immediate_iff material turn far notCheck).mpr immediate
    exact mateWithin_choose turn edge (Or.inl goal)
  · obtain ⟨i,mappedDistance,apart,mappedFar,region⟩ := points
    have distance : dInf sk ((frame wk).r (point i)) = 1 := by
      have preserved := (frame wk).distance sk ((frame wk).r (point i))
      rw [(frame wk).right_inv,mappedDistance] at preserved
      exact preserved.symm
    have notRook : (frame wk).r (point i) ≠ rs := by
      intro equal
      have same := congrArg (frame wk).f equal
      rw [(frame wk).right_inv] at same
      exact apart same
    have postFar : 2 ≤ dInf ((frame wk).r (point i)) wk := by
      have preserved := (frame wk).distance ((frame wk).r (point i)) wk
      rw [(frame wk).right_inv] at preserved
      rwa [←preserved]
    have legal := KRKOrdinaryEntry.king_legal material turn distance notRook postFar
    exact entry_sufficient turn legal (KRKThreePly.canonical_king_material material turn distance notRook postFar) region
  · obtain ⟨i,equal,a,v,mappedSees,notKing,notWeak,region⟩ := rays
    have sees : RookSees rs ((frame wk).r (a.target ((frame wk).f rs) v)) sk wk := by
      apply ((frame wk).sees _ _ _ _).mp
      simpa only [(frame wk).right_inv] using mappedSees
    have apartKing : (frame wk).r (a.target ((frame wk).f rs) v) ≠ sk := by
      intro equal
      have same := congrArg (frame wk).f equal
      rw [(frame wk).right_inv] at same
      exact notKing same
    have apartWeak : (frame wk).r (a.target ((frame wk).f rs) v) ≠ wk := by
      intro equal
      have same := congrArg (frame wk).f equal
      rw [(frame wk).right_inv] at same
      exact notWeak same
    have legal := KRKOrdinaryEntry.rook_legal material turn sees apartKing apartWeak far
    exact entry_sufficient turn legal (KRKMatingMove.rook_move_model material turn legal rfl).1 region

theorem entry_necessary {q : Position} {σ : Colour} {sk rs wk ns nr : Square} {m : Move}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ) (legal : isLegal q m = true)
    (next : IsKRK (play q m) σ ns nr wk) (notMate : ¬MatedK (play q m)) (eight : MateWithin σ 8 (play q m)) :
    KingPoints sk rs wk ∨ RookRays sk rs wk := by
  have nextTurn : (play q m).turn = σ.opp := by rw [play_turn,turn]
  have far := KRKEdgeDepth.arrival_far ⟨m,legal,rfl⟩ next
  have notTerminal : ¬KRKMateGeometry.Terminal ns nr wk := fun h =>
    notMate ((KRKMateGeometry.kernel_mate_iff next nextTurn far).mpr h)
  have region := ((KRKEightGlobal.kernel_eight_iff next nextTurn far).mp eight).resolve_left notTerminal
  rcases KRKNineEntry.eight_entry_move material turn legal next notMate eight with
    ⟨_,_,distance,moved,_⟩ | ⟨_,_,sees,moved,_⟩
  · have nsEq := KRKCastleFour.king_square next (t := m.dst) (by rw [moved.2.2.2]; exact krkBoard_sk)
    have nrEq := KRKCastleFour.rook_square next (t := rs) (by rw [moved.2.2.2]; exact krkBoard_rs moved.1)
    rw [←nsEq,←nrEq] at region
    obtain ⟨i,equal⟩ := KRKNineSlots.region_point region
    have actual := (frame wk).preimage_eq equal
    have mappedDistance := (frame wk).distance sk m.dst
    rw [equal,distance] at mappedDistance
    have apart : point i ≠ (frame wk).f rs := by rw [←equal]; exact (frame wk).ne_iff.mpr moved.1
    have mappedFar : 2 ≤ dInf (point i) ((frame wk).f wk) := by
      rw [←equal,(frame wk).distance]
      exact KRKEdgeDepth.arrival_far ⟨m,legal,rfl⟩ moved
    rw [actual] at region
    exact Or.inl ⟨i,mappedDistance,apart,mappedFar,region⟩
  · have nsEq := KRKCastleFour.king_square next (t := sk) (by rw [moved.2.2.2]; exact krkBoard_sk)
    have nrEq := KRKCastleFour.rook_square next (t := m.dst) (by rw [moved.2.2.2]; exact krkBoard_rs moved.1)
    rw [←nsEq,←nrEq] at region
    obtain ⟨i,equal⟩ := KRKNineSlots.region_point region
    have mappedSees := ((frame wk).sees rs m.dst sk wk).mpr sees
    obtain ⟨a,v,target⟩ := KRKCornerSlotBarriers.line_target mappedSees.1
    have actual := (frame wk).preimage_eq target
    have apartKing : a.target ((frame wk).f rs) v ≠ (frame wk).f sk := by rw [←target]; exact (frame wk).ne_iff.mpr moved.1.symm
    have apartWeak : a.target ((frame wk).f rs) v ≠ (frame wk).f wk := by rw [←target]; exact (frame wk).ne_iff.mpr moved.2.2.1
    rw [target] at mappedSees
    rw [actual] at region
    exact Or.inr ⟨i,equal,a,v,mappedSees,apartKing,apartWeak,region⟩

theorem necessary {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ)
    (far : 2 ≤ dInf sk wk) (notCheck : ¬RookSees rs wk sk wk) (win : MateWithin σ 9 q) : Clear sk rs wk := by
  rcases win with goal | ⟨_,chosen | defended⟩
  · exact False.elim (opp_ne σ (turn.symm.trans goal.1))
  · obtain ⟨_,r,⟨m,legal,rfl⟩,child⟩ := chosen
    obtain ⟨ns,nr,next⟩ := krk_strong_material material turn legal
    by_cases mate : MatedK (play q m)
    · exact Or.inl ((KRKImmediate.immediate_iff material turn far notCheck).mp ⟨_,⟨m,legal,rfl⟩,by rw [play_turn,turn],mate⟩)
    · exact Or.inr (entry_necessary material turn legal next mate child)
  · exact False.elim (opp_ne σ (turn.symm.trans defended.1))

theorem kernel_nine_iff {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ)
    (far : 2 ≤ dInf sk wk) (notCheck : ¬RookSees rs wk sk wk) : MateWithin σ 9 q ↔ Clear sk rs wk :=
  ⟨necessary material turn far notCheck,sufficient material turn far notCheck⟩

theorem frame_map (g : Frame) {sk rs wk : Square}
    (distinct : sk ≠ rs) (notKing : sk ≠ wk) (notRook : rs ≠ wk)
    (far : 2 ≤ dInf sk wk) (notCheck : ¬RookSees rs wk sk wk)
    (clear : Clear sk rs wk) : Clear (g.f sk) (g.f rs) (g.f wk) := by
  let q := krkPos .white sk rs wk .white
  let r := krkPos .white (g.f sk) (g.f rs) (g.f wk) .white
  have material : IsKRK q .white sk rs wk := ⟨distinct,notKing,notRook,rfl⟩
  have mapped : IsKRK r .white (g.f sk) (g.f rs) (g.f wk) :=
    ⟨g.ne_iff.mpr distinct,g.ne_iff.mpr notKing,g.ne_iff.mpr notRook,rfl⟩
  have win := (kernel_nine_iff material rfl far notCheck).mpr clear
  have transported := KRKFrameBound.bound_transport g
    (show Matches q .white ⟨sk,rs,wk,true⟩ from ⟨material,rfl⟩) rfl
    (show Matches r .white (g.mapState ⟨sk,rs,wk,true⟩) from ⟨mapped,rfl⟩) win
  exact (kernel_nine_iff mapped rfl (by rwa [g.distance])
    (fun seen => notCheck ((g.sees _ _ _ _).mp seen))).mp transported

theorem king_step_clear {sk rs wk ns : Square} (distance : dInf sk ns = 1) (apart : ns ≠ rs)
    (far : 2 ≤ dInf ns wk) (region : KRKEightGlobal.Region ns rs wk) : Clear sk rs wk := by
  obtain ⟨i,equal⟩ := KRKNineSlots.region_point region
  have actual := (frame wk).preimage_eq equal
  have mappedDistance := (frame wk).distance sk ns
  rw [equal,distance] at mappedDistance
  have mappedFar : 2 ≤ dInf (point i) ((frame wk).f wk) := by rw [←equal,(frame wk).distance]; exact far
  have mappedApart : point i ≠ (frame wk).f rs := by rw [←equal]; exact (frame wk).ne_iff.mpr apart
  rw [actual] at region
  exact Or.inr (Or.inl ⟨i,mappedDistance,mappedApart,mappedFar,region⟩)

theorem rook_step_clear {sk rs wk nr : Square} (sees : RookSees rs nr sk wk)
    (notKing : nr ≠ sk) (notWeak : nr ≠ wk) (region : KRKEightGlobal.Region sk nr wk) : Clear sk rs wk := by
  obtain ⟨i,equal⟩ := KRKNineSlots.region_point region
  have mappedSees := ((frame wk).sees rs nr sk wk).mpr sees
  obtain ⟨a,v,target⟩ := KRKCornerSlotBarriers.line_target mappedSees.1
  have actual := (frame wk).preimage_eq target
  have apartKing : a.target ((frame wk).f rs) v ≠ (frame wk).f sk := by rw [←target]; exact (frame wk).ne_iff.mpr notKing
  have apartWeak : a.target ((frame wk).f rs) v ≠ (frame wk).f wk := by rw [←target]; exact (frame wk).ne_iff.mpr notWeak
  rw [target] at mappedSees
  rw [actual] at region
  exact Or.inr (Or.inr ⟨i,equal,a,v,mappedSees,apartKing,apartWeak,region⟩)

end EndgameChess.Rules.KRKNineGeometry
