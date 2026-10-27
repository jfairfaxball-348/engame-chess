import EndgameChess.Rules.KRKFivePlyHistory

namespace EndgameChess.Rules.KRKFiveGeometry
open EndgameChess.KK KRKThreePly KRKLastReply KRKNativeFrame KRKFourGeometry
open KRKFourSlots (Kind Valid king Region)
set_option maxHeartbeats 500000

def Live (sk rs wk : Square) : Prop := ∃ t, KRKCornerWeakBand.Guard sk rs wk t

def KingPoints (sk rs wk : Square) : Prop :=
  let g := normalize wk
  ∃ i : Kind, Valid (g.f wk) i ∧ Region (g.f wk) (g.f rs) i ∧
    dInf (g.f sk) (king (g.f wk) i) = 1 ∧ king (g.f wk) i ≠ g.f rs ∧
      2 ≤ dInf (king (g.f wk) i) (g.f wk) ∧
      Live (g.r (king (g.f wk) i)) rs wk ∧
      SafeRook (g.r (king (g.f wk) i)) rs wk

def RookRays (sk rs wk : Square) : Prop :=
  let g := normalize wk
  ∃ i : Kind, Valid (g.f wk) i ∧ g.f sk = king (g.f wk) i ∧
    ∃ a : KRKCornerSlotBarriers.Axis, ∃ v : Fin 8,
      RookSees (g.f rs) (a.target (g.f rs) v) (g.f sk) (g.f wk) ∧
      a.target (g.f rs) v ≠ g.f sk ∧ a.target (g.f rs) v ≠ g.f wk ∧
      Region (g.f wk) (a.target (g.f rs) v) i ∧
      Live sk (g.r (a.target (g.f rs) v)) wk ∧
      SafeRook sk (g.r (a.target (g.f rs) v)) wk

/-- Explicit finite five-ply geometry, with no legal or future
outcome predicate. Slots restrict entries before the history tests are made. -/
def Clear (sk rs wk : Square) : Prop :=
  KRKImmediate.MateNow sk rs wk ∨
    (KRKEdgeDepth.depth wk = 0 ∧ (KingPoints sk rs wk ∨ RookRays sk rs wk))

theorem entry_sufficient {q : Position} {σ : Colour} {sk rs wk ns nr : Square} {m : Move}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ)
    (legal : isLegal q m = true) (next : IsKRK (play q m) σ ns nr wk)
    (live : Live ns nr wk) (safe : SafeRook ns nr wk) (depth : KRKEdgeDepth.depth wk = 0)
    (shape : Shape ((normalize wk).f ns) ((normalize wk).f nr) ((normalize wk).f wk)) : MateWithin σ 5 q := by
  have nextTurn : (play q m).turn = σ.opp := by rw [play_turn,turn]
  obtain ⟨t,guard⟩ := live
  have reply := KRKCornerWeakBand.guard_legal next nextTurn guard
  have nonempty : ∃ r, Legal (play q m) r := ⟨_,⟨_,reply,rfl⟩⟩
  have child := global_shape_sufficient next nextTurn (KRKEdgeDepth.arrival_far ⟨m,legal,rfl⟩ next)
    safe nonempty depth shape
  exact mateWithin_choose turn ⟨m,legal,rfl⟩ child

theorem sufficient {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ)
    (far : 2 ≤ dInf sk wk) (notCheck : ¬RookSees rs wk sk wk)
    (clear : Clear sk rs wk) : MateWithin σ 5 q := by
  rcases clear with immediate | ⟨depth,points | rays⟩
  · obtain ⟨r,edge,goal⟩ := (KRKImmediate.immediate_iff material turn far notCheck).mpr immediate
    exact mateWithin_choose turn edge (Or.inl goal)
  · obtain ⟨i,valid,region,mappedDistance,apart,mappedFar,live,clear⟩ := points
    have distance : dInf sk ((normalize wk).r (king ((normalize wk).f wk) i)) = 1 := by
      have preserved := (normalize wk).distance sk ((normalize wk).r (king ((normalize wk).f wk) i))
      rw [(normalize wk).right_inv,mappedDistance] at preserved
      exact preserved.symm
    have notRook : (normalize wk).r (king ((normalize wk).f wk) i) ≠ rs := by
      intro equal; have same := congrArg (normalize wk).f equal
      rw [(normalize wk).right_inv] at same
      exact apart same
    have far : 2 ≤ dInf ((normalize wk).r (king ((normalize wk).f wk) i)) wk := by
      have preserved := (normalize wk).distance ((normalize wk).r (king ((normalize wk).f wk) i)) wk
      rw [(normalize wk).right_inv] at preserved
      rwa [←preserved]
    have legal := KRKOrdinaryEntry.king_legal material turn distance notRook far
    have next := canonical_king_material material turn distance notRook far
    have shape : Shape ((normalize wk).f ((normalize wk).r (king ((normalize wk).f wk) i)))
        ((normalize wk).f rs) ((normalize wk).f wk) := by
      rw [(normalize wk).right_inv]
      have normal := normalize_spec depth
      exact (KRKFourSlots.shape_iff normal.1 normal.2).mpr ⟨i,valid,rfl,region⟩
    exact entry_sufficient material turn legal next live clear depth shape
  · obtain ⟨i,valid,equal,a,v,mappedSees,notKing,notWeak,region,live,clear⟩ := rays
    have sees : RookSees rs ((normalize wk).r (a.target ((normalize wk).f rs) v)) sk wk := by
      apply ((normalize wk).sees _ _ _ _).mp
      simpa only [(normalize wk).right_inv] using mappedSees
    have apartKing : (normalize wk).r (a.target ((normalize wk).f rs) v) ≠ sk := by
      intro equal; have same := congrArg (normalize wk).f equal
      rw [(normalize wk).right_inv] at same
      exact notKing same
    have apartWeak : (normalize wk).r (a.target ((normalize wk).f rs) v) ≠ wk := by
      intro equal; have same := congrArg (normalize wk).f equal
      rw [(normalize wk).right_inv] at same
      exact notWeak same
    have legal := KRKOrdinaryEntry.rook_legal material turn sees apartKing apartWeak far
    have next := (KRKMatingMove.rook_move_model material turn legal rfl).1
    have shape : Shape ((normalize wk).f sk)
        ((normalize wk).f ((normalize wk).r (a.target ((normalize wk).f rs) v))) ((normalize wk).f wk) := by
      rw [(normalize wk).right_inv]
      have normal := normalize_spec depth
      exact (KRKFourSlots.shape_iff normal.1 normal.2).mpr ⟨i,valid,equal,region⟩
    exact entry_sufficient material turn legal next live clear depth shape


theorem entry_necessary {q : Position} {σ : Colour} {sk rs wk ns nr : Square} {m : Move}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ)
    (legal : isLegal q m = true) (next : IsKRK (play q m) σ ns nr wk)
    (notMate : ¬MatedK (play q m)) (win : MateWithin σ 4 (play q m)) : Clear sk rs wk := by
  have nextTurn : (play q m).turn = σ.opp := by rw [play_turn,turn]
  have safe := krk_force_weak_safe next nextTurn ⟨4,win⟩
  have live : Live ns nr wk := by
    have nonempty : ∃ r, Legal (play q m) r := by
      rcases win with goal | ⟨_,chosen | defended⟩
      · exact False.elim (notMate goal.2)
      · exact False.elim (opp_ne σ (chosen.1.symm.trans nextTurn))
      · exact defended.2.1
    obtain ⟨r,edge⟩ := nonempty
    obtain ⟨t,_,step⟩ := krk_safe_reply next nextTurn safe edge
    exact ⟨t,KRKCornerWeakBand.step_guard step⟩
  have geometry := global_shape_necessary next (by rw [play_turn,turn])
    (KRKEdgeDepth.arrival_far ⟨m,legal,rfl⟩ next) notMate win
  have normal := normalize_spec geometry.1
  refine Or.inr ⟨geometry.1,?_⟩
  rcases KRKCastleFour.four_entry_move material turn legal next notMate win with
    ⟨src,promo,distance,moved,shape⟩ | ⟨src,promo,sees,moved,shape⟩
  · have nsEq := KRKCastleFour.king_square next (t := m.dst) (by rw [moved.2.2.2]; exact krkBoard_sk)
    have nrEq := KRKCastleFour.rook_square next (t := rs) (by rw [moved.2.2.2]; exact krkBoard_rs moved.1)
    rw [←nsEq,←nrEq] at live safe
    obtain ⟨i,valid,equal,region⟩ := (KRKFourSlots.shape_iff normal.1 normal.2).mp shape
    have actual := (normalize wk).preimage_eq equal
    have mappedDistance := (normalize wk).distance sk m.dst
    rw [equal,distance] at mappedDistance
    have apart : king ((normalize wk).f wk) i ≠ (normalize wk).f rs := by
      rw [←equal]; exact (normalize wk).ne_iff.mpr moved.1
    have mappedFar : 2 ≤ dInf (king ((normalize wk).f wk) i) ((normalize wk).f wk) := by
      rw [←equal,(normalize wk).distance]
      exact KRKEdgeDepth.arrival_far ⟨m,legal,rfl⟩ moved
    rw [actual] at live safe
    exact Or.inl ⟨i,valid,region,mappedDistance,apart,mappedFar,live,safe⟩
  · have nsEq := KRKCastleFour.king_square next (t := sk) (by rw [moved.2.2.2]; exact krkBoard_sk)
    have nrEq := KRKCastleFour.rook_square next (t := m.dst) (by rw [moved.2.2.2]; exact krkBoard_rs moved.1)
    rw [←nsEq,←nrEq] at live safe
    obtain ⟨i,valid,equal,region⟩ := (KRKFourSlots.shape_iff normal.1 normal.2).mp shape
    have mappedSees := ((normalize wk).sees rs m.dst sk wk).mpr sees
    obtain ⟨a,v,target⟩ := KRKCornerSlotBarriers.line_target mappedSees.1
    have actual := (normalize wk).preimage_eq target
    have apartKing : a.target ((normalize wk).f rs) v ≠ (normalize wk).f sk := by
      rw [←target]; exact (normalize wk).ne_iff.mpr moved.1.symm
    have apartWeak : a.target ((normalize wk).f rs) v ≠ (normalize wk).f wk := by
      rw [←target]; exact (normalize wk).ne_iff.mpr moved.2.2.1
    rw [target] at mappedSees region
    rw [actual] at live safe
    exact Or.inr ⟨i,valid,equal,a,v,mappedSees,apartKing,apartWeak,region,live,safe⟩

theorem necessary {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ)
    (far : 2 ≤ dInf sk wk) (notCheck : ¬RookSees rs wk sk wk) (win : MateWithin σ 5 q) : Clear sk rs wk := by
  rcases win with goal | ⟨_,chosen | defended⟩
  · exact False.elim (opp_ne σ (turn.symm.trans goal.1))
  · obtain ⟨_,r,⟨m,legal,rfl⟩,child⟩ := chosen
    obtain ⟨ns,nr,next⟩ := krk_strong_material material turn legal
    by_cases mate : MatedK (play q m)
    · apply Or.inl
      apply (KRKImmediate.immediate_iff material turn far notCheck).mp
      exact ⟨_,⟨m,legal,rfl⟩,by rw [play_turn,turn],mate⟩
    · exact entry_necessary material turn legal next mate child
  · exact False.elim (opp_ne σ (turn.symm.trans defended.1))

theorem kernel_five_iff {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ)
    (far : 2 ≤ dInf sk wk) (notCheck : ¬RookSees rs wk sk wk) :
    MateWithin σ 5 q ↔ Clear sk rs wk :=
  ⟨necessary material turn far notCheck,sufficient material turn far notCheck⟩


/-- Pure five-ply geometry transports through a board isometry. The proof
uses synthetic castling-free boards; no actual game's flags are transformed. -/
theorem map (g : BoardSym) {sk rs wk : Square}
    (distinct : sk ≠ rs) (notKing : sk ≠ wk) (notRook : rs ≠ wk)
    (far : 2 ≤ dInf sk wk) (notCheck : ¬RookSees rs wk sk wk) (clear : Clear sk rs wk) :
    Clear (g.f sk) (g.f rs) (g.f wk) := by
  let q := krkPos .white sk rs wk .white
  let r := krkPos .white (g.f sk) (g.f rs) (g.f wk) .white
  have material : IsKRK q .white sk rs wk := ⟨distinct,notKing,notRook,rfl⟩
  have mapped : IsKRK r .white (g.f sk) (g.f rs) (g.f wk) :=
    ⟨g.ne_iff.mpr distinct,g.ne_iff.mpr notKing,g.ne_iff.mpr notRook,rfl⟩
  have win := (kernel_five_iff material rfl far notCheck).mpr clear
  have transported := krk_bound_transport g
    (show Matches q .white ⟨sk,rs,wk,true⟩ from ⟨material,rfl⟩) rfl
    (show Matches r .white ((⟨sk,rs,wk,true⟩ : KRKState).map g) from ⟨mapped,rfl⟩) win
  have mappedCheck : ¬RookSees (g.f rs) (g.f wk) (g.f sk) (g.f wk) := fun seen => notCheck ((g.sees_iff _ _ _ _).mp seen)
  exact (kernel_five_iff mapped rfl (by rwa [g.dInf_eq]) mappedCheck).mp transported

theorem map_iff (g : BoardSym) {sk rs wk : Square}
    (distinct : sk ≠ rs) (notKing : sk ≠ wk) (notRook : rs ≠ wk)
    (far : 2 ≤ dInf sk wk) (notCheck : ¬RookSees rs wk sk wk) :
    Clear (g.f sk) (g.f rs) (g.f wk) ↔ Clear sk rs wk := by
  constructor
  · intro clear
    have check : ¬RookSees (g.f rs) (g.f wk) (g.f sk) (g.f wk) := fun seen => notCheck ((g.sees_iff _ _ _ _).mp seen)
    simpa only [g.invol] using map g (g.ne_iff.mpr distinct) (g.ne_iff.mpr notKing) (g.ne_iff.mpr notRook)
      (by rwa [g.dInf_eq]) check clear
  · exact map g distinct notKing notRook far notCheck

end EndgameChess.Rules.KRKFiveGeometry
