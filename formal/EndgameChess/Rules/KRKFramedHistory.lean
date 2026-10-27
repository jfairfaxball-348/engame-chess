import EndgameChess.Rules.KRKCanonicalSlots
import EndgameChess.Rules.KRKCornerSlotBarriers
import EndgameChess.Rules.KRKWeakBranch
import EndgameChess.Rules.KRKHighClock.StrongHold

namespace EndgameChess.Rules.KRKFramedHistory
open EndgameChess.KK KRKThreePly KRKLastReply KRKCanonicalSlots KRKNativeFrame RawHistoryLayer
open KRKCornerSlotBarriers (Axis)
set_option maxHeartbeats 400000

def AllowedRay (wk rs : Square) (i : Kind) (a : Axis) (v : Fin 8) : Prop :=
  Region wk i (a.target rs v) ∧
    match a with
    | .file => rs.2.val ≠ v.val ∧
        (rs.1.val ≠ (king wk i).1.val ∨
          ¬((rs.2.val < (king wk i).2.val ∧ (king wk i).2.val < v.val) ∨
            (v.val < (king wk i).2.val ∧ (king wk i).2.val < rs.2.val)))
    | .rank => rs.1.val ≠ v.val ∧
        (rs.2.val ≠ (king wk i).2.val ∨
          ¬((rs.1.val < (king wk i).1.val ∧ (king wk i).1.val < v.val) ∨
            (v.val < (king wk i).1.val ∧ (king wk i).1.val < rs.1.val)))

theorem ray_sees_iff {wk rs : Square} {i : Kind} {a : Axis} {v : Fin 8}
    (valid : Valid wk i) (region : Region wk i (a.target rs v)) :
    RookSees rs (a.target rs v) (king wk i) wk ↔ AllowedRay wk rs i a v := by
  have off := region_off_weak valid region
  have rank := valid.1
  simp only [AllowedRay, region, true_and]
  cases a <;> dsimp [Axis.target, RookSees, RookLine, OnSeg] at off ⊢ <;> omega

def KingPoints (s : RawTrace.State) (g : Frame) (sk rs wk : Square) : Prop :=
  ∃ i : Kind, Valid (g.f wk) i ∧ Region (g.f wk) i (g.f rs) ∧
    dInf (g.f sk) (king (g.f wk) i) = 1 ∧
      EntryClear s ⟨sk, g.r (king (g.f wk) i), none⟩ wk (g.r (reply (g.f wk) i))

def RookRays (s : RawTrace.State) (g : Frame) (sk rs wk : Square) : Prop :=
  ∃ i : Kind, Valid (g.f wk) i ∧ g.f sk = king (g.f wk) i ∧
    ∃ a : Axis, ∃ v : Fin 8, AllowedRay (g.f wk) (g.f rs) i a v ∧
      EntryClear s ⟨rs, g.r (a.target (g.f rs) v), none⟩ wk (g.r (reply (g.f wk) i))

def Clear (s : RawTrace.State) (g : Frame) (sk rs wk : Square) : Prop :=
  KRKImmediate.MateNow (g.f sk) (g.f rs) (g.f wk) ∨
    KingPoints s g sk rs wk ∨ RookRays s g sk rs wk

theorem native_reply_step (g : Frame) {sk rs wk : Square} {i : Kind}
    (equal : g.f sk = king (g.f wk) i) (valid : Valid (g.f wk) i) (region : Region (g.f wk) i (g.f rs)) :
    StepM ⟨sk, rs, wk, false⟩ ⟨sk, rs, g.r (reply (g.f wk) i), true⟩ := by
  have back := g.inverse.map_step (reply_step valid region)
  change StepM ⟨g.r (king (g.f wk) i), g.r (g.f rs), g.r (g.f wk), false⟩
    ⟨g.r (king (g.f wk) i), g.r (g.f rs), g.r (reply (g.f wk) i), true⟩ at back
  simpa only [g.left_inv, ←g.preimage_eq equal] using back

theorem king_history_iff {s : RawTrace.State} {σ : Colour} {sk rs wk : Square} (g : Frame)
    (material : IsKRK (RawTrace.erase s) σ sk rs wk) (turn : (RawTrace.erase s).turn = σ)
    (rank : (g.f wk).2.val = 0) (high : (g.f wk).1.val ≤ 3) :
    KingHistoryEntry s sk rs wk ↔ KingPoints s g sk rs wk := by
  constructor
  · rintro ⟨t, u, distance, notRook, far, last, legal, response, clear⟩
    obtain ⟨i, valid, equal, region⟩ := (last_catalogue_iff rank high).mp ((g.last t rs wk).mpr last)
    have actual := g.preimage_eq equal
    subst t
    have next := canonical_king_material material turn distance notRook far
    have step := native_reply_step g (by rw [g.right_inv]) valid region
    have replyLegal := lone_step_legal next (by rw [play_turn, turn]) step
    obtain ⟨_, _, unique⟩ := unique_legal_reply next (by rw [play_turn, turn]) far last
    have same : u = g.r (reply (g.f wk) i) := congrArg Move.dst ((unique _ response).trans (unique _ replyLegal).symm)
    have mappedDistance : dInf (g.f sk) (king (g.f wk) i) = 1 := by
      simpa only [g.right_inv] using (g.distance sk (g.r (king (g.f wk) i))).trans distance
    exact ⟨i, valid, region, mappedDistance, by simpa only [same] using clear⟩
  · rintro ⟨i, valid, region, mappedDistance, clear⟩
    have last : LastReply (g.r (king (g.f wk) i)) rs wk := by
      apply (g.last _ _ _).mp
      simpa only [g.right_inv] using slot_last valid region
    obtain ⟨notRook, _, _, far⟩ := KRKGeometricSymmetry.last_valid last
    have distance : dInf sk (g.r (king (g.f wk) i)) = 1 := by
      have preserved := g.distance sk (g.r (king (g.f wk) i))
      rw [g.right_inv, mappedDistance] at preserved
      exact preserved.symm
    have legal := king_entry_legal material turn distance notRook far last
    have next := canonical_king_material material turn distance notRook far
    have step := native_reply_step g (by rw [g.right_inv]) valid region
    have replyLegal := lone_step_legal next (by rw [play_turn, turn]) step
    exact ⟨_, _, distance, notRook, far, last, legal, replyLegal, clear⟩

theorem rook_history_iff {s : RawTrace.State} {σ : Colour} {sk rs wk : Square} (g : Frame)
    (material : IsKRK (RawTrace.erase s) σ sk rs wk) (turn : (RawTrace.erase s).turn = σ)
    (rank : (g.f wk).2.val = 0) (high : (g.f wk).1.val ≤ 3) :
    RookHistoryEntry s sk rs wk ↔ RookRays s g sk rs wk := by
  constructor
  · rintro ⟨t, u, sees, _, _, last, legal, response, clear⟩
    obtain ⟨i, valid, equal, region⟩ := (last_catalogue_iff rank high).mp ((g.last sk t wk).mpr last)
    have mappedSees := (g.sees rs t sk wk).mpr sees
    obtain ⟨a, v, target⟩ := KRKCornerSlotBarriers.line_target mappedSees.1
    have actual := g.preimage_eq target
    subst t
    simp only [g.right_inv] at region mappedSees
    have next := (KRKMatingMove.rook_move_model material turn legal rfl).1
    have step := native_reply_step g (rs := g.r (a.target (g.f rs) v)) equal valid (by simpa only [g.right_inv] using region)
    have replyLegal := lone_step_legal next (by rw [play_turn, turn]) step
    have far := KRKEdgeDepth.arrival_far ⟨_, legal, rfl⟩ next
    obtain ⟨_, _, unique⟩ := unique_legal_reply next (by rw [play_turn, turn]) far last
    have same : u = g.r (reply (g.f wk) i) := congrArg Move.dst ((unique _ response).trans (unique _ replyLegal).symm)
    have allowed := (ray_sees_iff valid region).mp (by simpa only [equal] using mappedSees)
    exact ⟨i, valid, equal, a, v, allowed, by simpa only [same] using clear⟩
  · rintro ⟨i, valid, equal, a, v, allowed, clear⟩
    have region := allowed.1
    have sees : RookSees rs (g.r (a.target (g.f rs) v)) sk wk := by
      apply (g.sees _ _ _ _).mp
      simpa only [g.right_inv, equal] using (ray_sees_iff valid region).mpr allowed
    have last : LastReply sk (g.r (a.target (g.f rs) v)) wk := by
      apply (g.last _ _ _).mp
      simpa only [g.right_inv, equal] using slot_last valid region
    obtain ⟨notKing, _, notWeak, far⟩ := KRKGeometricSymmetry.last_valid last
    have legal := rook_entry_legal material turn far sees notKing.symm notWeak last
    have next := (KRKMatingMove.rook_move_model material turn legal rfl).1
    have step := native_reply_step g (rs := g.r (a.target (g.f rs) v)) equal valid (by simpa only [g.right_inv] using region)
    have replyLegal := lone_step_legal next (by rw [play_turn, turn]) step
    exact ⟨_, _, sees, notKing.symm, notWeak, last, legal, replyLegal, clear⟩

theorem history_iff {s : RawTrace.State} {σ : Colour} {sk rs wk : Square} (g : Frame)
    (material : IsKRK (RawTrace.erase s) σ sk rs wk) (turn : (RawTrace.erase s).turn = σ)
    (rank : (g.f wk).2.val = 0) (high : (g.f wk).1.val ≤ 3) :
    ThreeHistory s sk rs wk ↔ Clear s g sk rs wk := by
  simp only [ThreeHistory, Clear, g.immediate, king_history_iff g material turn rank high,
    rook_history_iff g material turn rank high]

def GlobalClear (s : RawTrace.State) (sk rs wk : Square) : Prop :=
  KRKEdgeDepth.depth wk = 0 ∧ Clear s (normalize wk) sk rs wk

/-- Complete all-orientation RAW strong-turn h>=96 criterion. Only entry
coordinates are normalized; every key is computed by actual native play. -/
theorem high_clock_force_iff {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ) (high : 96 ≤ RawClock.clock s.val.trace) :
    KRKHolding.F σ s ↔ GlobalClear s.val sk rs wk := by
  rw [KRKThreePly.high_clock_force_iff material ongoing turn high]
  constructor
  · intro history
    have depth := KRKFourPlyEscape.three_depth_zero (KRKWeakBranch.history_geometry history)
    have normal := normalize_spec depth
    exact ⟨depth, (history_iff (normalize wk) material turn normal.1 normal.2).mp history⟩
  · rintro ⟨depth, clear⟩
    have normal := normalize_spec depth
    exact (history_iff (normalize wk) material turn normal.1 normal.2).mpr clear

theorem high_clock_actual_iff {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ) (high : 96 ≤ RawClock.clock s.val.trace)
 :
    KRKWinning.ActualWin σ s ↔ GlobalClear s.val sk rs wk :=
  (KRKWinning.actual_win_iff_force (Or.inl ⟨sk, rs, wk, material⟩)).trans
    (high_clock_force_iff material ongoing turn high)

theorem high_clock_hold_iff {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ) (high : 96 ≤ RawClock.clock s.val.trace)
 :
    KRKHolding.RuleHold σ.opp s ↔ ¬GlobalClear s.val sk rs wk := by
  have dual := KRKHolding.holding_iff_not_force (σ := σ) (c := σ.opp)
    (s := s) (Or.inl ⟨sk, rs, wk, material⟩)
  simpa only [opp_opp, high_clock_force_iff material ongoing turn high] using dual

theorem high_clock_distance_cases {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ) (high : 96 ≤ RawClock.clock s.val.trace)
 (win : KRKHolding.F σ s) :
    (KRKImmediate.MateNow sk rs wk ∧ KRKHolding.W σ 1 s ∧ ¬KRKHolding.W σ 0 s) ∨
      (¬KRKImmediate.MateNow sk rs wk ∧ KRKHolding.W σ 3 s ∧ ¬KRKHolding.W σ 2 s) := by
  by_cases immediate : KRKImmediate.MateNow sk rs wk
  · obtain ⟨v, edge, goal⟩ := (KRKImmediate.admitted_immediate_iff material ongoing turn).mpr immediate
    refine Or.inl ⟨immediate, Or.inr ⟨ongoing, Or.inl ⟨turn, v, edge, goal⟩⟩, ?_⟩
    intro zero
    exact opp_ne σ (turn.symm.trans zero.1)
  · have result := KRKThreePly.high_clock_exact_three material ongoing turn high
    exact Or.inr ⟨immediate, result.1.mp win, result.2 immediate⟩

theorem high_clock_draw_iff {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ) (high : 96 ≤ RawClock.clock s.val.trace) :
    (KRKHolding.RuleHold σ s ∧ KRKHolding.RuleHold σ.opp s) ↔ ¬GlobalClear s.val sk rs wk := by
  constructor
  · intro holds; exact (high_clock_hold_iff material ongoing turn high).mp holds.2
  · intro outside
    exact ⟨KRKHighClock.strong_hold material, (high_clock_hold_iff material ongoing turn high).mpr outside⟩

end EndgameChess.Rules.KRKFramedHistory
