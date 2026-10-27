import EndgameChess.Rules.KRKFramedHistory
import EndgameChess.Rules.KRKSlotPrefix

namespace EndgameChess.Rules.KRKFramedPrefix
open EndgameChess.KK KRKThreePly KRKLastReply KRKOppositionHistory KRKCanonicalSlots KRKNativeFrame
open KRKCornerSlotBarriers (Axis)
open KRKSlotPrefix (OriginalEntry)
set_option maxHeartbeats 400000

def KingPoints (s : RawTrace.State) (g : Frame) (sk rs wk t : Square) : Prop :=
  ∃ i : Kind, Valid (g.f t) i ∧ Region (g.f t) i (g.f rs) ∧
    dInf (g.f sk) (king (g.f t) i) = 1 ∧
      OriginalEntry s wk t ⟨sk, g.r (king (g.f t) i), none⟩ (g.r (reply (g.f t) i))

def RookRays (s : RawTrace.State) (g : Frame) (sk rs wk t : Square) : Prop :=
  ∃ i : Kind, Valid (g.f t) i ∧ g.f sk = king (g.f t) i ∧
    ∃ a : Axis, ∃ v : Fin 8, KRKFramedHistory.AllowedRay (g.f t) (g.f rs) i a v ∧
      OriginalEntry s wk t ⟨rs, g.r (a.target (g.f rs) v), none⟩ (g.r (reply (g.f t) i))

def Clear (s : RawTrace.State) (g : Frame) (sk rs wk t : Square) : Prop :=
  KRKImmediate.MateNow (g.f sk) (g.f rs) (g.f t) ∨
    KingPoints s g sk rs wk t ∨ RookRays s g sk rs wk t

theorem point_append {s : RawTrace.State} {σ : Colour} {sk rs wk t : Square} {i : Kind} (g : Frame)
    (material : IsKRK (RawTrace.erase s) σ sk rs wk) (turn : (RawTrace.erase s).turn = σ.opp)
    (safe : SafeRook sk rs wk) (legal : isLegal (RawTrace.erase s) ⟨wk, t, none⟩ = true)
    (valid : Valid (g.f t) i) (region : Region (g.f t) i (g.f rs))
    (mappedDistance : dInf (g.f sk) (king (g.f t) i) = 1) :
    EntryClear (RawTrace.append s ⟨wk, t, none⟩ legal) ⟨sk, g.r (king (g.f t) i), none⟩ t (g.r (reply (g.f t) i)) ↔
      OriginalEntry s wk t ⟨sk, g.r (king (g.f t) i), none⟩ (g.r (reply (g.f t) i)) := by
  have first := weak_material_after material turn safe legal
  have firstTurn : (firstBoard s wk t).turn = σ := by simp [firstBoard, play_turn, turn, opp_opp]
  have last : LastReply (g.r (king (g.f t) i)) rs t := by
    apply (g.last _ _ _).mp
    simpa only [g.right_inv] using slot_last valid region
  obtain ⟨notRook, _, _, far⟩ := KRKGeometricSymmetry.last_valid last
  have distance : dInf sk (g.r (king (g.f t) i)) = 1 := by
    have preserved := g.distance sk (g.r (king (g.f t) i))
    rw [g.right_inv, mappedDistance] at preserved
    exact preserved.symm
  have entryLegal := king_entry_legal first firstTurn distance notRook far last
  have next := canonical_king_material first firstTurn distance notRook far
  have step := KRKFramedHistory.native_reply_step g (by rw [g.right_inv]) valid region
  have response := lone_step_legal next (by simp only [play_turn, turn, opp_opp]) step
  exact KRKWeakPrefixEntry.entry_append_iff material turn safe legal entryLegal next last response

theorem ray_append {s : RawTrace.State} {σ : Colour} {sk rs wk t : Square}
    {i : Kind} {a : Axis} {v : Fin 8} (g : Frame)
    (material : IsKRK (RawTrace.erase s) σ sk rs wk) (turn : (RawTrace.erase s).turn = σ.opp)
    (safe : SafeRook sk rs wk) (legal : isLegal (RawTrace.erase s) ⟨wk, t, none⟩ = true)
    (valid : Valid (g.f t) i) (equal : g.f sk = king (g.f t) i)
    (allowed : KRKFramedHistory.AllowedRay (g.f t) (g.f rs) i a v) :
    EntryClear (RawTrace.append s ⟨wk, t, none⟩ legal) ⟨rs, g.r (a.target (g.f rs) v), none⟩ t (g.r (reply (g.f t) i)) ↔
      OriginalEntry s wk t ⟨rs, g.r (a.target (g.f rs) v), none⟩ (g.r (reply (g.f t) i)) := by
  have first := weak_material_after material turn safe legal
  have firstTurn : (firstBoard s wk t).turn = σ := by simp [firstBoard, play_turn, turn, opp_opp]
  have region := allowed.1
  have sees : RookSees rs (g.r (a.target (g.f rs) v)) sk t := by
    apply (g.sees _ _ _ _).mp
    simpa only [g.right_inv, equal] using (KRKFramedHistory.ray_sees_iff valid region).mpr allowed
  have last : LastReply sk (g.r (a.target (g.f rs) v)) t := by
    apply (g.last _ _ _).mp
    simpa only [g.right_inv, equal] using slot_last valid region
  obtain ⟨notKing, _, notWeak, far⟩ := KRKGeometricSymmetry.last_valid last
  have entryLegal := rook_entry_legal first firstTurn far sees notKing.symm notWeak last
  have next := (KRKMatingMove.rook_move_model first firstTurn entryLegal rfl).1
  have step := KRKFramedHistory.native_reply_step g (rs := g.r (a.target (g.f rs) v)) equal valid
    (by simpa only [g.right_inv] using region)
  have response := lone_step_legal next (by simp only [play_turn, turn, opp_opp]) step
  exact KRKWeakPrefixEntry.entry_append_iff material turn safe legal entryLegal next last response

theorem clear_append_iff {s : RawTrace.State} {σ : Colour} {sk rs wk t : Square} (g : Frame)
    (material : IsKRK (RawTrace.erase s) σ sk rs wk) (turn : (RawTrace.erase s).turn = σ.opp)
    (safe : SafeRook sk rs wk) (legal : isLegal (RawTrace.erase s) ⟨wk, t, none⟩ = true) :
    KRKFramedHistory.Clear (RawTrace.append s ⟨wk, t, none⟩ legal) g sk rs t ↔ Clear s g sk rs wk t := by
  unfold KRKFramedHistory.Clear Clear
  apply or_congr Iff.rfl
  apply or_congr
  · constructor
    · rintro ⟨i, valid, region, distance, clear⟩
      exact ⟨i, valid, region, distance, (point_append g material turn safe legal valid region distance).mp clear⟩
    · rintro ⟨i, valid, region, distance, clear⟩
      exact ⟨i, valid, region, distance, (point_append g material turn safe legal valid region distance).mpr clear⟩
  · constructor
    · rintro ⟨i, valid, equal, a, v, allowed, clear⟩
      exact ⟨i, valid, equal, a, v, allowed, (ray_append g material turn safe legal valid equal allowed).mp clear⟩
    · rintro ⟨i, valid, equal, a, v, allowed, clear⟩
      exact ⟨i, valid, equal, a, v, allowed, (ray_append g material turn safe legal valid equal allowed).mpr clear⟩

theorem history_append_iff {s : RawTrace.State} {σ : Colour} {sk rs wk t : Square} (g : Frame)
    (material : IsKRK (RawTrace.erase s) σ sk rs wk) (turn : (RawTrace.erase s).turn = σ.opp)
    (safe : SafeRook sk rs wk) (legal : isLegal (RawTrace.erase s) ⟨wk, t, none⟩ = true)
    (rank : (g.f t).2.val = 0) (high : (g.f t).1.val ≤ 3) :
    ThreeHistory (RawTrace.append s ⟨wk, t, none⟩ legal) sk rs t ↔ Clear s g sk rs wk t := by
  have first := weak_material_after material turn safe legal
  have firstTurn : (firstBoard s wk t).turn = σ := by simp [firstBoard, play_turn, turn, opp_opp]
  exact (KRKFramedHistory.history_iff (s := RawTrace.append s ⟨wk, t, none⟩ legal) g first firstTurn rank high).trans
    (clear_append_iff g material turn safe legal)

end EndgameChess.Rules.KRKFramedPrefix
