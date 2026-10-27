import EndgameChess.Rules.KRKSlotPrefix
import EndgameChess.Rules.KRKCornerSlotBarriers

namespace EndgameChess.Rules.KRKSlotPrefix.Corner
open EndgameChess.KK KRKThreePly KRKLastReply KRKOppositionHistory KRKCornerSlotBarriers
set_option maxHeartbeats 300000

def KingPoints (s : RawTrace.State) (sk rs wk t : Square) : Prop :=
  ∃ i : Slot, i.minFile ≤ rs.1.val ∧ i.minRank ≤ rs.2.val ∧ dInf sk i.king = 1 ∧
    OriginalEntry s wk t ⟨sk, i.king, none⟩ i.reply

def RookRays (s : RawTrace.State) (sk rs wk t : Square) : Prop :=
  ∃ i : Slot, sk = i.king ∧ ∃ a : Axis, ∃ v : Fin 8, Allowed rs i a v ∧
    OriginalEntry s wk t ⟨rs, a.target rs v, none⟩ i.reply

def Clear (s : RawTrace.State) (sk rs wk t : Square) : Prop :=
  ((sk.2.val = 2 ∧ sk.1.val ≤ 1 ∧ 2 ≤ rs.1.val ∧ rs.2.val ≠ 0) ∨
   (sk.1.val = 2 ∧ sk.2.val ≤ 1 ∧ 2 ≤ rs.2.val ∧ rs.1.val ≠ 0)) ∨
    KingPoints s sk rs wk t ∨ RookRays s sk rs wk t

private theorem point_append {s : RawTrace.State} {σ : Colour} {sk rs wk t : Square} {i : Slot}
    (material : IsKRK (RawTrace.erase s) σ sk rs wk) (turn : (RawTrace.erase s).turn = σ.opp)
    (safe : SafeRook sk rs wk) (legal : isLegal (RawTrace.erase s) ⟨wk, t, none⟩ = true)
    (file : t.1.val = 0) (rank : t.2.val = 0)
    (rx : i.minFile ≤ rs.1.val) (ry : i.minRank ≤ rs.2.val) (distance : dInf sk i.king = 1) :
    EntryClear (RawTrace.append s ⟨wk, t, none⟩ legal) ⟨sk, i.king, none⟩ t i.reply ↔
      OriginalEntry s wk t ⟨sk, i.king, none⟩ i.reply := by
  have first := weak_material_after material turn safe legal
  have firstTurn : (firstBoard s wk t).turn = σ := by simp [firstBoard, play_turn, turn, opp_opp]
  have notRook := slot_not_rook rx ry
  have far := slot_far file rank i
  have last := (last_slots_iff file rank).mpr ⟨i, rfl, rx, ry⟩
  have entryLegal := king_entry_legal first firstTurn distance notRook far last
  have next := canonical_king_material first firstTurn distance notRook far
  have reply := slot_reply_legal next (by simp only [firstBoard, play_turn, turn, opp_opp]) file rank rx ry
  exact KRKWeakPrefixEntry.entry_append_iff material turn safe legal entryLegal next last reply

private theorem ray_append {s : RawTrace.State} {σ : Colour} {sk rs wk t : Square}
    {i : Slot} {a : Axis} {v : Fin 8}
    (material : IsKRK (RawTrace.erase s) σ sk rs wk) (turn : (RawTrace.erase s).turn = σ.opp)
    (safe : SafeRook sk rs wk) (legal : isLegal (RawTrace.erase s) ⟨wk, t, none⟩ = true)
    (file : t.1.val = 0) (rank : t.2.val = 0) (equal : sk = i.king) (allowed : Allowed rs i a v) :
    EntryClear (RawTrace.append s ⟨wk, t, none⟩ legal) ⟨rs, a.target rs v, none⟩ t i.reply ↔
      OriginalEntry s wk t ⟨rs, a.target rs v, none⟩ i.reply := by
  have first := weak_material_after material turn safe legal
  have firstTurn : (firstBoard s wk t).turn = σ := by simp [firstBoard, play_turn, turn, opp_opp]
  have rx := allowed.1
  have ry := allowed.2.1
  have last := (last_slots_iff file rank).mpr ⟨i, equal, rx, ry⟩
  have sees : RookSees rs (a.target rs v) sk t := by rw [equal]; exact (ray_sees_iff file rank rx ry).mpr allowed
  have notKing : a.target rs v ≠ sk := by rw [equal]; exact (slot_not_rook rx ry).symm
  have notWeak : a.target rs v ≠ t := by
    rw [ne_iff_coords]
    have positive := (slot_geometry i).1
    omega
  have far : 2 ≤ dInf sk t := by rw [equal]; exact slot_far file rank i
  have entryLegal := rook_entry_legal first firstTurn far sees notKing notWeak last
  have next := (KRKMatingMove.rook_move_model first firstTurn entryLegal rfl).1
  have next' : IsKRK (play (firstBoard s wk t) ⟨rs, a.target rs v, none⟩) σ i.king (a.target rs v) t := by
    simpa only [equal, firstBoard] using next
  have reply := slot_reply_legal next' (by simp only [firstBoard, play_turn, turn, opp_opp]) file rank rx ry
  exact KRKWeakPrefixEntry.entry_append_iff material turn safe legal entryLegal next last reply

theorem clear_append_iff {s : RawTrace.State} {σ : Colour} {sk rs wk t : Square}
    (material : IsKRK (RawTrace.erase s) σ sk rs wk) (turn : (RawTrace.erase s).turn = σ.opp)
    (safe : SafeRook sk rs wk) (legal : isLegal (RawTrace.erase s) ⟨wk, t, none⟩ = true)
    (file : t.1.val = 0) (rank : t.2.val = 0) :
    KRKCornerSlotBarriers.CornerClear (RawTrace.append s ⟨wk, t, none⟩ legal) sk rs t ↔ Clear s sk rs wk t := by
  unfold KRKCornerSlotBarriers.CornerClear Clear
  apply or_congr Iff.rfl
  apply or_congr
  · constructor
    · rintro ⟨i, rx, ry, distance, clear⟩
      exact ⟨i, rx, ry, distance, (point_append material turn safe legal file rank rx ry distance).mp clear⟩
    · rintro ⟨i, rx, ry, distance, clear⟩
      exact ⟨i, rx, ry, distance, (point_append material turn safe legal file rank rx ry distance).mpr clear⟩
  · constructor
    · rintro ⟨i, equal, a, v, allowed, clear⟩
      exact ⟨i, equal, a, v, allowed, (ray_append material turn safe legal file rank equal allowed).mp clear⟩
    · rintro ⟨i, equal, a, v, allowed, clear⟩
      exact ⟨i, equal, a, v, allowed, (ray_append material turn safe legal file rank equal allowed).mpr clear⟩

theorem history_append_iff {s : RawTrace.State} {σ : Colour} {sk rs wk t : Square}
    (material : IsKRK (RawTrace.erase s) σ sk rs wk) (turn : (RawTrace.erase s).turn = σ.opp)
    (safe : SafeRook sk rs wk) (legal : isLegal (RawTrace.erase s) ⟨wk, t, none⟩ = true)
    (file : t.1.val = 0) (rank : t.2.val = 0) :
    ThreeHistory (RawTrace.append s ⟨wk, t, none⟩ legal) sk rs t ↔ Clear s sk rs wk t := by
  have first := weak_material_after material turn safe legal
  have firstTurn : (firstBoard s wk t).turn = σ := by simp [firstBoard, play_turn, turn, opp_opp]
  have evaluated : ThreeHistory (RawTrace.append s ⟨wk, t, none⟩ legal) sk rs t ↔
      KRKCornerSlotBarriers.CornerClear (RawTrace.append s ⟨wk, t, none⟩ legal) sk rs t := by
    simp only [ThreeHistory, KRKCornerSlotBarriers.CornerClear, immediate_corner_iff file rank,
      KRKCornerSlotBarriers.king_history_iff (s := RawTrace.append s ⟨wk, t, none⟩ legal) first firstTurn file rank,
      KRKCornerSlotBarriers.rook_history_iff (s := RawTrace.append s ⟨wk, t, none⟩ legal) first firstTurn file rank]
  exact evaluated.trans (clear_append_iff material turn safe legal file rank)

end EndgameChess.Rules.KRKSlotPrefix.Corner
