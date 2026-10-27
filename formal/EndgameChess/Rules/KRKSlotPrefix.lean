import EndgameChess.Rules.KRKNearSlotBarriers
import EndgameChess.Rules.KRKVerticalNearSlotBarriers
import EndgameChess.Rules.KRKWeakPrefixEntry

namespace EndgameChess.Rules.KRKSlotPrefix
open EndgameChess.KK KRKThreePly KRKLastReply KRKOppositionHistory
set_option maxHeartbeats 300000

def OriginalEntry (s : RawTrace.State) (wk t : Square) (m : Move) (u : Square) : Prop :=
  RawClock.clock s.trace < 97 ∧
    RawRepetition.occurrences s.trace (play (firstBoard s wk t) m) < 2 ∧
    RawRepetition.occurrences s.trace (play (play (firstBoard s wk t) m) ⟨t, u, none⟩) < 2

namespace Horizontal
open KRKNearSlotBarriers

def KingPoints (s : RawTrace.State) (sk rs wk t : Square) : Prop :=
  ∃ i : Slot, rs.1.val = i.file.val ∧ i.lower ≤ rs.2.val ∧ dInf sk i.king = 1 ∧
    OriginalEntry s wk t ⟨sk, i.king, none⟩ i.reply

def RookStrips (s : RawTrace.State) (sk rs wk t : Square) : Prop :=
  ∃ i : Slot, sk = i.king ∧ ∃ y : Fin 8, AllowedRank rs i y ∧
    OriginalEntry s wk t ⟨rs, (i.file, y), none⟩ i.reply

def Clear (s : RawTrace.State) (sk rs wk t : Square) : Prop :=
  (sk.1.val = 1 ∧ sk.2.val = 2 ∧ rs.2.val ≠ 0 ∧ 3 ≤ rs.1.val) ∨
    KingPoints s sk rs wk t ∨ RookStrips s sk rs wk t

private theorem point_append {s : RawTrace.State} {σ : Colour} {sk rs wk t : Square} {i : Slot}
    (material : IsKRK (RawTrace.erase s) σ sk rs wk) (turn : (RawTrace.erase s).turn = σ.opp)
    (safe : SafeRook sk rs wk) (legal : isLegal (RawTrace.erase s) ⟨wk, t, none⟩ = true)
    (near : t.1.val = 1) (edge : t.2.val = 0)
    (rx : rs.1.val = i.file.val) (ry : i.lower ≤ rs.2.val) (distance : dInf sk i.king = 1) :
    EntryClear (RawTrace.append s ⟨wk, t, none⟩ legal) ⟨sk, i.king, none⟩ t i.reply ↔
      OriginalEntry s wk t ⟨sk, i.king, none⟩ i.reply := by
  have first := weak_material_after material turn safe legal
  have firstTurn : (firstBoard s wk t).turn = σ := by simp [firstBoard, play_turn, turn, opp_opp]
  have geometry := slot_geometry i
  have notRook : i.king ≠ rs := by rw [ne_iff_coords]; omega
  have far : 2 ≤ dInf i.king t := by simp [dInf, absDiff, geometry.1, edge] <;> omega
  have last := (last_slots_iff near edge).mpr ⟨i, rfl, rx, ry⟩
  have entryLegal := king_entry_legal first firstTurn distance notRook far last
  have next := canonical_king_material first firstTurn distance notRook far
  have reply := flat_return_legal next (by simp only [play_turn, turn, opp_opp]) edge geometry.1
    (Nat.le_trans geometry.2.1 ry) geometry.2.2.1 (by omega) (slot_reply_distance near edge i)
  exact KRKWeakPrefixEntry.entry_append_iff material turn safe legal entryLegal next last reply

private theorem strip_append {s : RawTrace.State} {σ : Colour} {sk rs wk t : Square} {i : Slot} {y : Fin 8}
    (material : IsKRK (RawTrace.erase s) σ sk rs wk) (turn : (RawTrace.erase s).turn = σ.opp)
    (safe : SafeRook sk rs wk) (legal : isLegal (RawTrace.erase s) ⟨wk, t, none⟩ = true)
    (near : t.1.val = 1) (edge : t.2.val = 0) (equal : sk = i.king) (allowed : AllowedRank rs i y) :
    EntryClear (RawTrace.append s ⟨wk, t, none⟩ legal) ⟨rs, (i.file, y), none⟩ t i.reply ↔
      OriginalEntry s wk t ⟨rs, (i.file, y), none⟩ i.reply := by
  have first := weak_material_after material turn safe legal
  have firstTurn : (firstBoard s wk t).turn = σ := by simp [firstBoard, play_turn, turn, opp_opp]
  have geometry := slot_geometry i
  have height := allowed.1
  have last : LastReply sk (i.file, y) t := (last_slots_iff near edge).mpr ⟨i, equal, rfl, height⟩
  have sees := (slot_sees_iff equal near edge height).mpr allowed
  have notKing : (i.file, y) ≠ sk := by rw [ne_iff_coords, equal]; dsimp only; omega
  have notWeak : (i.file, y) ≠ t := by rw [ne_iff_coords]; dsimp only; omega
  have far : 2 ≤ dInf sk t := by rw [equal]; simp [dInf, absDiff, geometry.1, edge] <;> omega
  have entryLegal := rook_entry_legal first firstTurn far sees notKing notWeak last
  have next := (KRKMatingMove.rook_move_model first firstTurn entryLegal rfl).1
  have reply := flat_return_legal next (by simp only [play_turn, turn, opp_opp]) edge
    (by rw [equal]; exact geometry.1) (Nat.le_trans geometry.2.1 height) geometry.2.2.1
    geometry.2.2.2.2 (slot_reply_distance near edge i)
  exact KRKWeakPrefixEntry.entry_append_iff material turn safe legal entryLegal next last reply

theorem clear_append_iff {s : RawTrace.State} {σ : Colour} {sk rs wk t : Square}
    (material : IsKRK (RawTrace.erase s) σ sk rs wk) (turn : (RawTrace.erase s).turn = σ.opp)
    (safe : SafeRook sk rs wk) (legal : isLegal (RawTrace.erase s) ⟨wk, t, none⟩ = true)
    (near : t.1.val = 1) (edge : t.2.val = 0) :
    KRKNearSlotBarriers.NearClear (RawTrace.append s ⟨wk, t, none⟩ legal) sk rs t ↔ Clear s sk rs wk t := by
  unfold KRKNearSlotBarriers.NearClear Clear
  apply or_congr Iff.rfl
  apply or_congr
  · constructor
    · rintro ⟨i, rx, ry, distance, clear⟩
      exact ⟨i, rx, ry, distance, (point_append material turn safe legal near edge rx ry distance).mp clear⟩
    · rintro ⟨i, rx, ry, distance, clear⟩
      exact ⟨i, rx, ry, distance, (point_append material turn safe legal near edge rx ry distance).mpr clear⟩
  · constructor
    · rintro ⟨i, equal, y, allowed, clear⟩
      exact ⟨i, equal, y, allowed, (strip_append material turn safe legal near edge equal allowed).mp clear⟩
    · rintro ⟨i, equal, y, allowed, clear⟩
      exact ⟨i, equal, y, allowed, (strip_append material turn safe legal near edge equal allowed).mpr clear⟩

theorem history_append_iff {s : RawTrace.State} {σ : Colour} {sk rs wk t : Square}
    (material : IsKRK (RawTrace.erase s) σ sk rs wk) (turn : (RawTrace.erase s).turn = σ.opp)
    (safe : SafeRook sk rs wk) (legal : isLegal (RawTrace.erase s) ⟨wk, t, none⟩ = true)
    (near : t.1.val = 1) (edge : t.2.val = 0) :
    ThreeHistory (RawTrace.append s ⟨wk, t, none⟩ legal) sk rs t ↔ Clear s sk rs wk t := by
  have first := weak_material_after material turn safe legal
  have firstTurn : (firstBoard s wk t).turn = σ := by simp [firstBoard, play_turn, turn, opp_opp]
  have evaluated : ThreeHistory (RawTrace.append s ⟨wk, t, none⟩ legal) sk rs t ↔
      KRKNearSlotBarriers.NearClear (RawTrace.append s ⟨wk, t, none⟩ legal) sk rs t := by
    simp only [ThreeHistory, KRKNearSlotBarriers.NearClear, KRKThreePly.immediate_near_iff near edge,
      KRKNearSlotBarriers.king_history_iff (s := RawTrace.append s ⟨wk, t, none⟩ legal) first firstTurn near edge,
      KRKNearSlotBarriers.rook_history_iff (s := RawTrace.append s ⟨wk, t, none⟩ legal) first firstTurn near edge]
  exact evaluated.trans (clear_append_iff material turn safe legal near edge)

end Horizontal

namespace Vertical
open KRKVerticalNearSlotBarriers

def KingPoints (s : RawTrace.State) (sk rs wk t : Square) : Prop :=
  ∃ i : Slot, rs.2.val = i.rank.val ∧ i.lower ≤ rs.1.val ∧ dInf sk i.king = 1 ∧
    OriginalEntry s wk t ⟨sk, i.king, none⟩ i.reply

def RookStrips (s : RawTrace.State) (sk rs wk t : Square) : Prop :=
  ∃ i : Slot, sk = i.king ∧ ∃ y : Fin 8, AllowedFile rs i y ∧
    OriginalEntry s wk t ⟨rs, (y, i.rank), none⟩ i.reply

def Clear (s : RawTrace.State) (sk rs wk t : Square) : Prop :=
  (sk.2.val = 1 ∧ sk.1.val = 2 ∧ rs.1.val ≠ 0 ∧ 3 ≤ rs.2.val) ∨
    KingPoints s sk rs wk t ∨ RookStrips s sk rs wk t

private theorem point_append {s : RawTrace.State} {σ : Colour} {sk rs wk t : Square} {i : Slot}
    (material : IsKRK (RawTrace.erase s) σ sk rs wk) (turn : (RawTrace.erase s).turn = σ.opp)
    (safe : SafeRook sk rs wk) (legal : isLegal (RawTrace.erase s) ⟨wk, t, none⟩ = true)
    (near : t.2.val = 1) (edge : t.1.val = 0)
    (rx : rs.2.val = i.rank.val) (ry : i.lower ≤ rs.1.val) (distance : dInf sk i.king = 1) :
    EntryClear (RawTrace.append s ⟨wk, t, none⟩ legal) ⟨sk, i.king, none⟩ t i.reply ↔
      OriginalEntry s wk t ⟨sk, i.king, none⟩ i.reply := by
  have first := weak_material_after material turn safe legal
  have firstTurn : (firstBoard s wk t).turn = σ := by simp [firstBoard, play_turn, turn, opp_opp]
  have geometry := slot_geometry i
  have notRook : i.king ≠ rs := by rw [ne_iff_coords]; omega
  have far : 2 ≤ dInf i.king t := by simp [dInf, absDiff, geometry.1, edge] <;> omega
  have last := (last_slots_iff near edge).mpr ⟨i, rfl, rx, ry⟩
  have entryLegal := king_entry_legal first firstTurn distance notRook far last
  have next := canonical_king_material first firstTurn distance notRook far
  have reply := file_return_legal next (by simp only [play_turn, turn, opp_opp]) edge geometry.1
    (Nat.le_trans geometry.2.1 ry) geometry.2.2.1 (by omega) (slot_reply_distance near edge i)
  exact KRKWeakPrefixEntry.entry_append_iff material turn safe legal entryLegal next last reply

private theorem strip_append {s : RawTrace.State} {σ : Colour} {sk rs wk t : Square} {i : Slot} {y : Fin 8}
    (material : IsKRK (RawTrace.erase s) σ sk rs wk) (turn : (RawTrace.erase s).turn = σ.opp)
    (safe : SafeRook sk rs wk) (legal : isLegal (RawTrace.erase s) ⟨wk, t, none⟩ = true)
    (near : t.2.val = 1) (edge : t.1.val = 0) (equal : sk = i.king) (allowed : AllowedFile rs i y) :
    EntryClear (RawTrace.append s ⟨wk, t, none⟩ legal) ⟨rs, (y, i.rank), none⟩ t i.reply ↔
      OriginalEntry s wk t ⟨rs, (y, i.rank), none⟩ i.reply := by
  have first := weak_material_after material turn safe legal
  have firstTurn : (firstBoard s wk t).turn = σ := by simp [firstBoard, play_turn, turn, opp_opp]
  have geometry := slot_geometry i
  have height := allowed.1
  have last : LastReply sk (y, i.rank) t := (last_slots_iff near edge).mpr ⟨i, equal, rfl, height⟩
  have sees := (slot_sees_iff equal near edge height).mpr allowed
  have notKing : (y, i.rank) ≠ sk := by rw [ne_iff_coords, equal]; dsimp only; omega
  have notWeak : (y, i.rank) ≠ t := by rw [ne_iff_coords]; dsimp only; omega
  have far : 2 ≤ dInf sk t := by rw [equal]; simp [dInf, absDiff, geometry.1, edge] <;> omega
  have entryLegal := rook_entry_legal first firstTurn far sees notKing notWeak last
  have next := (KRKMatingMove.rook_move_model first firstTurn entryLegal rfl).1
  have reply := file_return_legal next (by simp only [play_turn, turn, opp_opp]) edge
    (by rw [equal]; exact geometry.1) (Nat.le_trans geometry.2.1 height) geometry.2.2.1
    geometry.2.2.2.2 (slot_reply_distance near edge i)
  exact KRKWeakPrefixEntry.entry_append_iff material turn safe legal entryLegal next last reply

theorem clear_append_iff {s : RawTrace.State} {σ : Colour} {sk rs wk t : Square}
    (material : IsKRK (RawTrace.erase s) σ sk rs wk) (turn : (RawTrace.erase s).turn = σ.opp)
    (safe : SafeRook sk rs wk) (legal : isLegal (RawTrace.erase s) ⟨wk, t, none⟩ = true)
    (near : t.2.val = 1) (edge : t.1.val = 0) :
    KRKVerticalNearSlotBarriers.NearClear (RawTrace.append s ⟨wk, t, none⟩ legal) sk rs t ↔ Clear s sk rs wk t := by
  unfold KRKVerticalNearSlotBarriers.NearClear Clear
  apply or_congr Iff.rfl
  apply or_congr
  · constructor
    · rintro ⟨i, rx, ry, distance, clear⟩
      exact ⟨i, rx, ry, distance, (point_append material turn safe legal near edge rx ry distance).mp clear⟩
    · rintro ⟨i, rx, ry, distance, clear⟩
      exact ⟨i, rx, ry, distance, (point_append material turn safe legal near edge rx ry distance).mpr clear⟩
  · constructor
    · rintro ⟨i, equal, y, allowed, clear⟩
      exact ⟨i, equal, y, allowed, (strip_append material turn safe legal near edge equal allowed).mp clear⟩
    · rintro ⟨i, equal, y, allowed, clear⟩
      exact ⟨i, equal, y, allowed, (strip_append material turn safe legal near edge equal allowed).mpr clear⟩

theorem history_append_iff {s : RawTrace.State} {σ : Colour} {sk rs wk t : Square}
    (material : IsKRK (RawTrace.erase s) σ sk rs wk) (turn : (RawTrace.erase s).turn = σ.opp)
    (safe : SafeRook sk rs wk) (legal : isLegal (RawTrace.erase s) ⟨wk, t, none⟩ = true)
    (near : t.2.val = 1) (edge : t.1.val = 0) :
    ThreeHistory (RawTrace.append s ⟨wk, t, none⟩ legal) sk rs t ↔ Clear s sk rs wk t := by
  have first := weak_material_after material turn safe legal
  have firstTurn : (firstBoard s wk t).turn = σ := by simp [firstBoard, play_turn, turn, opp_opp]
  have evaluated : ThreeHistory (RawTrace.append s ⟨wk, t, none⟩ legal) sk rs t ↔
      KRKVerticalNearSlotBarriers.NearClear (RawTrace.append s ⟨wk, t, none⟩ legal) sk rs t := by
    simp only [ThreeHistory, KRKVerticalNearSlotBarriers.NearClear, KRKVerticalNearSlotBarriers.immediate_vertical_iff near edge,
      KRKVerticalNearSlotBarriers.king_history_iff (s := RawTrace.append s ⟨wk, t, none⟩ legal) first firstTurn near edge,
      KRKVerticalNearSlotBarriers.rook_history_iff (s := RawTrace.append s ⟨wk, t, none⟩ legal) first firstTurn near edge]
  exact evaluated.trans (clear_append_iff material turn safe legal near edge)

end Vertical

end EndgameChess.Rules.KRKSlotPrefix
