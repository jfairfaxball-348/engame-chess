import EndgameChess.Rules.KRKThreePlyCorner
import EndgameChess.Rules.KRKThreePlyHistory

namespace EndgameChess.Rules.KRKCornerSlotBarriers
open EndgameChess.KK KRKThreePly KRKLastReply RawHistoryLayer
set_option maxHeartbeats 400000

inductive Slot where
  | horizontal | vertical

def Slot.king : Slot → Square
  | .horizontal => (1, 2)
  | .vertical => (2, 1)

def Slot.reply : Slot → Square
  | .horizontal => (1, 0)
  | .vertical => (0, 1)

def Slot.minFile : Slot → Nat
  | .horizontal => 3
  | .vertical => 1

def Slot.minRank : Slot → Nat
  | .horizontal => 1
  | .vertical => 3

inductive Axis where
  | file | rank

def Axis.target (rs : Square) : Axis → Fin 8 → Square
  | .file, y => (rs.1, y)
  | .rank, x => (x, rs.2)

theorem slot_geometry (i : Slot) :
    1 ≤ i.minFile ∧ 1 ≤ i.minRank ∧ i.reply.1.val < i.minFile ∧
    i.reply.2.val < i.minRank ∧ dInf i.king i.reply = 2 := by
  cases i <;> decide

theorem slot_reply_distance {wk : Square} (file : wk.1.val = 0) (rank : wk.2.val = 0) (i : Slot) :
    dInf wk i.reply = 1 := by
  cases i <;> simp [Slot.reply, dInf, absDiff, file, rank]

theorem slot_far {wk : Square} (file : wk.1.val = 0) (rank : wk.2.val = 0) (i : Slot) :
    2 ≤ dInf i.king wk := by
  cases i <;> simp [Slot.king, dInf, absDiff, file, rank]

theorem last_slots_iff {sk rs wk : Square} (file : wk.1.val = 0) (rank : wk.2.val = 0) :
    LastReply sk rs wk ↔ ∃ i : Slot, sk = i.king ∧ i.minFile ≤ rs.1.val ∧ i.minRank ≤ rs.2.val := by
  rw [last_corner_iff file rank]
  constructor
  · rintro (⟨sx, sy, rx, ry⟩ | ⟨sx, sy, ry, rx⟩)
    · refine ⟨.horizontal, ?_, rx, ry⟩
      apply Prod.ext <;> apply Fin.ext <;> assumption
    · refine ⟨.vertical, ?_, rx, ry⟩
      apply Prod.ext <;> apply Fin.ext <;> assumption
  · rintro ⟨i, equal, rx, ry⟩
    subst sk
    cases i <;> simp_all [Slot.king, Slot.minFile, Slot.minRank]

theorem slot_not_rook {r : Square} {i : Slot}
    (rx : i.minFile ≤ r.1.val) (ry : i.minRank ≤ r.2.val) : i.king ≠ r := by
  cases i <;> rw [ne_iff_coords] <;> dsimp [Slot.king, Slot.minFile, Slot.minRank] at * <;> omega

theorem slot_reply_legal {q : Position} {σ : Colour} {r wk : Square} {i : Slot}
    (material : IsKRK q σ i.king r wk) (turn : q.turn = σ.opp)
    (file : wk.1.val = 0) (rank : wk.2.val = 0)
    (rx : i.minFile ≤ r.1.val) (ry : i.minRank ≤ r.2.val) :
    isLegal q ⟨wk, i.reply, none⟩ = true := by
  have geometry := slot_geometry i
  apply lone_step_legal material turn
  refine StepM.lone (slot_reply_distance file rank i) ?_ ?_ ?_
  · rw [ne_iff_coords]; omega
  · have distance := geometry.2.2.2.2
    rw [dInf_comm] at distance
    omega
  · intro sees
    rcases sees.1.2 with x | y <;> omega

def Allowed (rs : Square) (i : Slot) (a : Axis) (v : Fin 8) : Prop :=
  i.minFile ≤ (a.target rs v).1.val ∧ i.minRank ≤ (a.target rs v).2.val ∧
    match a with
    | .file => rs.2.val ≠ v.val ∧
        (rs.1.val ≠ i.king.1.val ∨ ¬((rs.2.val < i.king.2.val ∧ i.king.2.val < v.val) ∨
          (v.val < i.king.2.val ∧ i.king.2.val < rs.2.val)))
    | .rank => rs.1.val ≠ v.val ∧
        (rs.2.val ≠ i.king.2.val ∨ ¬((rs.1.val < i.king.1.val ∧ i.king.1.val < v.val) ∨
          (v.val < i.king.1.val ∧ i.king.1.val < rs.1.val)))

theorem ray_sees_iff {rs wk : Square} {i : Slot} {a : Axis} {v : Fin 8}
    (file : wk.1.val = 0) (rank : wk.2.val = 0)
    (rx : i.minFile ≤ (a.target rs v).1.val) (ry : i.minRank ≤ (a.target rs v).2.val) :
    RookSees rs (a.target rs v) i.king wk ↔ Allowed rs i a v := by
  cases i <;> cases a <;>
    dsimp [Allowed, Axis.target, RookSees, RookLine, OnSeg, Slot.king, Slot.minFile, Slot.minRank] at rx ry ⊢ <;> omega

theorem line_target {rs t : Square} (line : RookLine rs t) :
    ∃ a : Axis, ∃ v : Fin 8, t = a.target rs v := by
  rcases line.2 with file | rank
  · refine ⟨.file, t.2, ?_⟩
    apply Prod.ext
    · exact Fin.ext file.symm
    · rfl
  · refine ⟨.rank, t.1, ?_⟩
    apply Prod.ext
    · rfl
    · exact Fin.ext rank.symm

def KingPoints (s : RawTrace.State) (sk rs wk : Square) : Prop :=
  ∃ i : Slot, i.minFile ≤ rs.1.val ∧ i.minRank ≤ rs.2.val ∧ dInf sk i.king = 1 ∧
    EntryClear s ⟨sk, i.king, none⟩ wk i.reply

def RookRays (s : RawTrace.State) (sk rs wk : Square) : Prop :=
  ∃ i : Slot, sk = i.king ∧ ∃ a : Axis, ∃ v : Fin 8, Allowed rs i a v ∧
    EntryClear s ⟨rs, a.target rs v, none⟩ wk i.reply

theorem king_history_iff {s : RawTrace.State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (RawTrace.erase s) σ sk rs wk) (turn : (RawTrace.erase s).turn = σ)
    (file : wk.1.val = 0) (rank : wk.2.val = 0) :
    KingHistoryEntry s sk rs wk ↔ KingPoints s sk rs wk := by
  constructor
  · rintro ⟨t, u, distance, notRook, far, last, legal, response, clear⟩
    obtain ⟨i, equal, rx, ry⟩ := (last_slots_iff file rank).mp last
    subst t
    have next := canonical_king_material material turn distance notRook far
    have reply := slot_reply_legal next (by rw [play_turn, turn]) file rank rx ry
    obtain ⟨_, _, unique⟩ := unique_legal_reply next (by rw [play_turn, turn]) far last
    have same : u = i.reply := congrArg Move.dst ((unique _ response).trans (unique _ reply).symm)
    exact ⟨i, rx, ry, distance, by simpa only [same] using clear⟩
  · rintro ⟨i, rx, ry, distance, clear⟩
    have notRook := slot_not_rook rx ry
    have far := slot_far file rank i
    have last := (last_slots_iff file rank).mpr ⟨i, rfl, rx, ry⟩
    have legal := king_entry_legal material turn distance notRook far last
    have next := canonical_king_material material turn distance notRook far
    have reply := slot_reply_legal next (by rw [play_turn, turn]) file rank rx ry
    exact ⟨_, _, distance, notRook, far, last, legal, reply, clear⟩

theorem rook_history_iff {s : RawTrace.State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (RawTrace.erase s) σ sk rs wk) (turn : (RawTrace.erase s).turn = σ)
    (file : wk.1.val = 0) (rank : wk.2.val = 0) :
    RookHistoryEntry s sk rs wk ↔ RookRays s sk rs wk := by
  constructor
  · rintro ⟨t, u, sees, _, _, last, legal, response, clear⟩
    obtain ⟨i, equal, rx, ry⟩ := (last_slots_iff file rank).mp last
    obtain ⟨a, v, target⟩ := line_target sees.1
    subst t
    have next := (KRKMatingMove.rook_move_model material turn legal rfl).1
    have next' : IsKRK (play (RawTrace.erase s) ⟨rs, a.target rs v, none⟩) σ i.king (a.target rs v) wk := by
      simpa only [equal] using next
    have reply := slot_reply_legal next' (by rw [play_turn, turn]) file rank rx ry
    have far := KRKEdgeDepth.arrival_far ⟨_, legal, rfl⟩ next
    obtain ⟨_, _, unique⟩ := unique_legal_reply next (by rw [play_turn, turn]) far last
    have same : u = i.reply := congrArg Move.dst ((unique _ response).trans (unique _ reply).symm)
    have allowed := (ray_sees_iff file rank rx ry).mp (by simpa only [equal] using sees)
    exact ⟨i, equal, a, v, allowed, by simpa only [same] using clear⟩
  · rintro ⟨i, equal, a, v, allowed, clear⟩
    have rx := allowed.1
    have ry := allowed.2.1
    have sees : RookSees rs (a.target rs v) sk wk := by
      rw [equal]; exact (ray_sees_iff file rank rx ry).mpr allowed
    have last := (last_slots_iff file rank).mpr ⟨i, equal, rx, ry⟩
    have notKing : a.target rs v ≠ sk := by rw [equal]; exact (slot_not_rook rx ry).symm
    have notWeak : a.target rs v ≠ wk := by
      rw [ne_iff_coords]
      have positive := (slot_geometry i).1
      omega
    have far : 2 ≤ dInf sk wk := by rw [equal]; exact slot_far file rank i
    have legal := rook_entry_legal material turn far sees notKing notWeak last
    have next := (KRKMatingMove.rook_move_model material turn legal rfl).1
    have next' : IsKRK (play (RawTrace.erase s) ⟨rs, a.target rs v, none⟩) σ i.king (a.target rs v) wk := by
      simpa only [equal] using next
    have reply := slot_reply_legal next' (by rw [play_turn, turn]) file rank rx ry
    exact ⟨_, _, sees, notKing, notWeak, last, legal, reply, clear⟩

def CornerClear (s : RawTrace.State) (sk rs wk : Square) : Prop :=
  ((sk.2.val = 2 ∧ sk.1.val ≤ 1 ∧ 2 ≤ rs.1.val ∧ rs.2.val ≠ 0) ∨
   (sk.1.val = 2 ∧ sk.2.val ≤ 1 ∧ 2 ≤ rs.2.val ∧ rs.1.val ≠ 0)) ∨
    KingPoints s sk rs wk ∨ RookRays s sk rs wk

theorem high_clock_force_iff {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ) (high : 96 ≤ RawClock.clock s.val.trace)
    (file : wk.1.val = 0) (rank : wk.2.val = 0) :
    KRKHolding.F σ s ↔ CornerClear s.val sk rs wk := by
  rw [KRKThreePly.high_clock_force_iff material ongoing turn high]
  simp only [ThreeHistory, CornerClear, immediate_corner_iff file rank,
    king_history_iff material turn file rank, rook_history_iff material turn file rank]

theorem high_clock_actual_iff {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ) (high : 96 ≤ RawClock.clock s.val.trace)
    (file : wk.1.val = 0) (rank : wk.2.val = 0) :
    KRKWinning.ActualWin σ s ↔ CornerClear s.val sk rs wk :=
  (KRKWinning.actual_win_iff_force (Or.inl ⟨sk, rs, wk, material⟩)).trans
    (high_clock_force_iff material ongoing turn high file rank)

theorem high_clock_hold_iff {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ) (high : 96 ≤ RawClock.clock s.val.trace)
    (file : wk.1.val = 0) (rank : wk.2.val = 0) :
    KRKHolding.RuleHold σ.opp s ↔ ¬CornerClear s.val sk rs wk := by
  have dual := KRKHolding.holding_iff_not_force (σ := σ) (c := σ.opp)
    (s := s) (Or.inl ⟨sk, rs, wk, material⟩)
  simpa only [opp_opp, high_clock_force_iff material ongoing turn high file rank] using dual

theorem high_clock_distance_cases {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ) (high : 96 ≤ RawClock.clock s.val.trace)
    (file : wk.1.val = 0) (rank : wk.2.val = 0) (win : KRKHolding.F σ s) :
    (KRKImmediate.MateNow sk rs wk ∧ KRKHolding.W σ 1 s ∧ ¬KRKHolding.W σ 0 s) ∨
      (¬KRKImmediate.MateNow sk rs wk ∧ KRKHolding.W σ 3 s ∧ ¬KRKHolding.W σ 2 s) := by
  by_cases immediate : KRKImmediate.MateNow sk rs wk
  · obtain ⟨v, edge, goal⟩ := (KRKImmediate.admitted_immediate_iff material ongoing turn).mpr immediate
    refine Or.inl ⟨immediate, Or.inr ⟨ongoing, Or.inl ⟨turn, v, edge, goal⟩⟩, ?_⟩
    intro zero
    exact opp_ne σ (turn.symm.trans zero.1)
  · have result := KRKThreePly.high_clock_exact_three material ongoing turn high
    exact Or.inr ⟨immediate, result.1.mp win, result.2 immediate⟩

end EndgameChess.Rules.KRKCornerSlotBarriers
