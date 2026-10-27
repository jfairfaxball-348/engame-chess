import EndgameChess.Rules.KRKNearSlotBarriers
import EndgameChess.Rules.KRKForcing.AxisWalls

namespace EndgameChess.Rules.KRKVerticalNearSlotBarriers
open EndgameChess.KK KRKThreePly KRKLastReply RawHistoryLayer
set_option maxHeartbeats 400000

theorem last_swap_iff {sk rs wk : Square} :
    LastReply (symSwap.f sk) (symSwap.f rs) (symSwap.f wk) ↔ LastReply sk rs wk := by
  have safety : SafeRook (symSwap.f sk) (symSwap.f rs) (symSwap.f wk) ↔ SafeRook sk rs wk := by
    simp only [SafeRook, symSwap.dInf_eq]
  change (SafeRook (symSwap.f sk) (symSwap.f rs) (symSwap.f wk) ∧
    (HorizontalLast (symSwap.f sk) (symSwap.f rs) (symSwap.f wk) ∨ HorizontalLast sk rs wk)) ↔
    (SafeRook sk rs wk ∧ (HorizontalLast sk rs wk ∨
      HorizontalLast (symSwap.f sk) (symSwap.f rs) (symSwap.f wk)))
  rw [safety]
  constructor
  · rintro ⟨safe, horizontal | vertical⟩
    · exact ⟨safe, Or.inr horizontal⟩
    · exact ⟨safe, Or.inl vertical⟩
  · rintro ⟨safe, horizontal | vertical⟩
    · exact ⟨safe, Or.inr horizontal⟩
    · exact ⟨safe, Or.inl vertical⟩

theorem last_vertical_iff {sk rs wk : Square} (near : wk.2.val = 1) (edge : wk.1.val = 0) :
    LastReply sk rs wk ↔ sk.1.val = 2 ∧
      ((sk.2.val = 2 ∧ rs.2.val = 0 ∧ 2 ≤ rs.1.val) ∨
       (sk.2.val = 0 ∧ rs.2.val = 2 ∧ 2 ≤ rs.1.val) ∨
       (sk.2.val = 1 ∧ rs.2.val = 2 ∧ 1 ≤ rs.1.val)) := by
  exact last_swap_iff.symm.trans
    (KRKThreePly.last_near_iff (sk := symSwap.f sk) (rs := symSwap.f rs) (wk := symSwap.f wk) near edge)

theorem immediate_vertical_iff {sk rs wk : Square} (near : wk.2.val = 1) (edge : wk.1.val = 0) :
    KRKImmediate.MateNow sk rs wk ↔ sk.2.val = 1 ∧ sk.1.val = 2 ∧ rs.1.val ≠ 0 ∧ 3 ≤ rs.2.val := by
  simp [KRKImmediate.MateNow, KRKMateGeometry.Horizontal, KRKImmediate.rankTarget,
    KRKImmediate.fileTarget, RookSees, RookLine, OnSeg, absDiff, near, edge]
  omega

inductive Slot where
  | north | south | inner

def Slot.king : Slot → Square
  | .north => (2, 2)
  | .south => (2, 0)
  | .inner => (2, 1)

def Slot.rank : Slot → Fin 8
  | .north => 0
  | .south => 2
  | .inner => 2

def Slot.lower : Slot → Nat
  | .north => 2
  | .south => 2
  | .inner => 1

def Slot.reply : Slot → Square
  | .north => (0, 2)
  | .south => (0, 0)
  | .inner => (0, 0)

theorem slot_geometry (i : Slot) :
    i.king.1.val = 2 ∧ 1 ≤ i.lower ∧ i.reply.1.val = 0 ∧
    i.rank.val ≠ i.king.2.val ∧ i.rank.val ≠ i.reply.2.val := by
  cases i <;> decide

theorem slot_reply_distance {wk : Square} (near : wk.2.val = 1) (edge : wk.1.val = 0) (i : Slot) :
    dInf wk i.reply = 1 := by
  cases i <;> simp [Slot.reply, dInf, absDiff, near, edge]

theorem last_slots_iff {sk rs wk : Square} (near : wk.2.val = 1) (edge : wk.1.val = 0) :
    LastReply sk rs wk ↔ ∃ i : Slot, sk = i.king ∧ rs.2.val = i.rank.val ∧ i.lower ≤ rs.1.val := by
  rw [last_vertical_iff near edge]
  constructor
  · rintro ⟨sy, (⟨sx, rx, ry⟩ | ⟨sx, rx, ry⟩ | ⟨sx, rx, ry⟩)⟩
    · refine ⟨.north, ?_, rx, ry⟩
      apply Prod.ext <;> apply Fin.ext <;> assumption
    · refine ⟨.south, ?_, rx, ry⟩
      apply Prod.ext <;> apply Fin.ext <;> assumption
    · refine ⟨.inner, ?_, rx, ry⟩
      apply Prod.ext <;> apply Fin.ext <;> assumption
  · rintro ⟨i, equal, rx, ry⟩
    subst sk
    cases i <;> simp_all [Slot.king, Slot.rank, Slot.lower]

/-- A vertical last-reply slot supplies its actual legal weak return. -/
theorem file_return_legal {q : Position} {σ : Colour} {sk rs wk u : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp)
    (edge : wk.1.val = 0) (kingFile : sk.1.val = 2) (rookFile : 1 ≤ rs.1.val)
    (returnFile : u.1.val = 0) (notRank : rs.2.val ≠ u.2.val) (distance : dInf wk u = 1) :
    isLegal q ⟨wk, u, none⟩ = true := by
  apply lone_step_legal material turn
  refine StepM.lone distance ?_ ?_ ?_
  · rw [ne_iff_coords]; omega
  · simp [dInf, absDiff, kingFile, returnFile] <;> omega
  · intro sees
    rcases sees.1.2 with x | y <;> omega

def KingPoints (s : RawTrace.State) (sk rs wk : Square) : Prop :=
  ∃ i : Slot, rs.2.val = i.rank.val ∧ i.lower ≤ rs.1.val ∧ dInf sk i.king = 1 ∧
    EntryClear s ⟨sk, i.king, none⟩ wk i.reply

def AllowedFile (rs : Square) (i : Slot) (y : Fin 8) : Prop :=
  i.lower ≤ y.val ∧
    ((rs.2.val = i.rank.val ∧ rs.1.val ≠ y.val) ∨
     (rs.2.val ≠ i.rank.val ∧ rs.1.val = y.val ∧
       (rs.1.val ≠ 2 ∨ ¬((rs.2.val < i.king.2.val ∧ i.king.2.val < i.rank.val) ∨
          (i.rank.val < i.king.2.val ∧ i.king.2.val < rs.2.val)))))

theorem slot_sees_iff {sk rs wk : Square} {i : Slot} {y : Fin 8}
    (equal : sk = i.king) (near : wk.2.val = 1) (edge : wk.1.val = 0)
    (height : i.lower ≤ y.val) : RookSees rs (y, i.rank) sk wk ↔ AllowedFile rs i y := by
  subst sk
  cases i <;>
    dsimp [AllowedFile, RookSees, RookLine, OnSeg, Slot.rank, Slot.lower, Slot.king] at height ⊢ <;> omega

/-- Each rook destination is an explicitly allowed file on a fixed rank.
No legal-move or future-outcome predicate remains in this test. -/
def StripClear (s : RawTrace.State) (rs wk : Square) (i : Slot) : Prop :=
  ∃ y : Fin 8, AllowedFile rs i y ∧
    EntryClear s ⟨rs, (y, i.rank), none⟩ wk i.reply

def RookStrips (s : RawTrace.State) (sk rs wk : Square) : Prop :=
  ∃ i : Slot, sk = i.king ∧ StripClear s rs wk i

private theorem king_slot_not_rook {rs : Square} {i : Slot} (rx : rs.2.val = i.rank.val) : i.king ≠ rs := by
  rw [ne_iff_coords]
  have geometry := slot_geometry i
  omega

private theorem slot_far {wk : Square} (edge : wk.1.val = 0) (i : Slot) : 2 ≤ dInf i.king wk := by
  have geometry := (slot_geometry i).1
  simp [dInf, absDiff, edge, geometry] <;> omega

theorem king_history_iff {s : RawTrace.State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (RawTrace.erase s) σ sk rs wk) (turn : (RawTrace.erase s).turn = σ)
    (near : wk.2.val = 1) (edge : wk.1.val = 0) :
    KingHistoryEntry s sk rs wk ↔ KingPoints s sk rs wk := by
  constructor
  · rintro ⟨t, u, distance, notRook, far, last, legal, response, clear⟩
    obtain ⟨i, equal, rx, ry⟩ := (last_slots_iff near edge).mp last
    subst t
    have next := canonical_king_material material turn distance notRook far
    have geometry := slot_geometry i
    have reply := file_return_legal next (by rw [play_turn, turn]) edge geometry.1
      (by omega) geometry.2.2.1 (by omega) (slot_reply_distance near edge i)
    obtain ⟨_, _, unique⟩ := unique_legal_reply next (by rw [play_turn, turn]) far last
    have same : u = i.reply := congrArg Move.dst ((unique _ response).trans (unique _ reply).symm)
    exact ⟨i, rx, ry, distance, by simpa only [same] using clear⟩
  · rintro ⟨i, rx, ry, distance, clear⟩
    have notRook := king_slot_not_rook rx
    have far := slot_far edge i
    have last := (last_slots_iff near edge).mpr ⟨i, rfl, rx, ry⟩
    have legal := king_entry_legal material turn distance notRook far last
    have next := canonical_king_material material turn distance notRook far
    have geometry := slot_geometry i
    have reply := file_return_legal next (by rw [play_turn, turn]) edge geometry.1
      (by omega) geometry.2.2.1 (by omega) (slot_reply_distance near edge i)
    exact ⟨_, _, distance, notRook, far, last, legal, reply, clear⟩

theorem rook_history_iff {s : RawTrace.State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (RawTrace.erase s) σ sk rs wk) (turn : (RawTrace.erase s).turn = σ)
    (near : wk.2.val = 1) (edge : wk.1.val = 0) :
    RookHistoryEntry s sk rs wk ↔ RookStrips s sk rs wk := by
  constructor
  · rintro ⟨⟨y, x⟩, u, sees, _, _, last, legal, response, clear⟩
    obtain ⟨i, equal, rx, ry⟩ := (last_slots_iff near edge).mp last
    have fixed : x = i.rank := Fin.ext rx
    subst x
    have next := (KRKMatingMove.rook_move_model material turn legal rfl).1
    have geometry := slot_geometry i
    have reply := file_return_legal next (by rw [play_turn, turn]) edge
      (by rw [equal]; exact geometry.1) (Nat.le_trans geometry.2.1 ry) geometry.2.2.1
      geometry.2.2.2.2 (slot_reply_distance near edge i)
    have far := KRKEdgeDepth.arrival_far ⟨_, legal, rfl⟩ next
    obtain ⟨_, _, unique⟩ := unique_legal_reply next (by rw [play_turn, turn]) far last
    have same : u = i.reply := congrArg Move.dst ((unique _ response).trans (unique _ reply).symm)
    exact ⟨i, equal, y, (slot_sees_iff equal near edge ry).mp sees, by simpa only [same] using clear⟩
  · rintro ⟨i, equal, y, allowed, clear⟩
    have height := allowed.1
    have sees := (slot_sees_iff equal near edge height).mpr allowed
    have geometry := slot_geometry i
    have last : LastReply sk (y, i.rank) wk := (last_slots_iff near edge).mpr ⟨i, equal, rfl, height⟩
    have notKing : (y, i.rank) ≠ sk := by
      rw [ne_iff_coords, equal]; dsimp only; omega
    have notWeak : (y, i.rank) ≠ wk := by rw [ne_iff_coords]; dsimp only; omega
    have far : 2 ≤ dInf sk wk := by rw [equal]; exact slot_far edge i
    have legal := rook_entry_legal material turn far sees notKing notWeak last
    have next := (KRKMatingMove.rook_move_model material turn legal rfl).1
    have reply := file_return_legal next (by rw [play_turn, turn]) edge
      (by rw [equal]; exact geometry.1) (Nat.le_trans geometry.2.1 height) geometry.2.2.1
      geometry.2.2.2.2 (slot_reply_distance near edge i)
    exact ⟨_, _, sees, notKing, notWeak, last, legal, reply, clear⟩

def NearClear (s : RawTrace.State) (sk rs wk : Square) : Prop :=
  (sk.2.val = 1 ∧ sk.1.val = 2 ∧ rs.1.val ≠ 0 ∧ 3 ≤ rs.2.val) ∨
    KingPoints s sk rs wk ∨ RookStrips s sk rs wk

theorem high_clock_force_iff {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ) (high : 96 ≤ RawClock.clock s.val.trace)
    (near : wk.2.val = 1) (edge : wk.1.val = 0) :
    KRKHolding.F σ s ↔ NearClear s.val sk rs wk := by
  rw [KRKThreePly.high_clock_force_iff material ongoing turn high]
  simp only [ThreeHistory, NearClear, immediate_vertical_iff near edge,
    king_history_iff material turn near edge, rook_history_iff material turn near edge]

theorem high_clock_actual_iff {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ) (high : 96 ≤ RawClock.clock s.val.trace)
    (near : wk.2.val = 1) (edge : wk.1.val = 0) :
    KRKWinning.ActualWin σ s ↔ NearClear s.val sk rs wk :=
  (KRKWinning.actual_win_iff_force (Or.inl ⟨sk, rs, wk, material⟩)).trans
    (high_clock_force_iff material ongoing turn high near edge)

theorem high_clock_hold_iff {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ) (high : 96 ≤ RawClock.clock s.val.trace)
    (near : wk.2.val = 1) (edge : wk.1.val = 0) :
    KRKHolding.RuleHold σ.opp s ↔ ¬NearClear s.val sk rs wk := by
  have dual := KRKHolding.holding_iff_not_force (σ := σ) (c := σ.opp)
    (s := s) (Or.inl ⟨sk, rs, wk, material⟩)
  simpa only [opp_opp, high_clock_force_iff material ongoing turn high near edge] using dual

theorem high_clock_distance_cases {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ) (high : 96 ≤ RawClock.clock s.val.trace)
    (near : wk.2.val = 1) (edge : wk.1.val = 0) (win : KRKHolding.F σ s) :
    (KRKImmediate.MateNow sk rs wk ∧ KRKHolding.W σ 1 s ∧ ¬KRKHolding.W σ 0 s) ∨
      (¬KRKImmediate.MateNow sk rs wk ∧ KRKHolding.W σ 3 s ∧ ¬KRKHolding.W σ 2 s) := by
  by_cases immediate : KRKImmediate.MateNow sk rs wk
  · obtain ⟨v, edge, goal⟩ := (KRKImmediate.admitted_immediate_iff material ongoing turn).mpr immediate
    refine Or.inl ⟨immediate, Or.inr ⟨ongoing, Or.inl ⟨turn, v, edge, goal⟩⟩, ?_⟩
    intro zero
    exact opp_ne σ (turn.symm.trans zero.1)
  · have result := KRKThreePly.high_clock_exact_three material ongoing turn high
    exact Or.inr ⟨immediate, result.1.mp win, result.2 immediate⟩

end EndgameChess.Rules.KRKVerticalNearSlotBarriers
