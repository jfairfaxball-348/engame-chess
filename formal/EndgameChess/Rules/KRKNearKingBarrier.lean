import EndgameChess.Rules.KRKThreePlyNearCorner
import EndgameChess.Rules.KRKThreePlyHistory
import EndgameChess.Rules.KRKRookRayBarriers

namespace EndgameChess.Rules.KRKNearKingBarrier
open EndgameChess.KK KRKThreePly KRKLastReply RawHistoryLayer
set_option maxHeartbeats 300000

def KingClear (s : RawTrace.State) (sk wk : Square) : Prop :=
  EntryClear s ⟨sk, ((1 : Fin 8), (2 : Fin 8)), none⟩ wk ((0 : Fin 8), (0 : Fin 8))

/-- The extra near-corner king entry has a fixed destination and fixed
weak reply; its only history tests are the two original keys. -/
theorem king_history_iff {s : RawTrace.State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (RawTrace.erase s) σ sk rs wk)
    (turn : (RawTrace.erase s).turn = σ)
    (sx : sk.1.val = 2) (sy : sk.2.val = 2)
    (file : wk.1.val = 1) (rank : wk.2.val = 0) (ry : 3 ≤ rs.2.val) :
    KingHistoryEntry s sk rs wk ↔ rs.1.val = 2 ∧ KingClear s sk wk := by
  have distance : dInf sk ((1 : Fin 8), (2 : Fin 8)) = 1 := by simp [dInf, absDiff, sx, sy]
  have notRook : ((1 : Fin 8), (2 : Fin 8)) ≠ rs := by rw [ne_iff_coords]; dsimp only; omega
  have far : 2 ≤ dInf ((1 : Fin 8), (2 : Fin 8)) wk := by simp [dInf, absDiff, file, rank]
  have next := canonical_king_material material turn distance notRook far
  have reply (rookFile : rs.1.val = 2) : isLegal (play (RawTrace.erase s) ⟨sk, ((1 : Fin 8), (2 : Fin 8)), none⟩)
      ⟨wk, ((0 : Fin 8), (0 : Fin 8)), none⟩ = true := by
    apply lone_step_legal next (by rw [play_turn, turn])
    refine StepM.lone ?_ ?_ ?_ ?_
    · simp [dInf, absDiff, file, rank]
    · rw [ne_iff_coords]; dsimp only; omega
    · simp [dInf, absDiff]
    · rintro ⟨⟨_, alignment⟩, _, _⟩
      dsimp only at alignment
      rcases alignment with x | y <;> omega
  constructor
  · rintro ⟨t, u, step, _, _, last, legal, response, clear⟩
    have shape := (last_near_iff file rank).mp last
    have shapeStep := step
    simp only [dInf, absDiff, sx, sy] at shapeStep
    have tx : t.1.val = 1 := by omega
    have ty : t.2.val = 2 := shape.1
    have rookFile : rs.1.val = 2 := by omega
    have fixed : t = ((1 : Fin 8), (2 : Fin 8)) := by
      apply Prod.ext <;> apply Fin.ext <;> assumption
    subst t
    obtain ⟨_, _, unique⟩ := unique_legal_reply next (by rw [play_turn, turn]) far last
    have sameMove := (unique _ response).trans (unique _ (reply rookFile)).symm
    have same : u = ((0 : Fin 8), (0 : Fin 8)) := congrArg Move.dst sameMove
    exact ⟨rookFile, by simpa only [KingClear, same] using clear⟩
  · rintro ⟨rookFile, clear⟩
    have last : LastReply ((1 : Fin 8), (2 : Fin 8)) rs wk :=
      (last_near_iff file rank).mpr ⟨rfl, Or.inr (Or.inr ⟨rfl, rookFile, by omega⟩)⟩
    have legal := king_entry_legal material turn distance notRook far last
    exact ⟨_, _, distance, notRook, far, last, legal, reply rookFile, clear⟩

theorem rook_history_iff {s : RawTrace.State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (RawTrace.erase s) σ sk rs wk)
    (turn : (RawTrace.erase s).turn = σ)
    (sx : sk.1.val = 2) (sy : sk.2.val = 2)
    (file : wk.1.val = 1) (rank : wk.2.val = 0) (ry : 3 ≤ rs.2.val) :
    RookHistoryEntry s sk rs wk ↔ KRKRookRayBarriers.ClearRay s sk rs wk (0 : Fin 8) := by
  have side : KRKRookRayBarriers.Side sk wk (0 : Fin 8) := Or.inl ⟨by omega, by omega⟩
  constructor
  · rintro ⟨⟨tx, ty⟩, u, sees, _, _, last, legal, response, clear⟩
    have shape := (last_near_iff file rank).mp last
    have targetFile : tx.val = 0 := by dsimp only at shape; omega
    have fixed : tx = (0 : Fin 8) := Fin.ext targetFile
    subst tx
    have height : 2 ≤ ty.val := by dsimp only at shape; omega
    have allowed := (KRKRookRayBarriers.ray_sees_iff rank sy ry side height).mp sees
    have reply := KRKRookRayBarriers.return_legal material turn rank sy side height legal
    have next := (KRKMatingMove.rook_move_model material turn legal rfl).1
    have far := KRKEdgeDepth.arrival_far ⟨_, legal, rfl⟩ next
    obtain ⟨_, _, unique⟩ := unique_legal_reply next (by rw [play_turn, turn]) far last
    have sameMove := (unique _ response).trans (unique _ reply).symm
    have same : u = (sk.1, 0) := congrArg Move.dst sameMove
    exact ⟨clear.1, ty, allowed, clear.2.1, by simpa only [same] using clear.2.2⟩
  · rintro ⟨clock, y, allowed, firstKey, secondKey⟩
    have last : LastReply sk ((0 : Fin 8), y) wk :=
      (last_near_iff file rank).mpr ⟨sy, Or.inl ⟨sx, rfl, allowed.1⟩⟩
    have sees := (KRKRookRayBarriers.ray_sees_iff rank sy ry side allowed.1).mpr allowed
    have notKing : ((0 : Fin 8), y) ≠ sk := by rw [ne_iff_coords]; dsimp only; omega
    have notWeak : ((0 : Fin 8), y) ≠ wk := by rw [ne_iff_coords]; dsimp only; omega
    have far : 2 ≤ dInf sk wk := by simp [dInf, absDiff, sy, rank] <;> omega
    have legal := rook_entry_legal material turn far sees notKing notWeak last
    have reply := KRKRookRayBarriers.return_legal material turn rank sy side allowed.1 legal
    exact ⟨_, _, sees, notKing, notWeak, last, legal, reply, clock, firstKey, secondKey⟩

/-- Complete RAW outcome for this previously missing branch: a clear rook
interval or the extra fixed king entry, each in the same incoming history. -/
theorem high_clock_force_iff {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ) (high : 96 ≤ RawClock.clock s.val.trace)
    (sx : sk.1.val = 2) (sy : sk.2.val = 2)
    (file : wk.1.val = 1) (rank : wk.2.val = 0) (ry : 3 ≤ rs.2.val) :
    KRKHolding.F σ s ↔ KRKRookRayBarriers.ClearRay s.val sk rs wk (0 : Fin 8) ∨
      (rs.1.val = 2 ∧ KingClear s.val sk wk) := by
  rw [KRKThreePly.high_clock_force_iff material ongoing turn high]
  have noImmediate : ¬KRKImmediate.MateNow sk rs wk := by
    rw [immediate_near_iff file rank]; omega
  simp only [ThreeHistory, noImmediate, false_or,
    king_history_iff material turn sx sy file rank ry,
    rook_history_iff material turn sx sy file rank ry, or_comm]

theorem high_clock_actual_iff {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ) (high : 96 ≤ RawClock.clock s.val.trace)
    (sx : sk.1.val = 2) (sy : sk.2.val = 2)
    (file : wk.1.val = 1) (rank : wk.2.val = 0) (ry : 3 ≤ rs.2.val) :
    KRKWinning.ActualWin σ s ↔ KRKRookRayBarriers.ClearRay s.val sk rs wk (0 : Fin 8) ∨
      (rs.1.val = 2 ∧ KingClear s.val sk wk) :=
  (KRKWinning.actual_win_iff_force (Or.inl ⟨sk, rs, wk, material⟩)).trans
    (high_clock_force_iff material ongoing turn high sx sy file rank ry)

theorem high_clock_hold_iff {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ) (high : 96 ≤ RawClock.clock s.val.trace)
    (sx : sk.1.val = 2) (sy : sk.2.val = 2)
    (file : wk.1.val = 1) (rank : wk.2.val = 0) (ry : 3 ≤ rs.2.val) :
    KRKHolding.RuleHold σ.opp s ↔ ¬(KRKRookRayBarriers.ClearRay s.val sk rs wk (0 : Fin 8) ∨
      (rs.1.val = 2 ∧ KingClear s.val sk wk)) := by
  have dual := KRKHolding.holding_iff_not_force (σ := σ) (c := σ.opp)
    (s := s) (Or.inl ⟨sk, rs, wk, material⟩)
  simpa only [opp_opp, high_clock_force_iff material ongoing turn high sx sy file rank ry] using dual

theorem high_clock_exact_three {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ) (high : 96 ≤ RawClock.clock s.val.trace)
    (sx : sk.1.val = 2) (file : wk.1.val = 1) (rank : wk.2.val = 0) :
    (KRKHolding.F σ s ↔ KRKHolding.W σ 3 s) ∧ ¬KRKHolding.W σ 2 s := by
  have result := KRKThreePly.high_clock_exact_three material ongoing turn high
  have noImmediate : ¬KRKImmediate.MateNow sk rs wk := by
    rw [immediate_near_iff file rank]; omega
  exact ⟨result.1, result.2 noImmediate⟩

end EndgameChess.Rules.KRKNearKingBarrier
