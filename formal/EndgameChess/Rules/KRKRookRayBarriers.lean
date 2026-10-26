import EndgameChess.Rules.KRKThreePlyMiddle
import EndgameChess.Rules.KRKThreePlyHistory

namespace EndgameChess.Rules.KRKRookRayBarriers
open EndgameChess.KK KRKThreePly KRKLastReply KRKImmediate RawHistoryLayer
set_option maxHeartbeats 500000

def Side (sk wk : Square) (f : Fin 8) : Prop :=
  (sk.1.val = wk.1.val + 1 ∧ f.val + 1 = wk.1.val) ∨
  (sk.1.val + 1 = wk.1.val ∧ f.val = wk.1.val + 1)

/-- An explicit rank interval on one file, excluding the source square.
A horizontal entry has its single crossing rank. -/
def AllowedRank (rs : Square) (f y : Fin 8) : Prop :=
  2 ≤ y.val ∧ ((rs.1.val = f.val ∧ rs.2.val ≠ y.val) ∨
    (rs.1.val ≠ f.val ∧ rs.2.val = y.val))

def ClearRay (s : RawTrace.State) (sk rs wk : Square) (f : Fin 8) : Prop :=
  RawClock.clock s.trace < 98 ∧ ∃ y : Fin 8, AllowedRank rs f y ∧
    RawRepetition.occurrences s.trace (play (RawTrace.erase s) ⟨rs, (f, y), none⟩) < 2 ∧
    RawRepetition.occurrences s.trace
      (play (play (RawTrace.erase s) ⟨rs, (f, y), none⟩) ⟨wk, (sk.1, 0), none⟩) < 2

theorem ray_last_iff {sk wk : Square} {f y : Fin 8}
    (rank : wk.2.val = 0) (low : 2 ≤ wk.1.val) (high : wk.1.val ≤ 5)
    (sy : sk.2.val = 2) (side : Side sk wk f) :
    LastReply sk (f, y) wk ↔ 2 ≤ y.val := by
  rw [last_middle_iff rank low high]
  dsimp only
  unfold Side at side
  omega

theorem ray_sees_iff {sk rs wk : Square} {f y : Fin 8}
    (rank : wk.2.val = 0) (sy : sk.2.val = 2) (ry : 3 ≤ rs.2.val)
    (side : Side sk wk f) (height : 2 ≤ y.val) :
    RookSees rs (f, y) sk wk ↔ AllowedRank rs f y := by
  simp only [RookSees, RookLine, OnSeg, AllowedRank]
  unfold Side at side
  omega

private theorem return_legal {q : Position} {σ : Colour} {sk rs wk : Square} {f y : Fin 8}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ)
    (rank : wk.2.val = 0) (sy : sk.2.val = 2) (side : Side sk wk f)
    (height : 2 ≤ y.val) (legal : isLegal q ⟨rs, (f, y), none⟩ = true) :
    isLegal (play q ⟨rs, (f, y), none⟩) ⟨wk, (sk.1, 0), none⟩ = true := by
  have next := (KRKMatingMove.rook_move_model material turn legal rfl).1
  apply lone_step_legal next (by rw [play_turn, turn])
  refine StepM.lone ?_ ?_ ?_ ?_
  · simp [dInf, absDiff, rank]
    unfold Side at side
    omega
  · rw [ne_iff_coords]; dsimp only; unfold Side at side; omega
  · simp [dInf, absDiff, sy]
  · simp [RookSees, RookLine]
    unfold Side at side
    omega

private theorem no_immediate {sk rs wk : Square} {f : Fin 8}
    (rank : wk.2.val = 0) (low : 2 ≤ wk.1.val) (high : wk.1.val ≤ 5)
    (side : Side sk wk f) : ¬MateNow sk rs wk := by
  rw [immediate_middle_iff rank low high]
  unfold Side at side
  omega

private theorem no_king_entry {sk rs wk : Square} {f : Fin 8}
    (rank : wk.2.val = 0) (low : 2 ≤ wk.1.val) (high : wk.1.val ≤ 5)
    (sy : sk.2.val = 2) (side : Side sk wk f) : ¬KingEntry sk rs wk := by
  rw [king_entry_middle_iff rank low high]
  simp only [CoordinateStep, absDiff, sy]
  unfold Side at side
  omega

/-- Exact interval-minus-two-key-barriers outcome, with all strong choices
eliminated, for the rook-entry branches of central opposition. -/
theorem high_clock_force_iff {s : State} {σ : Colour} {sk rs wk : Square} {f : Fin 8}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ) (highClock : 96 ≤ RawClock.clock s.val.trace)
    (rank : wk.2.val = 0) (low : 2 ≤ wk.1.val) (high : wk.1.val ≤ 5)
    (sy : sk.2.val = 2) (ry : 3 ≤ rs.2.val) (side : Side sk wk f) :
    KRKHolding.F σ s ↔ ClearRay s.val sk rs wk f := by
  rw [KRKThreePly.high_clock_force_iff material ongoing turn highClock]
  constructor
  · rintro (immediate | king | rook)
    · exact False.elim (no_immediate rank low high side immediate)
    · obtain ⟨t, _, distance, notRook, far, last, _⟩ := king
      exact False.elim (no_king_entry rank low high sy side ⟨t, distance, notRook, far, last⟩)
    · obtain ⟨⟨tx, ty⟩, u, sees, notKing, notWeak, last, legal, reply, clear⟩ := rook
      obtain ⟨_, height, geometry⟩ := (last_middle_iff rank low high).mp last
      have tf : tx = f := by
        apply Fin.ext
        unfold Side at side
        dsimp only at geometry
        omega
      subst tx
      have allowed := (ray_sees_iff rank sy ry side height).mp sees
      have returned := return_legal material turn rank sy side height legal
      have next := (KRKMatingMove.rook_move_model material turn legal rfl).1
      have nextFar := KRKEdgeDepth.arrival_far ⟨_, legal, rfl⟩ next
      obtain ⟨_, _, unique⟩ := unique_legal_reply next (by rw [play_turn, turn]) nextFar last
      have sameMove := (unique _ reply).trans (unique _ returned).symm
      have same : u = (sk.1, 0) := congrArg Move.dst sameMove
      change RawClock.clock s.val.trace < 98 ∧ _ ∧ _ at clear
      exact ⟨clear.1, ty, allowed, clear.2.1, by simpa only [same] using clear.2.2⟩
  · rintro ⟨clock, y, allowed, firstKey, secondKey⟩
    have last := (ray_last_iff rank low high sy side).mpr allowed.1
    have sees := (ray_sees_iff rank sy ry side allowed.1).mpr allowed
    have notKing : (f, y) ≠ sk := by rw [ne_iff_coords]; dsimp only; unfold Side at side; omega
    have notWeak : (f, y) ≠ wk := by
      have height := allowed.1
      rw [ne_iff_coords]; dsimp only; omega
    have far : 2 ≤ dInf sk wk := by simp [dInf, absDiff, sy, rank] <;> omega
    have legal := rook_entry_legal material turn far sees notKing notWeak last
    have reply := return_legal material turn rank sy side allowed.1 legal
    exact Or.inr (Or.inr ⟨(f, y), (sk.1, 0), sees, notKing, notWeak, last, legal, reply,
      clock, firstKey, secondKey⟩)

theorem high_clock_actual_iff {s : State} {σ : Colour} {sk rs wk : Square} {f : Fin 8}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ) (highClock : 96 ≤ RawClock.clock s.val.trace)
    (rank : wk.2.val = 0) (low : 2 ≤ wk.1.val) (high : wk.1.val ≤ 5)
    (sy : sk.2.val = 2) (ry : 3 ≤ rs.2.val) (side : Side sk wk f) :
    KRKWinning.ActualWin σ s ↔ ClearRay s.val sk rs wk f :=
  (KRKWinning.actual_win_iff_force (Or.inl ⟨sk, rs, wk, material⟩)).trans
    (high_clock_force_iff material ongoing turn highClock rank low high sy ry side)

/-- A barrier on every available rank gives a genuine holding policy,
against all strong alternatives, in the same RAW history layer. -/
theorem high_clock_hold_iff {s : State} {σ : Colour} {sk rs wk : Square} {f : Fin 8}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ) (highClock : 96 ≤ RawClock.clock s.val.trace)
    (rank : wk.2.val = 0) (low : 2 ≤ wk.1.val) (high : wk.1.val ≤ 5)
    (sy : sk.2.val = 2) (ry : 3 ≤ rs.2.val) (side : Side sk wk f) :
    KRKHolding.RuleHold σ.opp s ↔ ¬ClearRay s.val sk rs wk f := by
  have dual := KRKHolding.holding_iff_not_force (σ := σ) (c := σ.opp)
    (s := s) (Or.inl ⟨sk, rs, wk, material⟩)
  simpa only [opp_opp,
    high_clock_force_iff material ongoing turn highClock rank low high sy ry side] using dual

theorem high_clock_exact_three {s : State} {σ : Colour} {sk rs wk : Square} {f : Fin 8}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ) (highClock : 96 ≤ RawClock.clock s.val.trace)
    (rank : wk.2.val = 0) (low : 2 ≤ wk.1.val) (high : wk.1.val ≤ 5)
    (side : Side sk wk f) :
    (KRKHolding.F σ s ↔ KRKHolding.W σ 3 s) ∧ ¬KRKHolding.W σ 2 s := by
  have result := KRKThreePly.high_clock_exact_three material ongoing turn highClock
  exact ⟨result.1, result.2 (no_immediate rank low high side)⟩

end EndgameChess.Rules.KRKRookRayBarriers
