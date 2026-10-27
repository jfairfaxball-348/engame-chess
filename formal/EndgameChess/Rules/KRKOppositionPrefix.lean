import EndgameChess.Rules.KRKRookRayBarriers
import EndgameChess.Rules.KRKFourPlyMiddle

namespace EndgameChess.Rules.KRKOppositionHistory
open EndgameChess.KK KRKLastReply KRKThreePly KRKRookRayBarriers RawHistoryLayer

def firstBoard (s : RawTrace.State) (wk t : Square) : Position :=
  play (RawTrace.erase s) ⟨wk, t, none⟩

def rookBoard (s : RawTrace.State) (rs wk t : Square) (f y : Fin 8) : Position :=
  play (firstBoard s wk t) ⟨rs, (f, y), none⟩

def returnBoard (s : RawTrace.State) (sk rs wk t : Square) (f y : Fin 8) : Position :=
  play (rookBoard s rs wk t f y) ⟨t, (sk.1, 0), none⟩

/-- Query both later barrier keys in the trace before the first weak move. -/
def OriginalRay (s : RawTrace.State) (sk rs wk t : Square) (f : Fin 8) : Prop :=
  ∃ y : Fin 8, AllowedRank rs f y ∧
    RawRepetition.occurrences s.trace (rookBoard s rs wk t f y) < 2 ∧
    RawRepetition.occurrences s.trace (returnBoard s sk rs wk t f y) < 2

theorem weak_material_after {q : Position} {σ : Colour} {sk rs wk t : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp)
    (safe : SafeRook sk rs wk) (legal : isLegal q ⟨wk, t, none⟩ = true) :
    IsKRK (play q ⟨wk, t, none⟩) σ sk rs t := by
  obtain ⟨u, next, _⟩ := krk_safe_reply material turn safe ⟨_, legal, rfl⟩
  have same := congrArg Move.dst (weak_move_eq material turn legal next.1)
  change t = u at same
  simpa only [←same] using next.1

/-- Exact weak king squares are part of the normalized RAW key. -/
theorem weak_keys_ne {q r : Position} {σ : Colour} {sk rs wk ns nr nw : Square}
    (material : IsKRK q σ sk rs wk) (next : IsKRK r σ ns nr nw) (different : wk ≠ nw) :
    RawRepetition.key q ≠ RawRepetition.key r := by
  intro same
  have boards := congrArg Position.board same
  change q.board = r.board at boards
  have atWeak : q.board wk = some ⟨σ.opp, .king⟩ := by
    rw [material.2.2.2]; exact krkBoard_wk material.2.1 material.2.2.1
  rw [boards, next.2.2.2] at atWeak
  rcases krkBoard_some atWeak with ⟨_, bad⟩ | ⟨_, bad⟩ | ⟨equal, _⟩
  · exact opp_ne σ (congrArg Piece.colour bad).symm
  · have kind := congrArg Piece.kind bad; cases kind
  · exact different equal

theorem append_query {s : RawTrace.State} {m : Move} {q : Position}
    (legal : isLegal (RawTrace.erase s) m = true)
    (different : RawRepetition.key (play (RawTrace.erase s) m) ≠ RawRepetition.key q) :
    RawRepetition.occurrences (RawTrace.append s m legal).trace q =
      RawRepetition.occurrences s.trace q := by
  classical
  unfold RawRepetition.occurrences
  rw [RawOccurrences.append_occurrences]
  simp only [different, ↓reduceIte, Nat.add_zero]

/-- The first weak append contributes zero to each later rook-ray query:
one key has the opposite turn, the other a different weak king square. -/
theorem ray_queries_unchanged_of_last {s : RawTrace.State} {σ : Colour}
    {sk rs wk t : Square} {f y : Fin 8}
    (material : IsKRK (RawTrace.erase s) σ sk rs wk)
    (turn : (RawTrace.erase s).turn = σ.opp) (rank : wk.2.val = 0)
    (sy : sk.2.val = 2) (ry : 3 ≤ rs.2.val)
    (trank : t.2.val = 0) (last : LastReply sk (f, y) t)
    (side : Side sk t f) (legal : isLegal (RawTrace.erase s) ⟨wk, t, none⟩ = true)
    (allowed : AllowedRank rs f y) :
    RawRepetition.occurrences (RawTrace.append s ⟨wk, t, none⟩ legal).trace
      (rookBoard s rs wk t f y) = RawRepetition.occurrences s.trace (rookBoard s rs wk t f y) ∧
    RawRepetition.occurrences (RawTrace.append s ⟨wk, t, none⟩ legal).trace
      (returnBoard s sk rs wk t f y) = RawRepetition.occurrences s.trace (returnBoard s sk rs wk t f y) := by
  have safe : SafeRook sk rs wk := Or.inl (by simp [dInf, absDiff, rank] <;> omega)
  have first := weak_material_after material turn safe legal
  have firstTurn : (firstBoard s wk t).turn = σ := by simp [firstBoard, play_turn, turn, opp_opp]
  have far : 2 ≤ dInf sk t := by simp [dInf, absDiff, sy, trank] <;> omega
  have sees := (ray_sees_iff trank sy ry side allowed.1).mpr allowed
  have notKing : (f, y) ≠ sk := by
    rw [ne_iff_coords]; dsimp only; unfold Side at side; omega
  have notWeak : (f, y) ≠ t := by
    have height := allowed.1
    rw [ne_iff_coords]; dsimp only; omega
  have rookLegal := rook_entry_legal first firstTurn far sees notKing notWeak last
  have second := (KRKMatingMove.rook_move_model first firstTurn rookLegal rfl).1
  have secondTurn : (rookBoard s rs wk t f y).turn = σ.opp := by simp [rookBoard, play_turn, firstTurn]
  have returnLegal := return_legal first firstTurn trank sy side allowed.1 rookLegal
  have third := weak_material_after second secondTurn last.1 returnLegal
  constructor
  · apply append_query legal
    intro same
    have sameTurn := congrArg Position.turn same
    change (firstBoard s wk t).turn = (rookBoard s rs wk t f y).turn at sameTurn
    rw [firstTurn, secondTurn] at sameTurn
    exact opp_ne σ sameTurn
  · apply append_query legal
    apply weak_keys_ne first third
    intro equal
    have files := congrArg (fun u : Square => u.1.val) equal
    unfold Side at side
    dsimp only at files
    omega

theorem ray_queries_unchanged {s : RawTrace.State} {σ : Colour}
    {sk rs wk t : Square} {f y : Fin 8}
    (material : IsKRK (RawTrace.erase s) σ sk rs wk)
    (turn : (RawTrace.erase s).turn = σ.opp) (rank : wk.2.val = 0)
    (sy : sk.2.val = 2) (ry : 3 ≤ rs.2.val)
    (trank : t.2.val = 0) (low : 2 ≤ t.1.val) (high : t.1.val ≤ 5)
    (side : Side sk t f) (legal : isLegal (RawTrace.erase s) ⟨wk, t, none⟩ = true)
    (allowed : AllowedRank rs f y) :
    RawRepetition.occurrences (RawTrace.append s ⟨wk, t, none⟩ legal).trace
      (rookBoard s rs wk t f y) = RawRepetition.occurrences s.trace (rookBoard s rs wk t f y) ∧
    RawRepetition.occurrences (RawTrace.append s ⟨wk, t, none⟩ legal).trace
      (returnBoard s sk rs wk t f y) = RawRepetition.occurrences s.trace (returnBoard s sk rs wk t f y) := by
  exact ray_queries_unchanged_of_last material turn rank sy ry trank
    ((ray_last_iff trank low high sy side).mpr allowed.1) side legal allowed

/-- Convert a child ray test back to the exact original weak-root trace. -/
theorem ray_append_iff_of_last {s : RawTrace.State} {σ : Colour} {sk rs wk t : Square} {f : Fin 8}
    (material : IsKRK (RawTrace.erase s) σ sk rs wk)
    (turn : (RawTrace.erase s).turn = σ.opp) (rank : wk.2.val = 0)
    (sy : sk.2.val = 2) (ry : 3 ≤ rs.2.val)
    (trank : t.2.val = 0)
    (last : ∀ y : Fin 8, AllowedRank rs f y → LastReply sk (f, y) t)
    (side : Side sk t f) (legal : isLegal (RawTrace.erase s) ⟨wk, t, none⟩ = true) :
    ClearRay (RawTrace.append s ⟨wk, t, none⟩ legal) sk rs t f ↔
      RawClock.clock s.trace < 97 ∧ OriginalRay s sk rs wk t f := by
  have safe : SafeRook sk rs wk := Or.inl (by simp [dInf, absDiff, rank] <;> omega)
  have quiet := weak_safe_quiet material turn safe legal
  have clock : RawClock.clock (RawTrace.append s ⟨wk, t, none⟩ legal).trace = RawClock.clock s.trace + 1 := by
    rw [RawClock.append_clock, quiet]; rfl
  constructor
  · rintro ⟨time, y, allowed, first, second⟩
    rw [clock] at time
    have queries := ray_queries_unchanged_of_last material turn rank sy ry trank (last y allowed) side legal allowed
    change RawRepetition.occurrences (RawTrace.append s ⟨wk, t, none⟩ legal).trace
      (rookBoard s rs wk t f y) < 2 at first
    change RawRepetition.occurrences (RawTrace.append s ⟨wk, t, none⟩ legal).trace
      (returnBoard s sk rs wk t f y) < 2 at second
    rw [queries.1] at first
    rw [queries.2] at second
    exact ⟨by omega, y, allowed, first, second⟩
  · rintro ⟨time, y, allowed, first, second⟩
    have queries := ray_queries_unchanged_of_last material turn rank sy ry trank (last y allowed) side legal allowed
    refine ⟨?_, y, allowed, ?_, ?_⟩
    · rw [clock]; omega
    · change RawRepetition.occurrences (RawTrace.append s ⟨wk, t, none⟩ legal).trace
        (rookBoard s rs wk t f y) < 2
      rw [queries.1]; exact first
    · change RawRepetition.occurrences (RawTrace.append s ⟨wk, t, none⟩ legal).trace
        (returnBoard s sk rs wk t f y) < 2
      rw [queries.2]; exact second

theorem ray_append_iff {s : RawTrace.State} {σ : Colour} {sk rs wk t : Square} {f : Fin 8}
    (material : IsKRK (RawTrace.erase s) σ sk rs wk)
    (turn : (RawTrace.erase s).turn = σ.opp) (rank : wk.2.val = 0)
    (sy : sk.2.val = 2) (ry : 3 ≤ rs.2.val)
    (trank : t.2.val = 0) (low : 2 ≤ t.1.val) (high : t.1.val ≤ 5)
    (side : Side sk t f) (legal : isLegal (RawTrace.erase s) ⟨wk, t, none⟩ = true) :
    ClearRay (RawTrace.append s ⟨wk, t, none⟩ legal) sk rs t f ↔
      RawClock.clock s.trace < 97 ∧ OriginalRay s sk rs wk t f := by
  exact ray_append_iff_of_last material turn rank sy ry trank
    (fun y allowed => (ray_last_iff trank low high sy side).mpr allowed.1) side legal

end EndgameChess.Rules.KRKOppositionHistory
