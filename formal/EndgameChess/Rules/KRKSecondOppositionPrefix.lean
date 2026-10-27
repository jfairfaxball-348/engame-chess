import EndgameChess.Rules.KRKOppositionPrefix
import EndgameChess.Rules.KRKNearKingBarrier

namespace EndgameChess.Rules.KRKSecondOppositionHistory
open EndgameChess.KK KRKThreePly KRKLastReply KRKOppositionHistory KRKRookRayBarriers
set_option maxHeartbeats 300000

def kingBoard (s : RawTrace.State) (sk wk t : Square) : Position :=
  play (firstBoard s wk t) ⟨sk, ((1 : Fin 8), (2 : Fin 8)), none⟩

def kingReturnBoard (s : RawTrace.State) (sk wk t : Square) : Position :=
  play (kingBoard s sk wk t) ⟨t, ((0 : Fin 8), (0 : Fin 8)), none⟩

def OriginalKing (s : RawTrace.State) (sk wk t : Square) : Prop :=
  RawRepetition.occurrences s.trace (kingBoard s sk wk t) < 2 ∧
  RawRepetition.occurrences s.trace (kingReturnBoard s sk wk t) < 2

theorem king_queries_unchanged {s : RawTrace.State} {σ : Colour} {sk rs wk t : Square}
    (material : IsKRK (RawTrace.erase s) σ sk rs wk)
    (turn : (RawTrace.erase s).turn = σ.opp) (rank : wk.2.val = 0)
    (sx : sk.1.val = 2) (sy : sk.2.val = 2) (rx : rs.1.val = 2) (ry : 3 ≤ rs.2.val)
    (tx : t.1.val = 1) (ty : t.2.val = 0)
    (legal : isLegal (RawTrace.erase s) ⟨wk, t, none⟩ = true) :
    RawRepetition.occurrences (RawTrace.append s ⟨wk, t, none⟩ legal).trace
      (kingBoard s sk wk t) = RawRepetition.occurrences s.trace (kingBoard s sk wk t) ∧
    RawRepetition.occurrences (RawTrace.append s ⟨wk, t, none⟩ legal).trace
      (kingReturnBoard s sk wk t) = RawRepetition.occurrences s.trace (kingReturnBoard s sk wk t) := by
  have safe : SafeRook sk rs wk := Or.inl (by simp [dInf, absDiff, rank] <;> omega)
  have first := weak_material_after material turn safe legal
  have firstTurn : (firstBoard s wk t).turn = σ := by simp [firstBoard, play_turn, turn, opp_opp]
  have distance : dInf sk ((1 : Fin 8), (2 : Fin 8)) = 1 := by simp [dInf, absDiff, sx, sy]
  have notRook : ((1 : Fin 8), (2 : Fin 8)) ≠ rs := by rw [ne_iff_coords]; dsimp only; omega
  have far : 2 ≤ dInf ((1 : Fin 8), (2 : Fin 8)) t := by simp [dInf, absDiff, tx, ty]
  have second := canonical_king_material first firstTurn distance notRook far
  have last : LastReply ((1 : Fin 8), (2 : Fin 8)) rs t :=
    (last_near_iff tx ty).mpr ⟨rfl, Or.inr (Or.inr ⟨rfl, rx, by omega⟩)⟩
  have secondTurn : (kingBoard s sk wk t).turn = σ.opp := by simp [kingBoard, play_turn, firstTurn]
  have reply : isLegal (kingBoard s sk wk t) ⟨t, ((0 : Fin 8), (0 : Fin 8)), none⟩ = true := by
    apply lone_step_legal second secondTurn
    refine StepM.lone ?_ ?_ ?_ ?_
    · simp [dInf, absDiff, tx, ty]
    · rw [ne_iff_coords]; dsimp only; omega
    · simp [dInf, absDiff]
    · rintro ⟨⟨_, alignment⟩, _, _⟩
      dsimp only at alignment
      rcases alignment with x | y <;> omega
  have third := weak_material_after second secondTurn last.1 reply
  constructor
  · apply append_query legal
    intro same
    have sameTurn := congrArg Position.turn same
    change (firstBoard s wk t).turn = (kingBoard s sk wk t).turn at sameTurn
    rw [firstTurn, secondTurn] at sameTurn
    exact opp_ne σ sameTurn
  · apply append_query legal
    apply weak_keys_ne first third
    intro same
    have files := congrArg (fun u : Square => u.1.val) same
    dsimp only at files
    omega

theorem king_append_iff {s : RawTrace.State} {σ : Colour} {sk rs wk t : Square}
    (material : IsKRK (RawTrace.erase s) σ sk rs wk)
    (turn : (RawTrace.erase s).turn = σ.opp) (rank : wk.2.val = 0)
    (sx : sk.1.val = 2) (sy : sk.2.val = 2) (rx : rs.1.val = 2) (ry : 3 ≤ rs.2.val)
    (tx : t.1.val = 1) (ty : t.2.val = 0)
    (legal : isLegal (RawTrace.erase s) ⟨wk, t, none⟩ = true) :
    KRKNearKingBarrier.KingClear (RawTrace.append s ⟨wk, t, none⟩ legal) sk t ↔
      RawClock.clock s.trace < 97 ∧ OriginalKing s sk wk t := by
  have safe : SafeRook sk rs wk := Or.inl (by simp [dInf, absDiff, rank] <;> omega)
  have quiet := weak_safe_quiet material turn safe legal
  have clock : RawClock.clock (RawTrace.append s ⟨wk, t, none⟩ legal).trace = RawClock.clock s.trace + 1 := by
    rw [RawClock.append_clock, quiet]; rfl
  have queries := king_queries_unchanged material turn rank sx sy rx ry tx ty legal
  change (RawClock.clock (RawTrace.append s ⟨wk, t, none⟩ legal).trace < 98 ∧
    RawRepetition.occurrences (RawTrace.append s ⟨wk, t, none⟩ legal).trace (kingBoard s sk wk t) < 2 ∧
    RawRepetition.occurrences (RawTrace.append s ⟨wk, t, none⟩ legal).trace (kingReturnBoard s sk wk t) < 2) ↔ _
  rw [clock, queries.1, queries.2]
  unfold OriginalKing
  omega

theorem west_ray_append_iff {s : RawTrace.State} {σ : Colour} {sk rs wk t : Square}
    (material : IsKRK (RawTrace.erase s) σ sk rs wk)
    (turn : (RawTrace.erase s).turn = σ.opp) (rank : wk.2.val = 0)
    (sx : sk.1.val = 2) (sy : sk.2.val = 2) (ry : 3 ≤ rs.2.val)
    (tx : t.1.val = 1) (ty : t.2.val = 0)
    (legal : isLegal (RawTrace.erase s) ⟨wk, t, none⟩ = true) :
    ClearRay (RawTrace.append s ⟨wk, t, none⟩ legal) sk rs t (0 : Fin 8) ↔
      RawClock.clock s.trace < 97 ∧ OriginalRay s sk rs wk t (0 : Fin 8) := by
  apply ray_append_iff_of_last material turn rank sy ry ty
  · intro y allowed
    exact (last_near_iff tx ty).mpr ⟨sy, Or.inl ⟨sx, rfl, allowed.1⟩⟩
  · exact Or.inl ⟨by omega, by omega⟩

/-- Both alternatives of the near-corner outcome use the weak root's
original trace, with one common clock bound. -/
theorem west_alternatives_append_iff {s : RawTrace.State} {σ : Colour} {sk rs wk t : Square}
    (material : IsKRK (RawTrace.erase s) σ sk rs wk)
    (turn : (RawTrace.erase s).turn = σ.opp) (rank : wk.2.val = 0)
    (sx : sk.1.val = 2) (sy : sk.2.val = 2) (ry : 3 ≤ rs.2.val)
    (tx : t.1.val = 1) (ty : t.2.val = 0)
    (legal : isLegal (RawTrace.erase s) ⟨wk, t, none⟩ = true) :
    (ClearRay (RawTrace.append s ⟨wk, t, none⟩ legal) sk rs t (0 : Fin 8) ∨
      (rs.1.val = 2 ∧ KRKNearKingBarrier.KingClear (RawTrace.append s ⟨wk, t, none⟩ legal) sk t)) ↔
      RawClock.clock s.trace < 97 ∧
        (OriginalRay s sk rs wk t (0 : Fin 8) ∨ (rs.1.val = 2 ∧ OriginalKing s sk wk t)) := by
  rw [west_ray_append_iff material turn rank sx sy ry tx ty legal]
  by_cases rx : rs.1.val = 2
  · rw [king_append_iff material turn rank sx sy rx ry tx ty legal]
    simp only [rx, true_and]
    constructor
    · rintro (⟨clock, ray⟩ | ⟨clock, king⟩)
      · exact ⟨clock, Or.inl ray⟩
      · exact ⟨clock, Or.inr king⟩
    · rintro ⟨clock, ray | king⟩
      · exact Or.inl ⟨clock, ray⟩
      · exact Or.inr ⟨clock, king⟩
  · simp only [rx, false_and, or_false]

end EndgameChess.Rules.KRKSecondOppositionHistory
