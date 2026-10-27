import EndgameChess.Rules.KRKOppositionPrefix

namespace EndgameChess.Rules.KRKWeakPrefixEntry
open EndgameChess.KK KRKThreePly KRKLastReply KRKOppositionHistory
set_option maxHeartbeats 300000

/-- The first weak append adds no occurrence to either of the two keys in
any actual last-reply entry. The following weak move changes its king square. -/
theorem entry_queries_unchanged {s : RawTrace.State} {σ : Colour}
    {sk rs wk t ns nr u : Square} {m : Move}
    (material : IsKRK (RawTrace.erase s) σ sk rs wk)
    (turn : (RawTrace.erase s).turn = σ.opp) (safe : SafeRook sk rs wk)
    (firstLegal : isLegal (RawTrace.erase s) ⟨wk, t, none⟩ = true)
    (entryLegal : isLegal (firstBoard s wk t) m = true)
    (next : IsKRK (play (firstBoard s wk t) m) σ ns nr t)
    (last : LastReply ns nr t)
    (reply : isLegal (play (firstBoard s wk t) m) ⟨t, u, none⟩ = true) :
    RawRepetition.occurrences (RawTrace.append s ⟨wk, t, none⟩ firstLegal).trace
      (play (firstBoard s wk t) m) = RawRepetition.occurrences s.trace (play (firstBoard s wk t) m) ∧
    RawRepetition.occurrences (RawTrace.append s ⟨wk, t, none⟩ firstLegal).trace
      (play (play (firstBoard s wk t) m) ⟨t, u, none⟩) =
      RawRepetition.occurrences s.trace (play (play (firstBoard s wk t) m) ⟨t, u, none⟩) := by
  have first := weak_material_after material turn safe firstLegal
  have firstTurn : (firstBoard s wk t).turn = σ := by simp [firstBoard, play_turn, turn, opp_opp]
  have nextTurn : (play (firstBoard s wk t) m).turn = σ.opp := by rw [play_turn, firstTurn]
  have third := weak_material_after next nextTurn last.1 reply
  have moved : t ≠ u := by
    obtain ⟨v, post, step⟩ := krk_safe_reply next nextTurn last.1 ⟨_, reply, rfl⟩
    have same := congrArg Move.dst (weak_move_eq next nextTurn reply post.1)
    change u = v at same
    cases step with
    | lone distance _ _ _ =>
      rw [←same] at distance
      exact ne_of_dInf_pos (by omega)
  constructor
  · apply append_query firstLegal
    intro same
    have turns := congrArg Position.turn same
    change (firstBoard s wk t).turn = (play (firstBoard s wk t) m).turn at turns
    rw [firstTurn, nextTurn] at turns
    exact opp_ne σ turns
  · exact append_query firstLegal (weak_keys_ne first third moved)

/-- Generic original-trace form of a three-ply entry after an initial
quiet weak move. All moves are actual and all flags remain unchanged. -/
theorem entry_append_iff {s : RawTrace.State} {σ : Colour}
    {sk rs wk t ns nr u : Square} {m : Move}
    (material : IsKRK (RawTrace.erase s) σ sk rs wk)
    (turn : (RawTrace.erase s).turn = σ.opp) (safe : SafeRook sk rs wk)
    (firstLegal : isLegal (RawTrace.erase s) ⟨wk, t, none⟩ = true)
    (entryLegal : isLegal (firstBoard s wk t) m = true)
    (next : IsKRK (play (firstBoard s wk t) m) σ ns nr t)
    (last : LastReply ns nr t)
    (reply : isLegal (play (firstBoard s wk t) m) ⟨t, u, none⟩ = true) :
    EntryClear (RawTrace.append s ⟨wk, t, none⟩ firstLegal) m t u ↔
      RawClock.clock s.trace < 97 ∧
        RawRepetition.occurrences s.trace (play (firstBoard s wk t) m) < 2 ∧
        RawRepetition.occurrences s.trace (play (play (firstBoard s wk t) m) ⟨t, u, none⟩) < 2 := by
  have quiet := weak_safe_quiet material turn safe firstLegal
  have clock : RawClock.clock (RawTrace.append s ⟨wk, t, none⟩ firstLegal).trace = RawClock.clock s.trace + 1 := by
    rw [RawClock.append_clock, quiet]; rfl
  have queries := entry_queries_unchanged material turn safe firstLegal entryLegal next last reply
  change (RawClock.clock (RawTrace.append s ⟨wk, t, none⟩ firstLegal).trace < 98 ∧
    RawRepetition.occurrences (RawTrace.append s ⟨wk, t, none⟩ firstLegal).trace (play (firstBoard s wk t) m) < 2 ∧
    RawRepetition.occurrences (RawTrace.append s ⟨wk, t, none⟩ firstLegal).trace
      (play (play (firstBoard s wk t) m) ⟨t, u, none⟩) < 2) ↔ _
  rw [clock, queries.1, queries.2]
  omega

end EndgameChess.Rules.KRKWeakPrefixEntry
