import EndgameChess.Rules.KRKFresh.KeyMaterial
import EndgameChess.Rules.KRKFresh.PrefixRegion
namespace EndgameChess.Rules.KRKFresh
open EndgameChess.KK RawHistoryLayer KRKTermination

private theorem absent_count {σ : Colour} {q : Position} (trace : RawTrace.Trace q)
    (absent : ¬Ever σ trace) (r : Position) (query : Query σ r) :
    RawRepetition.occurrences trace r = 0 := by
  classical
  have empty : trace.positions.filter (fun p => decide (RawRepetition.key p = RawRepetition.key r)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro p member hit
    have same : RawRepetition.key p = RawRepetition.key r := of_decide_eq_true hit
    exact absent ⟨p,member,key_material same query⟩
  change (trace.positions.filter (fun p => decide (RawRepetition.key p = RawRepetition.key r))).length = 0
  rw [empty]
  rfl

/-- At actual nondead clock-zero endpoints, EVERY KRK query has full count at most one. -/
theorem clock_zero_counts (s : State) (σ : Colour)
    (zero : RawClock.clock s.val.trace = 0) (nondead : ¬DeadK (erase s)) :
    ∀ r, Query σ r → RawRepetition.occurrences s.val.trace r ≤ 1 := by
  classical
  rcases s with ⟨⟨q,trace⟩,admitted⟩
  cases trace with
  | start =>
    have absent : ¬Ever σ .start := by
      rintro ⟨p,member,sk,rs,wk,material⟩
      have same : p = initial := by simpa only [RawTrace.Trace.positions,List.mem_singleton] using member
      subst p
      exact initial_not_KRK σ sk rs wk material
    intro r query
    have count := absent_count .start absent r query
    change RawRepetition.occurrences .start r ≤ 1
    omega
  | @snoc q prior m hm =>
    have absent : ¬Ever σ prior := by
      intro earlier
      have parent := prefix_region prior admitted.1 earlier
      have ongoing : Ongoing (⟨⟨q,prior⟩,admitted.1⟩ : State) := admitted.2
      obtain ⟨sk,rs,wk,material⟩ := parent.resolve_right (not_not_intro ongoing)
      rcases krk_legal_material_clock material hm with ⟨_,_,_,_,quiet⟩ | ⟨_,_,_,dead⟩
      · change RawClock.zeroing q m = false at quiet
        have clock : RawClock.clock (.snoc prior m hm) = RawClock.clock prior + 1 := by
          simp only [RawClock.clock,quiet,Bool.false_eq_true,↓reduceIte]
        change RawClock.clock (.snoc prior m hm) = 0 at zero
        omega
      · exact nondead dead
    intro r query
    have old := absent_count prior absent r query
    have oldCount : (prior.positions.filter (fun p => decide (RawRepetition.key p = RawRepetition.key r))).length = 0 := old
    change ((prior.positions ++ [play q m]).filter
      (fun p => decide (RawRepetition.key p = RawRepetition.key r))).length ≤ 1
    rw [List.filter_append,List.length_append,oldCount]
    by_cases same : RawRepetition.key (play q m) = RawRepetition.key r <;> simp [same]
end EndgameChess.Rules.KRKFresh
