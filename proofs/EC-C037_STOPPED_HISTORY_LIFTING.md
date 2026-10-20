# EC-C037 — Stopped-history append and full legal-reply lifting

S062, 2026-10-20. Classical structural prerequisite for S032 §2/4, relative to
the chosen raw mate-first classifier. No novelty claim.

## Definitions and exact statement

Use the frozen indexed `RawTrace.Trace q`, rooted at `initial`, storing every
actual move and its legality proof. A raw state is exactly `s = ⟨q, prior⟩`.
Define a NEW predicate `StoppedHistory.Admissible` recursively on this data:
`Admissible Trace.start := True`; and
`Admissible (@Trace.snoc q prior m hm) := Admissible prior ∧
 RawAdjudication.classify ⟨q, prior⟩ = .ongoing`.
The parent passed to classify carries the exact indexed endpoint and prior trace.
It is not reconstructed from its board, clock or arbitrary occurrence counts.

For EVERY raw state s, prove the conjunction of:

1. For EVERY move m and proof hm of `isLegal (erase s) m = true`,
   `Admissible (append s m hm).trace ↔
    Admissible s.trace ∧ classify s = .ongoing`.
2. If `Admissible s.trace` and `classify s = .ongoing`, then for EVERY r with
   `Legal (erase s) r`, there is t with `Admissible t.trace ∧
    RawBoardStep s t ∧ erase t = r`.

No child-ongoing hypothesis or conclusion is included.

## Proof before Lean

For (1), unpack s as its endpoint q and exact stored prior trace. Frozen append
is exactly `⟨play q m, Trace.snoc prior m hm⟩`. The defining snoc equation gives
precisely `Admissible prior ∧ classify ⟨q, prior⟩ = .ongoing` in both directions.
There is no induction, move-case restriction or replacement of any trace.

For (2), unfold the frozen meaning of Legal: obtain an actual m, its legality
proof hm, and the equality identifying r with `play (erase s) m`. Choose
`t := append s m hm`. Part (1)'s reverse direction gives its admissibility.
The same m and hm witness RawBoardStep by reflexivity; erase t is r by the
Legal witness equality. Thus EVERY legal reply is represented, irrespective
of the child's classifier. This matches the full-reply obligation of the
abstract HistoryLayer interface, but does not construct a Layer here.

## Boundary and model scope

The start trace is admitted without testing its current endpoint. The first
append tests precisely the start parent. Each later append tests its own parent;
recursion therefore imposes ongoing status on every strict prefix, permitting a
terminal current endpoint. If parent status is terminal, (1) excludes every
legal append even if the kernel still permits board moves; if child is terminal,
it remains admitted and may not subsequently append. Claim availability is not
an automatic terminal trigger. The trace describes board moves with declined
optional claims, never a successful/invalid claim or a procedural claim phase.

All moves, colours, promotions and raw flags are quantified without a material
restriction. Initial-rooted flags are inherited from frozen Trace/play, but no
new historical-rights or FIDE repetition-key correspondence is proved. This is
admissibility relative to the CHOSEN RAW classifier, not certified full FIDE
legal-history/adjudication or claim-protocol correctness. No strategy lifting,
numerical KRK bound, holding/outcome, WDL/DTZ or initial-position value follows.
Sources: frozen RawTrace Definitions/Append/Completeness/Soundness,
RawAdjudication Definitions/Ongoing (EC-T0034), HistoryLayer interface and S032
§2/4. No external retrieval, enumeration, oracle, per-position certificates or
full-game diagnostic was used.
