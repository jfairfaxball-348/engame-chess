# EC-C028 — Legality-filtered en-passant availability and effective target

S044, 2026-10-20. Classical existence-filtered target specification, no novelty
claim. Sources: frozen kernel pawnMoveOK/isLegal/play, EC-T0022 RawClock.Pawn
and CaptureEvent EP branch, S032 rule/distance specification §2. No engine,
tablebase, enumeration, stored certificate or executable-search claim.

## Exact event and construction

For arbitrary raw Position q and actual Move m, LegalEP(q,m) means the
conjunction of:

1. isLegal q m=true;
2. RawClock.Pawn q m, i.e. q.board m.src=some(q.turn,pawn);
3. q.ep=some m.dst;
4. m.src.file≠m.dst.file;
5. q.board m.dst=none;
6. q.board(m.dst.file,m.src.rank)=some(q.turn.opp,pawn).

The event is the existing frozen RawClock.CaptureEvent EP branch with actual
legality required. The kernel play's epCapture is a LOCAL let with source-pawn,
flag/destination, distinct-file and empty-destination tests. pawnMoveOK's ep
branch also requires capture geometry and opposing flank pawn; actual legality
requires pseudo-legality and no self-check. These are the unchanged underlying
kernel definitions, not a newly exported epCapture predicate. The present
specification asserts no new general material-count or English-FIDE equivalence.

Let Available(q):=∃m,LegalEP(q,m). Define

    effectiveEP(q) := if Available(q) then q.ep else none.

Use an explicitly NONCOMPUTABLE classical existence decision. No finite move
search/enumeration or new dependency is introduced. q is arbitrary raw kernel
data: lawful castling/ep history and no-earlier-terminal admissibility are not
assumed or proved. A later use may apply this map to actual trace endpoints.
No independent history/count/clock vector or arbitrary seeded KRK state.

## Exact combined main statement and proof

For EVERY q:

    (effectiveEP(q)=none ↔ ¬∃m,LegalEP(q,m)) ∧
    (∀dst, effectiveEP(q)=some dst ↔ ∃m,LegalEP(q,m) ∧ m.dst=dst).

Case Available false: effectiveEP is none. The first equivalence is true on
both sides; no witness exists for the second, whose left side is also false.

Case Available true: choose an actual witness m. Its flag clause gives
q.ep=some m.dst, so effectiveEP=q.ep is SOME and never none. Thus the first
equivalence is false on both sides. For any dst, effectiveEP=some dst and the
witness flag force m.dst=dst by injectivity of some; use m for the right side.
Conversely any witness m' with destination dst supplies q.ep=some dst; since
Available is true, that equals effectiveEP. This also shows all legal ep
witnesses have the SAME target, even if two source pawns are eligible.
Returning q.ep when Available holds cannot silently return none or another
square: consistency is PROVED from the actual event, not assumed separately.

One shared definitions module and one combined main theorem module suffice;
no extra public elementary clauses are needed. No material/colour/terminal/
strategy filter. Actual legality, not merely pseudo-legality, is essential.

## Symbolic adversarial controls

q.ep=none contradicts any witness flag. A present flag without any eligible
move still yields effectiveEP=none. If candidate ep moves are only pseudo-legal
and every one fails actual legality (for example through self-check), no legal
witness exists and the target is suppressed; no specific pinned board or full
compatible game is asserted as constructed/run. Multiple legal source pawns
share the destination fixed by q.ep. Occupied destination, wrong source kind/
colour, wrong flank pawn or an ordinary non-ep pawn/capture move fails the
explicit event clause(s); non-diagonal pawn moves fail distinct-file condition.
All statements are symbolic implications of exact predicates. No promotion/ep/
castling/threshold game prefix is required or reported as run. Malformed raw
flags are not certified as lawful FIDE histories by this total raw map.

## Limits

This gives only legality-filtered effective-target bookkeeping. No full
repetition key is chosen/certified; Article 9.2.3 correspondence and rights/ep
history fidelity remain open. No low-repetition certificate, current/intended
claims, no-earlier-terminal admissibility, automatic draws/mate precedence,
full Layer/strategy extraction/lifting, numerical KRK bound, holding/outcomes,
DTM/DTZ/WDL/Syzygy parity or initial-position value. Generic occurrence counting
is frozen but cannot turn this target spec into FIDE claim correctness. No
adverse reply pruned and no new solved class or frozen row follows. Existing
owner-reviewed FIDE-to-kernel trust boundary remains unchanged.
