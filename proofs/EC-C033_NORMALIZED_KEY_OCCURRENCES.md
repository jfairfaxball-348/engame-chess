# EC-C033 — Current normalized-key occurrence count after actual append

S054, 2026-10-20. Classical bookkeeping specialization, no novelty claim.

## Definitions and exact statement

For every indexed raw trace t : RawTrace.Trace q and raw queried Position a,
define noncomputable occurrences t a := RawOccurrences.occurrences key t (key a),
with locally selected classical DecidableEq Position. Frozen key=normalizeEP,
equality FULL normalized Position, not board-only/hash. Define currentOccurrences s
:= occurrences s.trace (RawTrace.erase s). No global equality instance/search.

For every raw State s, actual Move m and proof hm:isLegal(erase s)m=true:
currentOccurrences(append s m hm) = occurrences s.trace (play(erase s)m) + 1.

## Complete proof

Unfold currentOccurrences and append's endpoint erase. Its endpoint is exactly
play(erase s)m, its trace is the actual stored snoc. Unfold occurrences, use the
same classical equality on both sides, and specialize frozen append_occurrences
with queried key a=key(play(erase s)m). The generic new-endpoint indicator is
if key(play(erase s)m)=key(play(erase s)m) then1else0, hence1 by reflexivity.
Thus the full prior history count of the NEW endpoint key plus one is exactly
the new current count. No trace replacement, endpoint approximation or legality
proof modification; hm remains stored in the actual append.

RawTrace.positions includes root and every endpoint by frozen append_spec.
Pawn/capture clock resets do not truncate this list. New definitions introduce
no such reset, terminal filter or strategy/reply restriction. Old query is NEW
endpoint key, not old current key. Symbolic [A,B,A] thenB gives new countB2;
old current countA2 plusone3 would be false. This is abstract list reasoning,
not a claim that such a compatible chess game was executed.

## Scope and sources

Frozen RawOccurrences.Definitions/Append and RawTrace.Append, frozen normalized
key definition, S032 specification. Both colours, arbitrary raw flags, promotions,
castling and every actual legal reply covered; no valid-history assumption.
No FIDE Article9.2.3/rights-history identity iff, repetition threshold/claim,
adjudication/mate precedence, strategy lifting, numerical KRK or WDL/DTZ result.
No enumeration/engine/tablebase/stored certificates or executable hash/search.
