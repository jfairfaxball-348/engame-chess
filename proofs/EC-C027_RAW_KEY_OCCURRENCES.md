# EC-C027 — Generic full raw-history key occurrences and exact append law

S042, 2026-10-20. Classical finite-list counting, no novelty claim. Sources:
frozen EC-T0021 Trace.positions/append_spec and S032 repetition specification
(occurrence convention only). No new FIDE repetition-key correctness claim,
engine, tablebase, class enumeration or per-position stored certificate.

## Definition and exact quantified statement

Fix ANY key type K with explicit decidable equality, and a FIXED function
key:Position→K. For a full indexed raw trace t:Trace q and queried a:K define

    occurrences(key,t,a)
      := length(filter (p ↦ decide(key(p)=a)) (t.positions)).

Decidable equality supplies the correct Boolean decision for propositional
key equality; an arbitrary unrelated Boolean equality is not assumed. The key
map is the same before and after the append. This count is DERIVED from full
stored data, not an independently supplied counter/vector. Trace.positions
includes both initial root and current endpoint, with every prior position.
Repeated equal entries count individually, including nonconsecutive occurrences.

For EVERY K, decidable equality, key, raw s, actual Move m, source legality
hm:isLegal(erase s)m=true, and queried key a:

    occurrences(key,(append s m hm).trace,a)
      = occurrences(key,s.trace,a)
        + (if key(play(erase s)m)=a then 1 else 0).

One shared definition module plus ONE main theorem module. No material, turn,
strategy, terminal, clock or repetition-threshold guard. Every raw legal append,
including resetting and draw-ending moves, retains all stored history.
No extra elementary monotonicity/bound/root theorem module is necessary.

## Proof and root computation

Frozen append_spec gives EXACTLY
(append s m hm).trace.positions=s.trace.positions++[play(erase s)m].
Filter distributes over list append. The filtered singleton contributes one
entry when the new endpoint key equals a, and no entries otherwise. Length of
an append is sum of lengths. These equations prove the exact displayed law.
No number of chess positions is enumerated and no FIDE key property is used.

At the empty-move root Trace.start, positions=[initial], not []. Thus the
same definition computes to 1 if key(initial)=a and 0 otherwise. The current
endpoint is already included for every stored trace. Appending adds exactly
one new endpoint; it does not recount or delete any earlier endpoint.

For a prospective/current child key a=key(new endpoint), the law specializes
to old-history occurrences of THAT NEW key plus one. The old-history queried
key is NOT necessarily the old current key. For example symbolic key-list
[A,B,A] followed by B gives a B count of 2, while the prior current A count was
2; adding one to the prior current count would incorrectly yield 3. This is
a symbolic list example, not a claimed compatible full chess game.

## Adversarial controls

Empty-move root contributes its one endpoint. Absent queried key gives zero
until a matching endpoint arrives. Equal/new keys contribute one/zero according
to actual equality; a previously seen key counts all earlier occurrences,
including separated ones. With a constant key map, every endpoint counts;
this valid generic choice shows why the map is not automatically a FIDE key.
Two traces sharing an erased board may have different counts because their
prior endpoint lists differ. Resetting the separate halfmove fold does not
truncate t.positions, so occurrence counting retains pre-reset positions.
Earlier raw draws do not block an otherwise kernel-legal append in this raw
statement; no lawful FIDE continuation is inferred. All controls symbolic;
no initial-rooted promotion/ep/castling/threshold game was constructed/run.

## Limits

An arbitrary key is NOT the FIDE repetition key. Effective legal en-passant,
Article 9.2.3 correspondence, history-derived rights fidelity, low-repetition
certificates, current/intended claims, no-earlier-terminal admissibility,
automatic fivefold/75-move adjudication, mate precedence, full Layer instance,
strategy extraction/rule-aware lifting, numerical KRK mate bound, holding/
outcome, DTM/DTZ/WDL/Syzygy parity and initial-position value remain separate.
No statement that all KRK histories have low repetitions or clock+n<100.
No adverse raw reply pruned; generic counting never upgrades a clock-free
force to a rule-aware win. Existing FIDE-to-kernel trust boundary unchanged.
