# EC-C036 — Exact ongoing guards of a raw mate-first endpoint classifier

S060, 2026-10-20. Additive kernel bookkeeping following S032 §4, classical result.

Define NEW RawAdjudication.Stalemated(q) := inCheck q q.turn=false AND no kernel
Legal successor. DrawTrigger(s) := Stalemated(erase s) OR DeadK(erase s) OR
clock(s.trace)>=150 OR currentOccurrences(s)>=5. Define EndpointStatus as
mate(winner Colour), draw, ongoing. Noncomputable classify(s) first tests MatedK
and returns mate(q.turn.opp), then DrawTrigger and returns draw, else ongoing.
All existing Position/trace/threshold/game definitions frozen and unchanged.

For EVERY raw s, classify s=ongoing IFF
¬DeadK(erase s) AND (∃r,Legal(erase s)r) AND
clock(s.trace)<150 AND currentOccurrences(s)<5.

Forward: if MatedK, classifier returns mate, contradiction; if DrawTrigger,
returns draw, contradiction. Thus nondeadness/strict clock/count bounds follow.
If there is no Legal successor, split check Bool: true would give MatedK, false
would give Stalemated and DrawTrigger. Both impossible; some successor exists.
Reverse: existence of a Legal successor refutes both MatedK and Stalemated.
Nondeadness and strict thresholds refute every DrawTrigger disjunct; classifier
therefore returns ongoing. No legal successor is discarded to achieve this.

Audit mate at rawclock150 still first branch, not automatic draw; fivefold plus
mate malformed/raw overlap also mate-first by definition, NOT an extra FIDE9.6.1
priority theorem. S032 excludes feasible historical overlap via admissibility,
still unproved. Stalemate, dead and numeric draw overlaps all return draw after
mate test. At149/4 thresholds absent,150/5 present unless mate. Ongoing MAY have
claim thresholds100/3: optional claims are separate actions, not automatic draws.
No legal moves: check gives mate, no check gives stalemate, so never ongoing.
Both colours/all raw flags/promotions/history traces covered, no legal-history
compatibility assumed; raw traces can extend beyond earlier terminal states.

This supplies exact raw classifier guards, NOT certified FIDE adjudication,
rights-history/key identity, no-earlier-terminal admissibility, successful claims,
full Layer, strategy lifting, numerical KRK or WDL/DTZ. Source: S032 specification
§4 and retained FIDE source record; frozen kernel MatedK/DeadK and raw clock/count.
No new external source retrieval, full-game diagnostic, enumeration/oracle,
stored certificates or novelty claim. Mate priority is explicit model definition;
its historical/English-FIDE correctness remains a separate bridge.
