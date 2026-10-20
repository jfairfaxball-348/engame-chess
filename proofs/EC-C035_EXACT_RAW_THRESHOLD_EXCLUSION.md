# EC-C035 — Exact complement of raw current/intended thresholds

S058, 2026-10-20. Classical logical bookkeeping, no novelty claim.

For EVERY raw state s, ¬AvailableThreshold s iff:
clock s.trace<100 AND currentOccurrences s<3 AND
for EVERY actual m/hm legal from erase s,
clock(append s m hm).trace<100 AND
occurrences s.trace(play(erase s)m)<2.
All predicates/types are frozen RawClaims/RawClock/RawRepetition/RawTrace.
Actual indexed child and hm retained, full normalized key and history unchanged.

Forward: a root clock or repetition threshold gives AvailableThreshold by left
injection, so both root bounds follow by Nat order complement. For arbitrary
m/hm, either child threshold gives intended availability by existential witness,
so both child bounds follow. Frozen append_currentOccurrences rewrites childcount
as old queried NEW endpoint count+1. Nat arithmetic gives query<2 iff childcount<3.
Reverse: root bounds refute CurrentThreshold. Any intended witness m/hm has child
clock<100 and queriedcount<2 by universal hypothesis, hence childcount<3 by frozen
append law. Both child disjuncts impossible, so IntendedThreshold impossible and
AvailableThreshold false. This proves exact IFF without a uniform root+1 clock
budget. Actual child clock remains: zeroing/reset branches are not approximated.

Audits: root99 below threshold, root100 not; rootcount2 below3, childoldquery1
becomes2, childoldquery2 becomes3. Child bounds do not replace separate root bounds.
No replies makes universal vacuous but root bounds still necessary. Pseudo-only
moves lack actual hm; EVERY legal intended move remains quantified, promotions,
flags/colours unrestricted. New endpoint query not parent current count. No raw
illegal-play equality, terminal/history/material/strategy filter. No concrete
full-game diagnostic, enumeration/engine/tablebase/stored certificates.

Scope: exact characterization of RAW thresholds, not FIDE key/rights-history
identity, certified CanClaim/claim protocol, lawful histories/adjudication/automatic
draw/mate precedence, strategy lifting, numerical KRK, WDL/DTZ or solved class.
Sources: frozen RawClaims.Definitions, RawRepetition.CurrentAppend, S032 specification.
