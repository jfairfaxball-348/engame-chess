# EC-C032 — Normalized-key congruence for legal moves and endpoints

S052, 2026-10-20. Classical equality transport, no novelty claim.

## Exact definitions and theorem

Define NEW noncomputable key : Position → Position by key q = normalizeEP q,
where frozen normalizeEP replaces raw ep with frozen effectiveEP. Equality is
FULL normalized record equality: board function, turn, castling rights, effective
ep. No finite hash, board-only surrogate or executable search is introduced.
For every raw Position q,r, if key q=key r, then for every actual Move m:

isLegal q m=isLegal r m AND
(isLegal q m=true → play q m=play r m).

Booleans equal, full legal endpoints equal. Both colours, arbitrary flags,
promotions and malformed raw positions included. No compatible-history,
material, terminal or strategy assumption. No raw endpoint equality for illegal
moves. This is one-way normalized-key congruence, not a full FIDE identity iff.

## Complete proof

Fix q,r,key equality and m. Apply frozen normalizeEP_preserves separately at q
and r. Let normalized equality be Nq=Nr. Legality satisfies
isLegal q m = isLegal Nq m = isLegal Nr m = isLegal r m,
using symmetry of q preservation, congruence along normalized equality, and r
preservation. For an actually legal q move, that equality gives legality at r.
Then full endpoints satisfy
play q m = play Nq m = play Nr m = play r m,
using both legal endpoint preservation clauses and normalized equality. No
self-check or branch premise is changed; every Move remains quantified.

## Scope

Sources: frozen EC-T0029 NormalizationDefinitions/Normalization, EC-T0026–28
transitive dependencies; research/KRK_RULE_DISTANCE_SPEC.md for motivation.
This proves congruence under equality of the chosen key, not completeness of
Article9.2.3 identity, correctness of historical castling rights, count/claim/
adjudication semantics, strategy lifting, numerical KRK or WDL/DTZ. No history
is assumed for either raw position. No enumeration/engine/tablebase/stored
certificates. Later occurrence counting must use the SAME fixed equality/key
on the entire retained history, including initial/current positions.
