# EC-C031 — Effective en-passant normalization preserves legal play

S050, 2026-10-20. Classical kernel reasoning, no novelty claim.

## Definitions and exact statement

For every raw Position q define noncomputable normalizeEP q =
{q with ep := effectiveEP q}. effectiveEP retains q.ep iff some actual legal
LegalEP event exists and otherwise is none (frozen EC-T0026 definitions).
For EVERY raw q and actual Move m, including its promotion choice:

isLegal (normalizeEP q) m = isLegal q m AND
(isLegal q m = true → play (normalizeEP q) m = play q m).

The first is Boolean equality, the second FULL Position equality. No assumption
of legal arrival, compatible history, correct flags, material, side or terminal.

## Complete proof

Split whether ∃move,LegalEP q move. If so effectiveEP q=q.ep by definition,
normalizeEP q=q by record equality, and both conclusions are reflexive.

Otherwise effectiveEP q=none. Split raw EP shape:
Pawn q m ∧ different source/destination files ∧ empty destination.
Outside the shape, frozen EC-T0028 ordinary_ep_irrelevance, with replacement
marker effectiveEP q, gives identical isPseudo and full play. normalizeEP keeps
turn, so the inCheck test after play has the same position and colour; unfolding
isLegal gives Boolean equality. The full play equality needs no legality here.

Inside the shape, original isLegal q m cannot be true: frozen EC-T0027
legalEP_iff_shape would yield LegalEP q m and contradict absence of any witness.
Thus original Boolean is false. Normalized board/turn are unchanged and ep=none.
Distinct finite files imply dx≠0 (if integer difference zero, Fin.ext identifies
the files). Unfold isPseudo on the source pawn and pawnMoveOK. Straight
single/double clauses require dx=0 and are false; empty dst makes ordinary
capture false; none marker makes EP equality false. Hence normalized isPseudo
and isLegal are false. Both Booleans equal false. The second conclusion's actual
original legality premise is contradictory. This covers every move and proves
both statements without asserting equality of raw illegal EP play.

## Scope and attribution

Definitions/proofs imported unchanged: RawRepetition.Definitions, OrdinaryEP,
EPCharacterization; Rules.Moves (isPseudo,pawnMoveOK,play,isLegal,inCheck), Board.dx.
Normalization definition is NEW, not a change to frozen effectiveEP. This is
one kernel prerequisite for a repetition key. It does not establish a full
FIDE key/Article9.2.3/rights-history correspondence, history admissibility,
claims/automatic-draw adjudication or mate precedence, strategy lifting,
numerical KRK, WDL/DTZ, solved class or initial-position result. No enumeration,
tablebase, engine or stored position certificates. Altered raw q need not have
an initial-rooted trace. No legal reply is discarded.
