# EC-C030 — Raw ep-marker irrelevance outside en-passant shape

S048, 2026-10-20. Classical kernel branch reasoning, no novelty claim.

## Exact statement

For every raw kernel Position q, actual Move m (including its promotion choice),
and e : Option Square, put r = {q with ep := e}. Assume
H : ¬(RawClock.Pawn q m ∧ m.src.1 ≠ m.dst.1 ∧ q.board m.dst = none).
Then isPseudo r m = isPseudo q m AND play r m = play q m.
Pawn means q.board m.src = some ⟨q.turn, pawn⟩. The first equality is Boolean;
the second is equality of the FULL Position, including its board function.
No legality, reachability or valid-history hypothesis. All colours/raw flags.

## Complete proof

First the raw epCapture conjunction is false for any replacement marker a:
if true, Boolean equality gives Pawn, distinct files and empty destination,
contradicting H. Unfold play on q and r. Their source piece, turn and castling
rights coincide; both epCapture tests are false. Every board branch therefore
coincides pointwise, including source=destination ordering, promotion arrival
and castling rook movement. updateCastling has identical arguments. Output turn
is identical. Output ep is computed solely from source Pawn and rank displacement,
not the old marker, so it too is identical. Thus full played positions coincide.

For isPseudo split the source option. None returns false. For a source piece of
wrong colour the outer colour test is false. For a right-colour nonpawn, no
marker is read: attacksFrom uses only board and geometry, king's canCastle uses
only board, turn and castling rights. Promotion tests use the unchanged Move.
For a right-colour pawn, H implies either equal source/destination files or an
occupied destination. Equal files give dx=0 and pawnCaptureGeom=false, suppressing
the EP branch for both markers. An occupied destination makes its isNone test
false, also suppressing that branch. All single/double/ordinary capture clauses
have identical arguments. Hence pawnMoveOK and isPseudo coincide. This completes
both equalities without deleting any move from a later legal-game quantifier.

## Scope and sources

Definitions: Rules/Moves.lean (pawnMoveOK, isPseudo, canCastle, play,
updateCastling), Rules/Board.lean (dx), RawClock/Definitions.lean (Pawn).
This is a conditional raw-kernel lemma. It does not prove full effectiveEP
normalization, correctness of a FIDE repetition key, claims/adjudication,
KRK distance/outcomes or compatible histories for r. It does not use a tablebase,
engine, finite board enumeration or stored position certificates.
