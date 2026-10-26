# Coordinate-only three-ply KRK formula one file from the corner

Fix W=(1,0) and distinct S,R. The geometric Three predicate is exactly the
disjunction of the following seven rows. As before, on an exact strong-turn
legal arrival with separated kings this evaluates mate within three plies.

| Type | Coordinate condition |
|---|---|
| Immediate mate | S=(1,2), R.y!=0, R.x>=3 |
| King entry at (2,2) | R.x=0, R.y>=2, dInf(S,(2,2))=1 |
| King entry at (0,2) | R.x=2, R.y>=2, dInf(S,(0,2))=1 |
| King entry at (1,2) | R.x=2, R.y>=1, dInf(S,(1,2))=1 |
| Rook entry with S=(2,2) | R.x=0, or R.y>=3, or R.y=2 and R.x<2 |
| Rook entry with S=(0,2) | R.x=2, or R.y>=3, or R.y=2 and R.x>0 |
| Rook entry with S=(1,2) | R.x=2, or R.y=1, or R.y>=3, or R.y=2 and R.x>1 |

This is an explicit coordinate formula with no landing-square or game-value
quantifier. It is a board theorem, without a new full-history outcome claim.

## Boundary difference from the central edge

LastReply here reduces to S.y=2 and one of:

* S.x=2, R.x=0, R.y>=2;
* S.x=0, R.x=2, R.y>=2;
* S.x=1, R.x=2, R.y>=1.

The last alternative is the extra corner-offset placement. At rank one the
rook is protected by S=(1,2); the two-file-separated alternatives need rank
at least two. Thus there are three king slots rather than the central edge's
two. The rook-ray crossing rules then give the final three rows, including
the protected rank-one horizontal crossing.

For example, S=(2,2), R=(2,5), W=(1,0) admits the actual ordinary king entry
to (1,2). The subsequent unique weak reply is (0,0). The same starting geometry
also admits rook entries to file zero, which instead force a weak reply to
(2,0). These paths query different intermediate keys. The central proof that
all winning entries are rook moves does not apply here; a history extension
must retain the king option or prove it redundant under its exact hypotheses.
No such redundancy is claimed.

## Lean correspondence

`KRKThreePlyNearCorner.lean` defines NearThree and proves last_near_iff,
immediate_near_iff, king_entry_near_iff, rook_entry_near_iff and three_near_iff.
Vertical-ray witnesses are explicitly chosen at rank six or seven to differ
from the source; horizontal witnesses are the named rank/file crossings.
The focused build `lake build EndgameChess.Rules.KRKThreePlyNearCorner` passed.
The aggregate `lake build` passed (268 jobs), and `lake env lean AxiomCheck.lean`
passed with only `propext`, `Classical.choice`, and `Quot.sound` for the new
public declarations.

Remaining work includes the four-ply edge files and corners, their original
history barriers, the rest of the positive-clock class, and full FIDE/DTZ
correspondence. This result supplies the boundary case needed by that work.
