# Four-ply KRK classification on the two middle edge files

For an exact weak-turn KRK board with kings separated by at least two squares,
W=(x,0), and 3<=x<=4, the checked equivalence is

    MateWithin(4)
      iff MatedK
          or LastReply(S,R,W)
          or [S=(x,2) and R.y>=3].

The first two clauses are terminal mate and the previously evaluated two-ply
region. The added region is direct opposition with a rook at least three
ranks inward. This is a complete four-ply board result on these two files,
not the full edge conjecture or a rule-aware four-ply outcome criterion.

## Necessity

Every legal weak reply must enter the complete three-ply region. Its weak king
must therefore lie on an edge, so the three inward neighbours are covered.
The two edge neighbours either are covered or satisfy the coordinate-only
central three-ply formula. Their files remain between two and five, which is
why this argument currently applies to x=3,4.

Covering the three inward neighbours forces either S.y=2 or R.y=1. In the
latter case, with S.y!=2, no three-ply edge entry is possible; rook safety
prevents both edge neighbours from being covered.

When S.y=2, separate the rook's rank. At rank zero the only surviving case is
terminal mate. Rank one cannot support all legal replies while retaining rook
safety. At rank two, the king blocks the crossing needed on one side unless
the position is already in LastReply. At rank three or above, inward coverage
forces either LastReply or S.x=x. The proof includes the nonempty reply and
terminal exceptions at the kernel level.

## Sufficiency

In the added opposition family all inward moves are king-controlled. Every
legal reply has destination (x-1,0) or (x+1,0). There is always at least one
legal reply: a rook file can exclude only one of those two squares. A reply
to (x-1,0) leaves a strong rook entry on file x-2; a reply to (x+1,0) leaves
one on file x+2. The original rook rank is at least three, so the crossing
avoids both kings. A rook already on the required file has a free vertical
ray. The coordinate three-ply theorem therefore applies to every reply.

The safe-rook theorem lifts all actual legal weak moves to this geometry,
including the capture boundary. Actual strong castling was already excluded
from all winning three-ply entries by the complete three-ply theorem.

## Lean correspondence

`KRKFourPlyMiddle.lean` proves `central_four_necessary`, `opposition_replies`,
and `weak_four_iff`. The focused build
`lake build EndgameChess.Rules.KRKFourPlyMiddle` passed. The distinct-piece
hypothesis matters in the rank-two crossing argument and is supplied by exact
KRK material at every kernel application.

The aggregate `lake build` passed (263 jobs), and `lake env lean AxiomCheck.lean`
passed with only `propext`, `Classical.choice`, and `Quot.sound` for the new
public declarations.

Incoming-history barriers for this added opposition family are now evaluated
separately in [the central weak history theorem](KRK_CENTRAL_WEAK_HISTORY.md).
That result checks the permitted rook ranks and both intermediate keys on
every legal weak branch. This board theorem alone does not establish a
RAW/FIDE winning history.
