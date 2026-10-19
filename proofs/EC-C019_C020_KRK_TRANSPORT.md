# EC-C019–020 — KRK strategy transport (S030)

Scope: clock-free `ForceMate`, either named strong colour. This is a bridge for
arbitrary setup, not a proof that every strong-turn KRK arrival wins.

## EC-C019: exact ordinary-move interface

An adjacent lone king can capture an unprotected rook: its one-square move has
an enemy non-king target; afterwards only separated kings remain. En-passant
flags cannot affect a king move, and the one-square move cannot be castling.
The resulting legal KK position is dead. Therefore a weak-turn forcing position
must have a distant or protected rook (`SafeRook`). Distinctness excludes distance
zero; failure of the safety disjunction gives precisely the capture hypotheses.

With all castling rights false, any strong legal move in exact KRK is a king
step or a rook slide onto an empty square. Own-piece and king-capture exclusions
rule out all occupied targets. Post-move self-check exclusion gives king
separation; rook attacks give a clear rook segment. Thus it is a `StepM` move,
with an exactly matching successor. Rights remain false after every legal move.
No assumption on an en-passant flag is required.

## EC-C020: one-way forcing transport

Let g be an involutive king-distance/rook-line/segment preserving board map.
A castling-free exact source position with a finite forcing proof transports
to any-flags position matching its mapped configuration. Induct on the source
`MateWithin` budget, returning `ForceMate` (no distance equality claimed).

At a strong choice, C019 projects the chosen source legal move to `StepM`;
map it and lift it to an actual target move. Apply induction to the successor.
At a weak node, the source forcing proof implies safety by C019. Safety maps.
The frozen safe-reply completeness theorem projects EVERY target legal reply;
map back by involution and lift to a source reply. Its source budget decreases,
so induction wins the target successor. Nonemptiness is transported from a
source reply in the opposite direction. The finite-branching forcing constructor
combines successor bounds. Castling-free rights persist on the source.
At a source mate, check maps by the exact KRK check formula, and any target
reply would map back to a forbidden source reply. Hence actual mate transports.

Applying this theorem to a canonical castling-free source and the unchanged
S029 rank-wall theorem gives oriented wall forcing with arbitrary target flags.
Reflected ranks and exchanged coordinates cover both rank and file directions.

## Setup strategy under investigation

Choose an axis where the kings differ by at least two. A distant rook can enter
the intermediate wall using the S029 entry theorem. A rook beyond the lone king
can enter even on the strong king's file, since that king lies outside the ray.
For a close rook, a far-file retreat changes the weak king's position: if the
original rank gap falls from two to one, king separation forces a horizontal
gap of at least two. That branch needs a perpendicular safe entry rather than
reuse of the original axis. Rook/strong-king on the same back rank additionally
needs a protected entry or a preparatory king move. These are obligations, not
assumed continuations. No full arbitrary-setup theorem is asserted here.

## EC-C021: off-rank setup

The direct entry extends to a rook above the strong king even when their files
coincide: the king lies below both endpoints and cannot block the ray. The same
safe-reply argument then wins. Coordinate transport extends this to other axes.

For positive vertical king gap two, assume the rook is off the strong king's
rank. A rook on the weak king's rank is excluded by no incoming check. If the
rook lies between the kings, use the wall immediately. Otherwise its rank is
below the strong king or above the weak king. If distant in file, use direct
entry, or perpendicular entry when the strong king blocks the vertical ray.
If close in file, slide horizontally to the far file (distance at least four).
Both kings are off that row, hence the ray is clear. A same-rank horizontal king
reply witnesses nonemptiness; every reply is a safe, noncapturing king step.
The rook retains file margin at least three. If the vertical king gap remains
two, direct entry works unless the strong king blocks, in which case the
horizontal gap is at least three and perpendicular entry works. If the gap
falls to one, separation forces horizontal gap at least two. The rook's rank
is at least two away from the new weak king: its old rank was outside the
original interval, which had length at least two. Perpendicular entry works.
The retreat consumes two plies and the entry at most two more; no recursion.
Same-rank strong king and rook remain an obligation. The off-rank theorem is
asserted only to the extent of completed formal checks.

## Same-rank completion attempt (before formalisation)

If rook and strong king share a rank and that rank is positive, step the king
one rank away from the weak king. The rook becomes an intermediate wall. It
is distant from the weak king, whose downward step on its old file is a legal
witness (the no-check hypothesis excludes that rook file). Every reply remains
above the wall and wins by S029.

On rank zero, with rook adjacent in file to the strong king, push it to rank
one. It is protected, so captures are illegal; the barrier covers all replies.
A reply on the old weak file exists: go up if weak rank is two, down otherwise.
That file differs from the rook's by no incoming check; resulting rank is at
least two, so both king and rook checks are avoided. Thus no stalemate.

If horizontal king gap is at least two, swap axes and use off-rank setup:
rook and strong king are distinct squares on the same original rank, hence
have distinct original files. If rook/weak file margin is at least two, direct
entry works. Otherwise no incoming check forces this margin to equal one.
With horizontal king gap at most one and rook distinct from both king files,
the rook is either adjacent to the strong king or two files away beyond the
weak king. In the latter case step the strong king onto the old weak file on
rank zero. It is then adjacent in file to the rook. The distant rook is safe
for the reply. Every legal reply remains at rank at least two: a downward move
to rank one would be adjacent to the newly aligned king. Every successor has
no incoming check and can use the protected rank-one entry just established.
This is a bounded preparation, not a recursive setup assumption.

## EC-C021 intended flagship and weak-turn corollary

The preceding finite cases prove exact strong-turn KRK wins whenever the lone
king is not currently in check: king separation follows from that fact and
piece distinctness. Normalize a gap of at least two by one of the four axis
maps, create a castling-free canonical source, run the positive-gap setup, and
transport its strategy back. A legal incoming move gives the no-check premise
by mover safety. This proves the requested strong-turn arbitrary-arrival target.

For a weak-turn exact position, the intended classification is: forcing iff
actual checkmate, or a nonempty legal reply set with every legal reply avoiding
KK capture. Necessity follows from terminal inversion and dead-KK obstruction.
For sufficiency, each noncapturing reply is an actual strong-turn KRK legal
arrival, so the flagship applies; finite branching combines the bounds. This
classification is about the clock-free kernel and named strong winner, not
50-move/repetition outcomes or DTZ. It is to be claimed only after checking.
