# EC-C019–021 and EC-C011 — finite safe KRK setup (S030)

This is a classical KRK mating result, not a novelty claim. Sources: the general
FIDE 2023 kernel and frozen KRK safety/forcing lemmas in this repository; the
unchanged S029 separated-wall strategy. No engine, tablebase or enumerated
position certificates supply a general argument. Earlier development notes are
retained in `EC-C019_C020_KRK_TRANSPORT.md`; this document is the final standalone
proof. The audits are same-agent adversarial reviews, not independent human review.

## Definitions and exact statements

Squares have files/ranks 0–7. Write S,R,W for strong king, rook, weak king;
d(A,B) is Chebyshev distance, and |a−b| is coordinate absolute difference.
Exact KRK means those three squares are distinct and contain precisely the
named pieces. `Matches` also fixes the turn. A safe rook is distant, d(R,W)≥2,
or king-protected, d(S,R)=1. `StepM` specifies ordinary rook slides and king
steps, with clear rays and post-move king/check safety. Its frozen soundness
lemma lifts each such move to a kernel-legal move, for any flags.

`ForceMate σ q` means a finite-rank strategy forcing actual mate of σ's opponent:
σ chooses a legal successor, the opponent has a nonempty legal reply set and
EVERY reply wins at smaller rank. Actual opponent mate is the zero-ply case.
The constructors derive nondeadness from the winning continuations and use
kernel finite branching to obtain a uniform finite bound. No clock, repetition
history or exact mating distance is encoded.

C019: a weak king adjacent to an unprotected rook has a legal KK capture;
therefore every weak-turn forcing KRK position has a safe rook. Every strong
legal move from castling-free exact KRK projects to an exact `StepM` successor.

C020: an involutive isometry preserving king distance and rook lines/segments
transports a forcing strategy from a castling-free exact KRK source to a
matching mapped destination with arbitrary flags. Consequently the S029 wall
and direct-entry theorems apply in both coordinate axes and directions.

C021: exact KRK on the strong turn, with the weak king not in check, has
`ForceMate σ q`. In particular **any exact strong-turn KRK with some legal
incoming move forces mate**, for either colour and arbitrary flags.

C011 completion: on the weak turn, forcing is equivalent to actual checkmate,
or a nonempty legal reply set in which no reply leaves KK. Equivalently it is
actual checkmate, or a safe rook and a nonempty reply set. These are clock-free
named-colour forcing classifications, not complete FIDE/Syzygy WDL/DTZ claims.

## 1. Exact kernel interface (C019)

For an adjacent unprotected rook, W→R is an ordinary king step with an enemy
non-king target. Its postboard contains only S and W on R, distance at least
two, so the mover is safe. King moves ignore en-passant, and a one-square move
cannot castle. A legal arrival in KK is dead by the frozen theorem. Therefore
such a reply contradicts a named strong forcing strategy. Distinctness excludes
distance zero; negation of the safety disjunction gives exactly these capture
hypotheses.

With all castling rights false, a strong legal mover is its king or rook. The
kernel prohibits own-piece destinations and king captures; hence its target is
empty. Pseudo-legality gives a one-square king step or clear rook ray and no
promotion. The exact simple-play board formula computes the successor; the
self-check exclusion gives separated kings afterwards. Thus the move projects
to `StepM` and exact matching. Castling rights can only be cleared by play, so
the source remains castling-free. No assumption on the source ep flag is needed.

## 2. Alternating strategy transport (C020)

Let g be an involution preserving king distance and rook geometry. Induct on
the source `MateWithin` budget, returning target `ForceMate` rather than equal
distance. At a strong node, project its chosen legal move using §1, map the
model move, lift at the target, and apply induction to its successor. Extra
strong choices in the target are immaterial to existence of this strategy.

At a weak winning node, §1 derives source rook safety, which maps by distance.
The frozen safe-reply completeness theorem projects every target legal reply
to a noncapturing king model step. Map back by involution, lift a legal source
reply, and use its decreased budget and induction. Source nonemptiness supplies
a target reply by the same construction in the forward direction. Finite
branching combines the target successor bounds. At a source mate, the KRK
check formula maps; any target reply would map to a forbidden source reply,
so the target is actually mated. No invariance of kernel deadness is assumed.

This is not unrestricted kernel symmetry: source castling is disabled. A weak
king has no own rook, so target castling cannot introduce extra weak replies.
Maps used are identity, rank reflection, coordinate swap, and anti-diagonal
reflection. Their distance/line/segment identities are proved symbolically.
Apply transport to a canonical castling-free mapped board and map back. Thus
any oriented strict wall S.rank<R.rank<W.rank wins on the strong turn by the
unchanged S029 theorem, even with a threatened rook before the strong move.

## 3. Safe direct entry

Normalize to W.rank≥S.rank+2. If rook/weak file margin is at least two, move R
to its current file and rank S.rank+1. The ray is clear if R.file≠S.file, or
if S.rank<R.rank (S then lies below both endpoints). If R is already there,
use the wall directly. The rook is distant before giving W its turn. A legal
horizontal reply exists by the existing barrier reply lemma; every legal reply
is noncapturing and remains above the wall. S029 wins every successor.
Transport gives the same entry in any axis/direction. In particular, horizontal
king gap at least two, R.rank≠S.rank, and rook/weak rank margin at least two
suffice for perpendicular entry.

## 4. Off-rank rook setup

Assume R.rank≠S.rank. R.rank cannot equal W.rank: S is below that rank and
cannot block the incoming rook check. If R is strictly between the kings, use
the wall. Otherwise R.rank<S.rank or R.rank>W.rank. With file margin≥2 use §3;
if the vertical ray is blocked by S, the file gap to W is at least two, so
perpendicular entry applies (rook/weak rank distance is at least two).

With file margin<2, slide R horizontally on its rank to the far file, whose
weak-file distance is at least four. Both kings are off that rank, the ray is
clear, and the move is distinct. A same-rank horizontal W step supplies a legal
reply witness. Rook safety projects every legal reply to a king step. The new
weak-file margin is at least three and kings remain separated.

If the vertical king gap stays at least two, direct entry applies unless S
blocks; in that case the horizontal gap is at least three and perpendicular
entry applies. If the vertical gap falls to one, king separation forces a
horizontal gap of at least two. R's old rank was outside the original king
interval, so its rank is at least two away from this new W. Perpendicular entry
again applies. This handles the axis switch rather than assuming the original
gap survives. There is one retreat/reply pair followed by direct entry at most.

## 5. Same-rank rook and strong king

If their rank is positive, move S down one rank. R is now an intermediate wall
and still distant from W. A reply exists: W steps down on its old file, which
is not R.file by no incoming check. Its rank remains above R and two above the
new S. Safety and the barrier cover every reply; S029 then wins.

On rank zero, if horizontal king gap is at least two, swap/reflect coordinates:
R and S have different files, so §4 applies in the new frame. If rook/weak file
margin is at least two, use §3. Otherwise both file gaps are at most one, and
R.file≠W.file by no incoming check.

When R is adjacent in file to S, push R to rank one. It is protected by S;
safety and the barrier cover every reply. Nonemptiness requires care: choose
W's old file, moving up when W.rank=2 and down otherwise. The resulting rank
is at least two, the file differs from R.file, and the move avoids both checks.
Hence this protected entry cannot accidentally stalemate.

In the remaining case R is two files from S beyond W's file. Move S horizontally
onto W's old file on rank zero, now adjacent in file to R. The rook remains
distant before the reply. Use the preceding up/down witness for nonemptiness.
Every legal reply has rank at least two: a downward step to rank one would be
adjacent to the newly aligned S. Mover safety re-establishes no incoming check
on the actual successor. Apply the protected entry just proved. This is one
preparation pair and one entry pair, not a recursive setup assumption.

## 6. Global setup, arrival and weak classification

No weak check gives king separation ≥2. Some coordinate differs by at least
two; identity/reflection/swap/anti-reflection orients it as a positive rank gap.
Create a canonical castling-free source; distinctness and no rook check map.
Sections 3–5 win there; §2 transports back to the original arbitrary flags.
Any kernel-legal incoming move leaves its mover (the weak side) out of check,
so supplies the premise without a global history/reachability assumption.

For the weak-turn classification, actual mate gives a zero-ply win. A legal KK
capture refutes forcing by dead-KK obstruction. If no legal replies exist,
forcing is equivalent to actual named-colour mate, excluding stalemate. If a
nonempty reply set has no captures, frozen `lone_move_cases` makes every reply
an exact strong-turn KRK legal arrival; the flagship wins each, and finite
branching proves weak-turn forcing. Safety gives the equivalent geometric
interface by frozen reply completeness; its necessity was §1.

## Termination and limits

Setup has no recursive cycle: the off-rank branch uses at most one retreat
pair plus one direct-entry pair; same-rank preparation has the same bounded
form. The subsequent S029 wall strategy uses its already proved nested finite
rank/gap/pursuit induction. Transport decreases a source finite forcing budget.
No numerical optimal distance is asserted. No seven-piece, clock, repetition,
DTZ, or initial-position theorem follows. Frozen ledger entries are unchanged;
Gate Z remains separate. The standard Lean/core/rules-encoding trust boundary
and need for independent human review remain.
