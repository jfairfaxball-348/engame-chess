# EC-C044 — Cost-parametric KRK setup and global 442/443-ply ceilings

S074,2026-10-20. Classical rook setup/finite-budget composition, no novelty claim.
Sources: frozen legal-action/setup geometry and same-budget transport in EC-T0037,
EC-T0017/19 weak-reply safety/classification, and S073 EC-C043 verified wall bound
73*(7−rookRank) (freeze pending). Standalone paper/separate same-agent audit BEFORE
Lean. No tablebase/engine/class enumeration or stored position certificate.

## Exact statement and direct dependency admission

For colour σ and natural B, let WallBudget(σ,B) mean: for EVERY raw exact KRK
Position q with strong turn, squares S,R,W and S.y<R.y<W.y, MateWithin σ B q.
Flags are arbitrary. This is an explicit hypothesis to a KRK-specific interface,
not a new axiom. Under that hypothesis prove:

- exact strong-turn KRK with no weak check has MateWithin σ (B+4);
- hence every exact legal strong-turn KRK arrival has the SAME B+4 budget;
- a weak-turn exact KRK with safe rook and nonempty legal replies has B+5.

Both colours and all raw flags are quantified. Defensive replies remain ALL
actual Legal replies; the winner chooses only its proved setup moves. Axis
transformations use canonical noRights source and arbitrary-flags target with
SAME-budget transport. Root legal arrival needs some actual legal incoming move,
not a stored per-position proof tree or global history premise.

EC-C043 gives the hypothesis at B=438 because strict rank wall implies R.y≥1,
so73*(7−R.y)≤73*6=438. Therefore every legal strong-turn arrival has a global
clock-free ceiling442. Every exact WEAK-turn KRK already known to ForceMate σ
has ceiling443: actual named mate uses0; otherwise rook safety/nonempty replies
supply the B+5 clause. The latter does NOT assert that every weak input wins.
These are nonoptimal upper bounds, not evaluated DTM/DTZ or full FIDE outcomes.

Four-part admission: (1) blocked direct KRK step is numerical arbitrary setup
composition after the improved wall result; (2) frozen setup returns hardcoded
504/506/508 or existential ForceMate and cannot accept a new wall budget;
(3) smallest needed statement is this material-specific WallBudget→B+4 interface,
with concrete438→442 and weak443 payoff; (4) exit immediately back to useful
quantitative/clock geometry and remaining FIDE/outcome obligations. No unrelated
generic lemma or automatic helper sequence. Frozen modules are never edited.

## 1. Budget composition and logical frame changes

Use frozen mateWithin_choose/defend/pair. A chosen legal strong move adds1,
a nonempty set of EVERY legal weak child at COMMON budget N adds1, and a full
chosen move/reply pair adds2. Smaller budgets pad by mateWithin_mono. These keep
the supplied fixed numerical budget; existential ForceMate is used, if needed,
only to establish nondeadness guards via a winning child, never as a numeral.

WallBudget also gives budget B for every proved involutive BoardSym-oriented
wall: map squares to canonical noRights exact KRK, apply the canonical wall
hypothesis, and transport its SAME B strategy back. Every target weak reply is
retained by frozen safe-reply completeness; source noRights is explicit and
persists. Extra target strong choices do not matter to a chosen strategy.
No raw-history or normalized-key transformation is asserted. Logical changes of
frame cost ZERO chess plies. Nested frame changes compose the proofs, without
assuming that an arbitrary composite map is itself an allowed involution.

## 2. Direct and perpendicular entry (B+2)

Normalize W.y≥S.y+2. If rook/weak file margin≥2 and the ray from R to
(R.file,S.y+1) cannot be blocked by S, use that target. The clear-ray condition
is R.file≠S.file OR S.y<R.y. If R is already on that rank, WallBudget applies
at B and pads to B+2. Otherwise this is an actual nonzero clear rook move; both
kings are safe and the rook is distant BEFORE giving the weak side its turn.
A horizontal weak neighbour witnesses nonemptiness. Frozen safe-rank reply
completeness covers every actual reply, each staying above the new wall. Apply
WallBudget at B to all strong-turn successors, compose one pair: B+2.

Same-budget transport gives this entry in every proved frame. In particular,
horizontal king gap≥2, R.y≠S.y, and rook/weak rank margin≥2 give perpendicular
entry at B+2. Use swap or anti-diagonal frame according to the file ordering;
no new unchecked symmetry premise or extra physical move.

## 3. Off-rank setup (B+4)

Assume R.y≠S.y and no incoming weak rook check. R.y also differs from W.y:
otherwise S is off the rook/weak rank and cannot block the rook's check. If R
is strictly between the king ranks, it is already a wall at B. Otherwise R is
outside the interval. With file margin≥2, direct entry applies unless S blocks;
then horizontal king separation≥2 and rook/weak rank margin≥2 give perpendicular
entry. Both cost at most B+2, padding to B+4.

With smaller file margin first slide R horizontally to the far file on its
current rank. Both kings are off the rank, so the nonzero ray is clear. A
same-rank horizontal weak move witnesses nonemptiness. Every legal reply is a
noncapturing unit king step and leaves file margin≥3. If vertical king separation
remains≥2, use direct entry or the perpendicular blocked-ray case. If it falls
to1, post-reply king safety forces horizontal separation≥2; because the old rook
rank lay OUTSIDE the original king interval, the new rook/weak rank margin is
still≥2. Perpendicular entry applies. Thus all replies have B+2, and the actual
far-rook/reply pair gives B+4. No recursive setup assumption or favourable weak
reply is used.

## 4. Same-rank and back-rank setup

A safe WEAK-turn strict wall with nonempty replies has B+1: every safe rank reply
returns a strong-turn strict wall at B. This common budget is independent of
files and all raw flags.

If R.y=S.y>0, retreat S down one rank. The rook becomes an intermediate wall,
remaining distant before W moves. No incoming rook check ensures W's file differs
from R's; W down on its old file supplies a legal reply witness. Every legal
reply stays above the rook. Apply the weak-wall B+1 and add the chosen king move:
B+2. Frozen same-rank no-file and rank-zero reply geometry are reused, not assumed.

At common rank0: with distant rook file margin use direct entry (B+2). If the
kings have horizontal separation≥2, change frame and use off-rank setup (B+4).
Otherwise both rook/weak and king/weak file gaps≤1. No incoming check excludes
the rook sharing W's file. If R and S are file-adjacent, move R to rank1. It is
king-protected. The explicit up/down weak witness (up when W is on rank2,
down otherwise) avoids stalemate, and every legal reply gives a strict wall:
B+2. In the remaining geometry R lies two files from S beyond W's file. First
move S horizontally to W's old file at rank0, still safely below W. Every reply
stays at rank≥2 by king separation and restores no incoming check through actual
mover safety. The protected entry then costs B+2. Preparation/reply adds2,
giving B+4. Both movements are actual legal actions, no assumed waiting pass.

## 5. Arbitrary strong geometry, arrival and uniform438

No weak check implies king separation≥2. One coordinate differs by at least2;
use the proved identity/y-reflection/swap/anti-diagonal frame to orient it as
W.y≥S.y+2. Create the canonical noRights source, apply §§2–4 at B+4 and transfer
back at the SAME budget to original flags. This proves the geometric theorem.
Any legal strong-turn incoming arrival leaves its mover, the weak side, out of
check, providing that premise. No complete history simulation is needed.

At the new wall bound, any canonical strict wall has1≤R.y≤6. Pad
73*(7−R.y) to438 uniformly to construct the actual WallBudget(σ,438) hypothesis.
Apply the interface:438+4=442. The number is derived from the new wall and actual
setup costs, not relabelled from508 or extracted from an existential witness.
The uniform438 bound itself is conservative; smaller coordinate values remain
available separately. Both colours/arbitrary flags and every defensive reply.

## 6. Quantitative weak-turn corollary

With a safe rook and nonempty legal replies on a weak-turn exact KRK board,
frozen safe-reply completeness sends EVERY actual legal reply to exact strong-turn
KRK. It is a legal arrival, so §5 supplies B+4 at each child; the defending
constructor gives B+5. Terminal children are not filtered.

For a weak-turn input with ForceMate σ q: if actual named mate, pad its0 to443.
Otherwise absence of all legal replies would force the named goal by frozen
forceMate_no_moves_iff, a contradiction. Frozen necessary weak forcing safety
supplies SafeRook; the preceding B+5 theorem at438 gives443. This excludes no
Legal move by fiat: any optional rook capture to dead KK would contradict the
forcing premise. Losing/stalemated/unsafe weak positions are NOT asserted wins.
No draw/holding theorem is inferred from failure of these hypotheses.

## Scope and status

The global clock-free numerical ceilings improve508 to442 for legal strong-turn
arrivals and give443 for weak-turn winning inputs. They exceed100 and therefore
do NOT instantiate general strict fifty-move RAW certificates. EC-C043's local
73-ply/clock≤26 family is unchanged, conditional on actual incoming counts.
Full FIDE correspondence, every-history outcomes/holding and exact WDL/DTZ remain.

LOCAL_VERIFIED after separate same-agent audit; formal/freeze gates pending.
39 frozen bundles unchanged. New parametric modules must preserve all supplied
budgets and exact geometry. No class completion percentages or novelty claim.
