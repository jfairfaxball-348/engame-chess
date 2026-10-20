# EC-C040 — Explicit KRK strategy bound (S067)

2026-10-20. Status: LOCAL_VERIFIED on paper after the separate same-agent audit;
not Lean verified or frozen. Classical rook technique, no novelty claim. Sources:
the unchanged S029 wall/pursuit paper and S030 safe-setup paper, and their frozen
Lean modules (EC-T0013–0019). No tablebase, engine, exhaustive class enumeration
or stored position certificates are used.

## Statement and conventions

For either colour σ, any kernel Position q and squares S,R,W, assume exact
IsKRK q σ S R W, q.turn=σ, and inCheck q σ.opp=false. Then
MateWithin σ 508 q. In particular the conclusion holds when q has a legal incoming
move, since that move leaves its mover, the weak side, out of check. Flags are
arbitrary; no initial-rooted history premise is imposed. This is clock-free,
nonoptimal, measured in individual board plies. Actual named mate has budget zero;
a mating move costs one; all defending replies remain in the proof. No numerical
exact distance, history certificate, rule-aware outcome or FIDE WDL/DTZ follows.

More informative intermediate bounds use coordinates 0..7 in the chosen frame.
For a strong-turn wall S.y<R.y<W.y put n=7−R.y and g=R.y−S.y. Then
1≤n≤6, 1≤g≤6, and define

    A(n,g)=84*(n−1)+62+4*(g−1),   U(n)=84*n.

Every such wall has MateWithin at A(n,g), hence U(n), since A(n,g)≤U(n)
(the largest overhead is 62+4*5=82≤84). A setup branch costing e≤4 plies
and ending at a wall of rank r≥1 therefore has branch budget e+84*(7−r)≤508.
For a choice with varying defending successors take the maximum of these
coordinate budgets, padding smaller budgets by monotonicity. Thus the global
constant is a ceiling derived from the coordinate/phase bounds, not an
existential witness renamed as a number.

## 1. Budget composition and transport

Use the frozen MateWithin recurrence. At a strong node with chosen legal child
winning within N, the parent wins within N+1. At a weak node with a NONEMPTY
reply set and EVERY legal child winning within the SAME N, the parent wins within
N+1. The nondeadness guard follows from a legal route to a mate: any one winning
child supplies such a route by mateWithin_sound, and prepend the legal move.
For weak nodes choose the stated reply witness. Early mate is padded by
mateWithin_mono. A full strong-move/reply pair costs two; no branching sum is
needed. The old existential forceMate_defend implementation used finite bounds
that need not be sharp; it must not be used to infer a numerical budget.

The S030 transport proof strengthens to preservation of a GIVEN MateWithin N,
from a noRights exact KRK source to its BoardSym image with arbitrary target
flags. Induct on N. Source mate maps to target named mate by its check formula
and safe-reply completeness. At a strong node, noRights ordinary-move
completeness projects the chosen move, map StepM and lift the target legal move;
apply induction at N−1. Extra target strong choices do not matter. At a weak
node, source winning implies SafeRook, which maps by distance. Map one source
reply forward for nonemptiness. For EACH target legal reply use safe-reply
completeness, map back by involution, lift the source legal reply, and apply
induction at N−1. Target nondeadness follows from a mapped winning child as above.
noRights persists in source successors. The involution on geometry recovers the
source KRK state; equality of raw flags or full positions is never assumed.
The maps are the proved identity, y reflection, swap and anti-diagonal maps.
This is a new same-budget statement; the frozen existential transport theorem
alone does not discharge it. Axis changes cost ZERO plies.

## 2. Pursuit with a uniform exit budget E

Fix lower-band ranks S.y=y−1, R.y=y, W.y=y+1, rook/weak file margin≥2.
Assume EVERY upper-band or aligned-file exit satisfying the frozen exit
interface wins within a uniform budget E. In orientation d let x be the oriented
file (physical file or 7−file) and m=7−x(S). If x(S)<x(W), then 1≤m≤7.
The S029 policy reaches an exit with total budget at most 8*m+E.

Prove by induction on m. A good state has offset x(W)−x(S)≥2 and file margin≥3.
Its king-file advance followed by ANY weak reply costs two. A reply either exits,
or leaves a same-band state in the same orientation with m decreased by exactly
one and margin≥2. The induction bound is 2+8*(m−1)+E≤8*m+E.

For offset≥2 and margin exactly two, first use a far-file rook move. A non-exit
reply either leaves a good state, or leaves offset one. In the latter case old
offset was exactly two; use the distinct far/second-far rook tempo. Any remaining
non-exit reply returns the weak file to its original value and has margin≥3,
by pursuit_tempo_return_margin. A king advance follows. This costs at most
three pairs (six plies) before exit or the recursive call at m−1.

For initial offset one, one distinct far/second-far rook tempo either exits or
leaves offset two, with margin≥2. Then use the preceding wide case. Hence at
most four pairs (eight plies) precede exit or recursion at m−1. Every earlier
exit costs at most eight as well. m=0 has no strict-orientation inputs. At m=1,
a surviving recursive input at m=0 is impossible, so the same argument terminates.
If files initially agree, it is already an exit with budget E. Otherwise choose
the appropriate physical direction. All lower-band inputs therefore win within
56+E. This count includes the initially narrow offset, BOTH normalization tempos,
and the king move; it does not assume a free waiting pass.

All nonempty and all-reply action facts are exactly the frozen WallActions and
PursuitGeometry statements. A same-band weak move changes file by one; upward
replies are exits; the barrier excludes downward replies. No favourable reply
is selected by the strong player.

## 3. Wall induction and constants

Induct on n, and at fixed n induct on g. The assertions concern ALL wall states,
including a threatened rook on a strong turn. Prove the ready case (file margin≥2)
first; if not ready, a far-file rook move and all replies cost two and give a
ready state at the same n,g. This normalization is bounded, not a recursive
same-measure invocation. Every ready/full bound below is uniform over files.

Upper band W.y≥R.y+2: use frozen rank_advance_rescue. Raising costs one pair;
if necessary the strong player immediately rescues the hanging rook with one
more pair. All successors have rank R.y+1 and hence bound U(n−1), irrespective
of their king gap. Total ready cost ≤4+U(n−1). If this branch exists then n≥2:
W.y≤7 and R.y+2≤W.y. Thus no U(0) wall is being assumed.

Lower band W.y=R.y+1 and g≥2: advance the strong king one rank. Every reply
preserves the same wall, now with gap g−1. The rook was safe before the reply;
it may be threatened at the new strong turn, which the FULL gap induction
allows. Ready cost ≤2+A(n,g−1). Including possible initial normalization gives
4+A(n,g−1)=A(n,g).

Lower band and g=1: discharge the pursuit exit assumption. An upper exit costs
at most 4+U(n−1), by the upper-band action. An aligned exit uses the two-file
check. At the upper edge it is mate in one ply; otherwise the check and every
reply cost two and produce a strict wall at rank R.y+1, hence cost ≤2+U(n−1).
For n=1, R.y=6 and W.y=7: upper exits cannot occur, and every aligned exit is
an actual one-ply mate. In all cases E=4+U(n−1) is a valid common upper bound;
no unavailable higher-rank wall is invoked at n=1. Section 2 gives ready cost
≤56+4+U(n−1)=60+U(n−1). Initial normalization gives 62+U(n−1)=A(n,1).

For g>1 the upper ready branch with normalization costs ≤6+U(n−1)≤A(n,g).
The lower ready catch branch is handled by the gap induction above. These are
all cases. Since g≤R.y≤6, A(n,g)≤U(n). The wall result has now closed at an
explicit budget, rather than by existential finite-branching assembly.

## 4. Setup count covering every arrival

Use the exact choices and reply-completeness proofs of S030. No incoming weak
check gives separated kings and no rook ray to W. Choose a proved coordinate
frame with W.y≥S.y+2; create the canonical noRights source and later transport
its strategy back with §1. All subsequent coordinate changes are free.

If R.y differs from S.y, it also differs from W.y (otherwise W would be in rook
check). If it is between them, it is already a wall (zero setup plies). Otherwise
with rook/weak file margin≥2 use clear vertical entry or, if the strong king
blocks that ray, perpendicular entry. A nontrivial entry costs at most one pair.
With smaller margin first slide the rook horizontally to the far file (one pair).
Every reply has margin≥3 and is safe. Either the vertical king gap persists and
clear or perpendicular entry applies, or it falls to one, forcing horizontal
king separation≥2; the rook rank outside the old interval gives the perpendicular
margin. Then entry costs at most one more pair. Total off-rank cost ≤4.

If R.y=S.y>0, retreat the king down one rank (one pair). All replies preserve a
strict wall; the explicit reply witness steps W down on its old file, which differs
from the rook file. Setup ≤2. On rank zero: if the rook/weak file margin≥2 use
entry directly (≤2); if the kings' horizontal separation≥2 change frame and use
the off-rank proof (≤4). Otherwise both file gaps≤1. If rook and strong king
are file-adjacent use protected rook entry to rank one (≤2). In the remaining
case move the strong king onto W's old file at rank zero (one pair); every reply
keeps W at rank≥2 and restores no incoming check. Protected entry then costs
one pair. Total ≤4. Protected entry and preparation have explicit rank-zero
up/down reply witnesses; stalemate is not silently discarded.

Every resulting wall in its active frame has 1≤r≤6, so U(7−r)≤504. Each branch
costs at most four plies. Pad branch bounds to 508 and compose, or use the maximum
of the e+84*(7−r) branch bounds. The same-budget transport preserves 508 through
all nested canonical-frame constructions. Both strong colours and arbitrary flags
are included; the strategy chooses ordinary moves and does not require castling.

## 5. History and remaining obligations

The coarse ceiling 508 exceeds 100 and does NOT establish any general fifty-move
winning certificate. The strategy has a lexicographic macro progress order:
wall rank increases; at fixed wall rank king rank increases; in lower-band pursuit
the oriented strong file increases, with bounded normalization subphases. Setup
has at most two pairs. This prevents infinite policy play. It does NOT by itself
prove that normalized repetition keys never repeat: orientations may change,
subphase labels are not in the key, and different phases can revisit geometry.
Milestone B must bound occurrences for this chosen policy on ALL weak branches,
including prospective intended moves, and separately incorporate incoming keys.
The frozen four-ply chase cycle is a control against silently dropping tempo
branches. EC-C039's all-raw-prefix certificate is not assumed here.

S067 performs paper proof/audit only. The exact formal obligation is now to
implement same-budget composition/transport, uniform-exit 8*m+E pursuit, the
A/U wall induction and the ≤4 setup composition in NEW modules. Frozen modules
and theorem ledger remain unchanged. Until observed Gate F and separate Gate Z,
508 is a paper-verified bound only; KRK rule-aware coverage remains unchanged.
