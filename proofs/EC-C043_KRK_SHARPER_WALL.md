# EC-C043 — Sharper pursuit, 73-per-rank walls and RAW clock coverage

S073,2026-10-20. Classical KRK geometry/finite-phase accounting; no novelty claim.
Sources: frozen EC-T0037 KRKBound/Pursuit/LowerBand/Wall and same-budget transport,
EC-T0014/15 action geometry, EC-T0039 actual-history lifting. Standalone paper and
separate same-agent audit precede Lean. No engine/tablebase/exhaustive class proof
or per-position certificate. Frozen modules/records remain immutable.

## Exact claim and domain

For either strong colour σ, arbitrary flags and exact strong-turn KRK wall
S.y<R.y<W.y, prove MateWithin σ (73*(7−R.y)) q. The coordinate bound transports
at the SAME budget through any proved involutive BoardSym frame g, using the
canonical noRights source and arbitrary target flags:

    (gS).y<(gR).y<(gW).y ⇒ MateWithin σ (73*(7−(gR).y)) q.

Identity/reflection/swap/anti-diagonal frames cover walls toward each board edge.
No unrestricted raw-kernel/history symmetry is assumed.

For an actual admitted initial-rooted RAW state s matching such a strong-turn
wall in frame g, with (gR).y=6, clock(s.trace)+73<100 (clock≤26), current count<3
and the UNCHANGED LowerRankHistory σ s.val condition, conclude RAW
RuleMateWithin layer σ 73 s. Counts and ranks are queried in the ORIGINAL state,
not a transformed history. All legal weak executed/intended moves retained,
both colours/all flags. This is a PARTIAL conditional RAW family, not complete
FIDE outcomes/holding/distances; no compatible-history witness is asserted.

Relative to the earlier canonical rank-six family this changes the conservative
clock ceiling from15 to26 and exposes every proved frame. The prior global508
arrival ceiling is unchanged in this session. No global442 or sub100 maximum is
claimed without formal setup composition. No bound here is optimal distance/DTZ.

## 1. File-edge pursuit saving

Retain the frozen lower-band domain S.y+1=R.y, W.y=R.y+1 and rook/weak file
margin≥2. Every aligned-file or upper-band exit has a UNIFORM supplied budget E.
For direction d use oriented file x (physical file or7−file), with x(S)<x(W),
and let m=7−x(S). Then1≤m≤7. Define f(m)=8*m−6 using natural subtraction;
only positive m occurs in this theorem.

The SAME chosen moves/action facts as the frozen pursuit prove budget f(m)+E.
This is an all-reply cost refinement, not a new unproved legal strategy.

At m=1, x(S)=6 and x(W)=7, necessarily offset one. A distinct far/second-far
rook tempo and ANY weak reply costs two. An upward reply is already an exit.
A same-band reply changes file by exactly one; the file edge excludes moving
farther away, so it aligns with S. Thus all replies exit within2=f(1) plies.
This is a FILE-edge argument; W may still rise in rank, which remains an exit.
It is not assumed already checkmate.

For general m, reproduce the frozen nested local branches:

- Good: offset≥2 and margin≥3. One king-file advance/reply pair costs2. It exits
  or recurses at m−1 with margin≥2, for cost≤f(m−1)+2+E.
- Wide: offset≥2 and margin≥2. At margin2 one far-file normalization may need
  the distinct far/second-far waiting pair when the reply reduces offset to1.
  The second nonexit reply returns the weak file to its original value with
  margin≥3. A good king step follows. Cost≤f(m−1)+6+E.
- Initial offset1: one tempo either exits or reaches offset≥2, then uses Wide.
  For m≥2 total≤f(m−1)+8+E=f(m)+E. At m=1 a continued Wide input is IMPOSSIBLE
  by the on-board file bounds, as in the base argument above.

Good and Wide require m≥2. Therefore no f(0) witness or negative subtraction is
used as a recursive strategy bound. Earlier exits cost no more than the stated
positive parent budget. More precisely the offset-one first pair can leave a
residual budget8*m−8+E, nonnegative for m≥1: at m1 this is exactly E; at m≥2 it
equals f(m−1)+6+E. This avoids the invalid unconditional f(0)+8 padding.
The only recursive call is still an actual king-file advance. All nonempty
reply/action hypotheses remain the frozen kernel theorems, both directions.

Since m≤7, f(m)≤50. Aligned initial files use E directly. Thus the entire lower
band with uniform exit budget E wins within50+E, improving56+E. The saving is
six PLIES and does not erase any rook tempo or check/reply pair.

## 2. Rank-edge credit and the wall coefficient

For a strict strong-turn wall put n=7−R.y and g=R.y−S.y. Then1≤n≤6 and1≤g≤6.
Let c(n)=3 if n=1, else0. Define U(n)=73*n and the refined full-wall budget

    A(n,g)=73*(n−1)+56+4*(g−1)−c(n).

Its ready-state budget (file margin≥2) is smaller by two. Subtractions are safe:
all displayed offsets exceed c≤3. Induct on n and at fixed n on g, proving Ready
before full normalization, exactly as in the frozen wall proof.

An upper-band state W.y≥R.y+2 has n≥2. Frozen rank advance/rescue costs at most
four plies and reaches a strict wall at the higher rook rank, with arbitrary
king gap and a possibly threatened strong-turn rook already repaired as required.
The outer induction gives U(n−1). Since c(n)=0 here, budget4+U(n−1) suffices.

At lower band and g≥2, one upward strong-king step and every reply costs2, giving
full-wall gap g−1 at the SAME n. Possible threatened rook is allowed by the full
induction. Initial far-rook normalization, when needed, adds2 at EVERY gap, so
4+A(n,g−1)=A(n,g). No same-measure normalization recursion or free waiting pass.

At lower band and g=1, the exit budget is

    E(n)=4+U(n−1)−c(n).

For n≥2, upper exits use the four-ply advance/rescue and aligned exits use the
two-ply check/reply plus U(n−1), or one-ply mate. For n=1, the rook is on rank6
and weak king on rank7. An upper exit is impossible; an aligned-file check is
ACTUAL named mate in ONE ply. A nonmating aligned reply would require rank8,
contradicting on-board bounds. Thus E(1)=1, rather than the old conservative4;
this is the extra three-ply rank-edge credit. It is separate from §1's file edge.
No nonexistent rank-seven strict wall is assumed winning.

Section1 gives ready lower cost50+E(n). Normalization adds2, hence full lower
cost52+E(n)=U(n−1)+56−c(n)=A(n,1). For g>1, the inner induction supplies its
4*(g−1) allowance. Upper ready branches fit the same bound with slack.

Finally A(n,g)≤U(n): at n1, c=3 and g≤6 give overhead56+20−3=73; at n≥2,
R.y≤5 and therefore g≤5, c=0 and overhead≤56+16=72≤73. This is why the exact
coefficient73 is justified. Simply replacing84 with73 without the rank-edge
case would fail at n1/g6 (uncorrected overhead76). The initially suggested76
coefficient follows without the credit, but this audited proof earns the extra3.

## 3. Axis transport and actual-history payoff

For a proved BoardSym g, create the canonical noRights exact KRK source at mapped
squares and apply §2. The frozen same-budget transport theorem maps its strategy
back to the original arbitrary flags. It retains EVERY target legal weak reply
and a nonempty witness and costs zero chess plies. It does not transform any
history or assume normalized-key symmetry.

At transformed rook rank6 the bound is73*(7−6)=73. Apply the frozen EC-T0039
raw_ruleMateWithin_of_strategy_history at N=73, with the ORIGINAL admitted state,
clock+73<100, original current count and original lower-winning-rank histogram.
That theorem chooses the least-rank strong moves and handles ALL weak executed/
intended actual appends. The numerical wall policy supplies an upper budget;
it need not itself be the rank policy. This is exactly the already proved
lifting interface, not an additional all-raw-path repetition premise.

The strict clock condition permits every integer clock≤26 under the displayed
other hypotheses. This is a conditional RAW coverage improvement only. Failure
of the certificate is not draw; no compatible-history witness/nonemptiness,
FIDE correspondence, complete KRK outcomes/holding or exact distance is claimed.

## Status and next direct obligation

LOCAL_VERIFIED after separate same-agent audit, Lean/Gate F and separate Gate Z
pending. 39 frozen bundles unchanged. No generic prerequisite diversion: this
is direct strategy-cost/clock-family progress. Existing frozen modules, earlier
proofs/manifests and the global508 arrival theorem are not edited or upgraded.
To improve the global bound, actual setup/axis composition must expose the new
wall budget in NEW statements, rather than reusing hardcoded504/506/508 results
as if parametric. Wider geometry/clocks and full FIDE/outcome/distance work remain.
