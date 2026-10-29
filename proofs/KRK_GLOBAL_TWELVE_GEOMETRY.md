# Complete twelve-ply board geometry

Certification update (2026-10-29): checked results are included in EC-T0049; see the [bundle scope and proof correspondence](KRK_BOUNDED_FRONTIER_CERTIFICATION.md). Any local-build counts or unfrozen/uncommitted statements below describe the pre-certification research checkpoint, not current publication status. Mathematical open obligations remain open.

`KRKTwelveGlobal.kernel_twelve_iff` proves, for either colour, any native KRK position with weak side to move and kings at distance at least two:

MateWithin(strong,12,q) iff Terminal(sk,rs,wk) or Region(sk,rs,wk).

Native position flags remain in the theorem. This is a bounded board theorem, not closure of full-history KRK or its distances.

The entire interior region is evaluated by `KRKTwelveInteriorExact`: canonical inward, near-strip and central-strip rook inequalities at depth one, and the reflected second-corner family at greater depth. The complete inward combination and its all-move lower bounds are described in [the inward proof](KRK_TWELVE_INWARD_FRONTIER.md).

On an edge, normalize the weak king to (j,0), 0 <= j <= 3. `KRKTwelveEdge.Region` requires a safe rook, a legal member of the five compass destinations, and an explicit eleven-ply test at every legal compass destination. Edge destinations use `KRKElevenEdge`, forty-eight fixed king-point intersections and rook-line intersections with the evaluated ten-ply compass region. Inward destinations use the evaluated six-point `KRKElevenInner` criterion or the four-point `KRKElevenNearStrip` criterion after transposition. The central inward destinations are excluded by the proved twelve-ply holding bound. No future winning predicate or position-value atlas occurs in the region definition.

`KRKTwelveGlobal.kernel_exact_twelve_iff` proves exact distance twelve precisely on Region minus the entire earlier ten-ply set, including terminal positions. The reverse lower bound uses the theorem that a weak-turn eleven-ply win already wins within ten. `region_live` proves nonterminal regions have legal moves.

The subsequent `KRKCastleTwelve` proof excludes actual native castling as a nonmating twelve-ply entry. The original-history criteria now cover strong h>=86 and weak h>=85; see [the history proof](KRK_THIRTEEN_FOURTEEN_PLY_HISTORY.md). That conclusion uses the separate castling argument and retained original trace/claim tests, rather than this board iff alone.

Verification: full local Lean build passed all 426 jobs; expanded public axiom audit passed with only propext, Classical.choice and Quot.sound. These results remain unfrozen and uncommitted; KRK is open.
