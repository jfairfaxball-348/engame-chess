# Complete eight-ply interior geometry

Certification update (2026-10-29): checked results are included in EC-T0049; see the [bundle scope and proof correspondence](KRK_BOUNDED_FRONTIER_CERTIFICATION.md). Any local-build counts or unfrozen/uncommitted statements below describe the pre-certification research checkpoint, not current publication status. Mathematical open obligations remain open.

`KRKEightInteriorExact.kernel_eight_iff` covers every board-kernel KRK
position with the weak side to move, distinct pieces, king separation
at least two, and a weak king strictly inside the board. Native flags
are retained. `stripFrame` changes coordinates only, without rewriting
the position, rights or history.

Forcing within eight plies requires edge depth one. The chosen frame
maps any such weak square to (1,j), 1<=j<=3. At j=1 the criterion is
the five families and transposes in [the inward-corner proof](KRK_EIGHT_INWARD_CORNER.md).
At j=2 it is K=(3,1), R=(x,3), x>=3, as in
[the near-strip proof](KRK_EIGHT_NEAR_STRIP.md). At j=3 forcing within
eight plies is impossible. The already checked central-strip exclusions
include the reflected fourth rank; the frame maps it to j=3.

The proof combines the necessary deep-interior exclusion, a symbolic
proof of the frame's coordinate bounds, the two iff geometry theorems,
and inverse coordinate transport. These alternatives exhaust all
interior weak squares; no sampled or enumerated values enter the proof.

`kernel_exact_eight` additionally characterises exact distance eight:
the eight-ply region must hold and the complete inward-corner six-ply
region must fail. Weak-turn seven-ply forcing equals six-ply forcing,
so this is a matching optimal-distance exclusion, not merely an upper
bound. This result is clock-free. Actual history barriers and full KRK
rule-aware distance closure remain open. All results remain unfrozen.
