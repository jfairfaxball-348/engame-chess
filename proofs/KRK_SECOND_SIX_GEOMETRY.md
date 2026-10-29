# Second-edge six-ply geometry

Certification update (2026-10-29): checked results are included in EC-T0049; see the [bundle scope and proof correspondence](KRK_BOUNDED_FRONTIER_CERTIFICATION.md). Any local-build counts or unfrozen/uncommitted statements below describe the pre-certification research checkpoint, not current publication status. Mathematical open obligations remain open.

Locally checked, unfrozen. KRK remains open.

Let the weak king be W=(2,0), the strong king K=(a,b), and the rook
R=(x,y). Assume exact KRK material, weak turn, and Chebyshev distance
d(K,W)>=2. Actual kernel flags are retained. Then mate can be forced
within six plies exactly when W is already mated, or the rook is safe,
the weak king has a legal reply, and one of these coordinate regions holds:

| Strong king | Rook condition |
|---|---|
| (1,2) | x=3 and y>=2 |
| (2,2) | y>=3, or y=2 and x>=3, or y=1 and x in {3,4} |
| (3,2) | x=1 and y>=2, or y=1 and x>=4 |

The formula includes every legal strong alternative through the existing exact
five-ply criterion. It is not a sufficient-policy test. The exact newly added
distance-six region is:

* K=(2,2), with y=2 and x>=3, or y=1 and x in {3,4}; or
* K=(3,2), with y=1 and x>=4.

For these new families safety and a legal reply follow from the coordinates;
(1,0) is always a legal weak reply. Mate cannot be forced within five plies.
The remaining rows already force within four. These are clock-free distances,
not full-history RAW or FIDE distances.

## Proof

Every legal weak reply must lie in the exact strong five-ply region. That
region excludes the interior. Therefore each of (1,1), (2,1), (3,1) must be
covered by the strong king or a rook line. Their joint constraints, rook
safety and king separation force b=2 or y=1. In the latter case the exact
five-ply tests at (1,0) and (3,0), together with rook safety, also force b=2.
Safety is essential: an adjacent unguarded rook permits capture.

When y=0 these constraints and safety force terminal mate. Otherwise split
y=1, y=2, y>=3. Evaluate the left reply with `KRKFiveNear.Five` and the right
reply with `KRKFiveMiddle.Five`. The resulting inequalities give the table.
The necessity proof uses a rook line as a relaxed coverage test only where
that is sound; the sufficiency proof uses exact visibility including blockers.

Conversely every table family excludes all three inward replies. Each legal
remaining reply is (1,0) or (3,0), and satisfies the corresponding exact
five-ply criterion. A separate legal-reply requirement prevents vacuity at
stalemate. Already-mated roots are handled first.

For exact distance six, subtract the previously proved second-edge four-ply
criterion. Weak-turn five-ply forcing is equivalent to four-ply forcing by
parity. The difference is exactly the two new families above.

Lean source: `formal/EndgameChess/Rules/KRKSixSecond.lean`;
main declarations `kernel_six_iff` and `kernel_exact_six_iff`.
Both declarations pass the local Lean 4.35.0 checker. The integrated
`lake build` passed (318 jobs); `lake env lean AxiomCheck.lean` passed.
Every new public main declaration reports only `propext`, `Classical.choice`,
and `Quot.sound`. No hosted CI result is claimed.

This does not eliminate native incoming-history barriers, finish near-corner
six-ply geometry, establish the next complete clock band, or settle global
KRK outcome, FIDE correspondence or WDL/DTZ obligations. No frozen source or
manifest was changed.
