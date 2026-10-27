# KRK: compact middle five-ply geometry and six-ply destination reductions

Locally Lean-verified, unfrozen. These are clock-free geometric results
supporting the OPEN strong h=92/93 history-aware classification.

## Compact strong five-ply middle formula

Let the weak king be W=(x,0), 2<=x<=3. Assume exact KRK material, strong turn,
kings at least two apart, and the weak king not already under rook attack
(the usual legal-arrival geometry). Write K and R for the strong king/rook.
Let L=(x-1,2), C=(x,2), E=(x+1,2).

`KRKFiveMiddle.kernel_five_iff` evaluates mate within five plies exactly by
the union of these three king-entry tests:

- R.y>=3 and dInf(K,C)=1;
- R.x=x+1, R.y>=2 and dInf(K,L)=1;
- R.x=x-1, R.y>=2 and dInf(K,E)=1;

and these three rook-entry tests:

- K=C;
- K=L and [R.x=x+1 or R.y>=3 or (R.y=2 and R.x>=x)];
- K=E and [R.x=x-1 or R.y>=3 or (R.y=2 and R.x<=x)].

No moved-square search remains. Immediate mate is already contained in K=C.
The reflected formula evaluates x=4,5. `KRKFiveGeometry.map_iff` establishes
pure geometric reflection using synthetic castling-free proof boards; actual
flags/history are not mapped. Both strong colours and actual kernel castling
alternatives are retained by the exact five-ply theorem on which this rests.

The king tests follow from the three middle four-ply destination slots.
Their safe-rook/live-reply/distinct-piece conditions are proved automatic
within these middle slots. For the central rook entry, choose rank three or
four, avoiding the old rook square. On the king's file, a rook below its king
would already check W, violating the arrival assumption; hence this lift is
unblocked. For each side point, vertical entry is possible exactly on the
opposite file; horizontal entry works at rank>=3, or at rank two when the
king does not lie between source and destination. These yield the inequalities
above. `west_reachable_iff` and `east_reachable_iff` prove necessity as well as
constructive sufficiency.

Two additional exact reductions remove irrelevant arithmetic cases: a rook
on rank zero/one permits only three king/file configurations, and when king
and rook are both on rank two the formula reduces to five king-file cases.
These are `low_rook_bottom_iff` and `rank_two_bottom_iff`.

## Central weak six-ply region equals its four-ply region

For W=(x,0), x=3 or 4, exact KRK material, weak turn and separated kings,
`KRKSixMiddle.kernel_six_four_iff` proves

    MateWithin(strong,6,q) iff MateWithin(strong,4,q).

Every interior neighbour must be covered by king or rook line, since a
strong five-ply child requires an edge weak king. Coverage of the three
inward neighbours forces K.y=2 or R.y=1. The explicit left/right five-ply
formulas and safe-rook condition exclude R.y=1. With K.y=2, rook rank zero
is terminal mate, rank two forces one of the last-reply placements, and
higher ranks allow only those placements or direct opposition. Explicitly,
the nonterminal regions are:

- K=(x-1,2), R.x=x+1, R.y>=2;
- K=(x+1,2), R.x=x-1, R.y>=2;
- K=(x,2), R.y>=3.

These are precisely the existing four-ply regions. Both directions, including
terminal mate, are checked. The necessity proof separates rook ranks before
performing arithmetic; it does not enumerate a class of positions.

**Boundary:** This is a clock-free equivalence. It does not compress a RAW
history-aware six-ply certificate to four: original repetition barriers may
obstruct a shorter strategy. It supplies the finite geometric entry catalogue
for later exact history tests, not a full next-clock-band outcome.

## Interior weak six-ply destinations

`KRKSixInterior.weak_six_interior_corner` proves that an interior weak king
supporting a six-ply kernel win must be at one of

    (1,1), (1,6), (6,1), (6,6).

For the noncorner first interior strip W=(1,y), 2<=y<=5, inward-neighbour
coverage forces K=(3,y) and R.x=1. Safe rook forces rook rank at least two
away from y. Thus the outward reply (0,y) is actual legal geometry. After
swapping coordinate axes, its strong five-ply formula has K.y=3 and R.y=1;
the exact low-rook criterion requires K.y=2, a contradiction. Reflections and
axis swap exclude the other strips. The already checked deep-neighbour
coverage obstruction excludes interior depth at least two.

This is necessary only; it does not declare the four remaining inward-corner
squares winning or drawn. Their geometry, the second edge file, near-corner
and corner edge destinations still need evaluation for the next band.

## Verification

Full `lake build`: PASS, 313 jobs. `lake env lean AxiomCheck.lean`: PASS, all
new public declarations audited. Dependencies are subsets of propext,
Classical.choice and Quot.sound. No sorry/admit/new axiom/unsafe escape,
tablebase, engine or stored position values. Historical frozen modules,
manifests and ledger are unchanged. Full KRK all-history outcomes, FIDE
correspondence and global exact distances remain OPEN.
