# EC-C051 — Guarded large-box contraction (S087)

2026-10-21. This is a geometric phase toward EC-C050, not a complete KRK
strategy or a sub100 bound. Classical confinement geometry; no novelty claim.
All coordinates are integers from0 through7. Costs count board plies, and every
legal weak reply is quantified. No engine, tablebase, position-value search,
class enumeration or stored per-position proof is used.

## Exact normalized phase

Let the strong king S=(a-1,b-1), rook R=(a,b), and weak king W=(x,y),
where1<=a<=2,1<=b<=6,a<x<=7,b<y<=7. The strong side is to move in an exact
kernel KRK position, either colour and arbitrary flags. Thus R is protected,
neither rook ray into the northeast quadrant is blocked, and W lies in a box
of width w=7-a>=5 and height h=7-b>=1. This domain is a partial family;
arbitrary KRK-to-guarded-box entry is a separate, unproved obligation.

There is an actual legal strong policy, retaining EVERY legal weak reply,
which within at most four strong/weak pairs (eight plies) reaches one of:

* NE: R'=(a+1,b), S'=(a,b-1), W'.x>a+1,W'.y>b.
  Its box has width w'=6-a=w-1 and height h'=h.
* NW: R'=(a+1,b), S'=(a+2,b-1), W'.x<a+1,W'.y>b.
  Its box has width w'=a+1<=3 and height h'=h.

All intervening weak positions have an actual legal reply, the rook is protected,
and every weak reply preserves all three pieces. Therefore this phase introduces
neither stalemate nor a rook-capture branch. Its endpoint is a strong-turn
guarded box with the king diagonally outside its weak quadrant.

The corresponding signed-coordinate/axis variants follow on the geometric
move model by reflections and swapping coordinates, followed by kernel
step_sound and safe-reply completeness. A kernel-history symmetry is NOT claimed.
The first Lean implementation must prove its actual declared scope; it must not
pretend normalized phase transport has already been implemented.

## 1. Elementary reply facts, with witnesses

If a rook is on (c,b), the strong king is on (s,b-1) with |s-c|<=1, and the
weak king is strictly above b, a weak reply cannot capture the rook: its target
would be adjacent to the strong king. A noncapturing reply cannot land on rank
b, since the rook's horizontal ray is unblocked by the strong king below it.
Since a king moves by at most one, it also cannot cross rank b without landing
on it. Consequently every weak reply remains strictly above b.

Likewise, as long as its file is initially strictly to one side of c, a reply
cannot cross the rook's file: above rank b that file is attacked by the rook,
and the strong king is below b and does not block that upward ray. A king
cannot jump over it. These facts concern ALL actual legal weak moves; arbitrary
castling flags give the weak side no rook with which to castle.

For nonemptiness, whenever the permitted file interval has at least two files,
keep W's rank and take a horizontal neighbouring file within that interval.
At an interval's left endpoint move right; elsewhere move left. The destination
is on the board, off the rook file/rank, and at least two ranks from the strong
king. It is therefore a legal ordinary king move. This witness is used below
only for intervals of length at least two. It is not used to dismiss 1x1 boxes.

## 2. First pair: align the supporting king

Play S:(a-1,b-1)->(a,b-1). This is a one-square move onto an empty square.
W's rank exceeds b, so the destination is at least two ranks from W and the
king is safe. The rook remains adjacent/protected. The preceding reply facts
retain W1.x>a,W1.y>b for EVERY weak reply. The interval[a+1,7] has at least
five files, so the explicit horizontal witness establishes nonemptiness.
Cost: two plies. No progress is charged before this preparation is paid.

## 3. Second pair: protected rook contraction, including crossing

Play R:(a,b)->(a+1,b). The path is one square and clear, the destination is
empty, and the strong king on(a,b-1) protects the new rook diagonally.
W1 is above b and strictly right of a. If W1.x=a+1, this gives a rook check;
otherwise it is a quiet move. The policy permits BOTH cases.

A legal weak reply exists: if W1.x=a+1, move right to(a+2,W1.y);
otherwise take a horizontal neighbour within[a+2,7]. That interval has at
least four files. All these destinations are on board, outside both rook rays,
and at least two ranks from S.

For EVERY reply W2, the rook is uncapturable and W2.y>b. The file a+1 is
attacked above b. From W1.x>=a+1 and a unit king step, W2.x>=a. Excluding
the rook file leaves precisely W2.x>=a+2 OR W2.x=a. The latter is a real
crossing branch and is not thrown away.

In the right branch, the NE target has already been reached in four plies.
The king is diagonally outside the box and its width decreases from7-a to6-a.

## 4. Crossing branch: paid escort and quadrant reversal

In the left branch W2.x=a, leave R on(a+1,b) and play two supporting king
steps along rank b-1:

    (a,b-1)->(a+1,b-1)->(a+2,b-1).

Each step is legal, since every W remains above b and thus at least two ranks
away. Both destinations are on board (a<=2), and neither is the rook square.
At EACH weak turn the rook remains adjacent/protected. Every reply remains
above b and strictly left of a+1 by the ray and unit-step argument. No reply
is selected in favour of the strong player. Each weak turn has the horizontal
witness in[0,a], whose length a+1 is at least two because a>=1.

After these two pairs S=(a+2,b-1), R=(a+1,b), W.x<a+1,W.y>b. The king
is now diagonally outside the NW box. Its width a+1<=3 is strictly less than
the old width7-a>=5. Total cost: eight plies, including both escort replies.

## 5. Closed cost inequality and precise coverage payoff

For a guarded box with dimensions u,v define

    E(u,v)=max(u-4,0)+max(v-4,0),    Phi(u,v)=8*E(u,v).

In this phase h'=h. In the right branch w'=w-1 and w>=5, so E'=E-1.
In the crossing branch w'<=3, while w>=5, so E'<=E-1. Thus

    actual phase plies + Phi(w',h') <= 8 + Phi(w',h') <= Phi(w,h).

This is an actual all-reply phase inequality; orientations are paid for by
the escort, and the rectangle is measured in its actual new quadrant. It does
not assume the weak king stays on the original side of the shifted rook.

For the corresponding reflected/axis phases and an already guarded box with
1<=u,v<=6, induction on E gives a policy reaching dimensions at most4x4 in
at most8*E<=32 plies. The geometric model transport must be retained when
implementing this corollary in Lean. This is a box-entry bound, NOT mate.
Its exact payoff is a closed large-box stage for the principal new strategy.
The exit criterion is an actual guarded <=4x4 box; arbitrary entry and its
small-box mating finish remain required before any global budget follows.

## 6. Why the threshold is strict

At width4, a=3. In a crossing branch the new width a+1 is again4, so the
inequality E'<E is unavailable. The rule is explicitly disabled there.
At width1 a protected shrink can stalemate, as the older frozen control shows.
This proof uses neither width4 contraction nor a width1 horizontal witness.

A selected legal ordinary cycle illustrates why blindly extending the rule
to width4 is wrong. Start S=c3,R=d4,W=e5, strong turn. Play

    Kd3 Ke6, Re4 Kd5, Ke3 Kc5, Kf3 Kd5.

This has S=f3,R=e4,W=d5, the horizontal reflection of the root. Applying the
reflected phase returns to the root in another eight plies. Both kings and
the rook are retained. This is a local clock-free failed-policy control,
not an infinite admitted RAW play or a counterexample to optimal mating.
The selected diagnostic must check every listed move before this is treated
as computationally observed. The symbolic equal-width calculation already
shows why no strict decrease may be asserted at width4.

## Sources and status boundary

The project's frozen KRK move model, step_sound, safe-reply completeness and
rook-rank barrier are the kernel interfaces. Separate source review consulted
Maric, Janicic and Malikovic, CADE2015,
[Proving Correctness of a KRK Chess Endgame Strategy](https://argo.matf.bg.ac.rs/publications/2015/krk-cade.pdf).
It motivates room perimeter and explicit rook safety. Its strategy, Isabelle
proof and termination theorem are not imported as our kernel proof or as any
numeric sub100 result. The guarded phase above and its eight-ply accounting
are proved here directly; the remaining small-box obligation is explicit.

Paper audit, Lean and exact-source Gate F/Z statuses are recorded separately.
Nothing here supplies complete low-clock/history outcomes, full FIDE
correspondence or exact global WDL/DTZ. EC-C050 remains open unless the
remaining geometry and all other closure obligations actually close.


S087 observed Gate F addendum: Own published source `84161c2650b902e98f37252532a706ec50f40ed4`; NEW GitHub clone `C:\engame-checkouts\s087-gate-f`, .lake absent before full214-job build exit0 in371.031s. Complete395-report runner exit0 at2026-10-21T11:36:01Z, full working/clean runner and published source bytes match; standard-three axioms only. Gate Z pending; hosted CI unobserved.
