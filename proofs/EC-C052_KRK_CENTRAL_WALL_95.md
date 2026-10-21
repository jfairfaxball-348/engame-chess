# EC-C052 — Centralised all-defence KRK wall strategy, candidate95 ceiling strengthened to93

S090-S091,2026-10-21. FROZEN as EC-T0048 after separate own-source Gate F/Z.
Earlier pending-status notes below are chronological; this is the current status.
Classical king/rook confinement and centralisation; no novelty claim. No
tablebase, engine oracle, class enumeration or stored position values. This
attacks EC-C050's WHOLE wall obligation, not an isolated family or library goal.

## Statement and exact payoff

For either strong colour sigma, every exact strong-turn kernel KRK position
with squares S,R,W and S.y<R.y<W.y has MateWithin sigma93. All raw flags and
EVERY actual legal weak reply are included. No incoming weak-noncheck premise
is needed for this wall statement. Coordinates range0..7; costs are BOARD PLIES.

If verified, existing parametric setup gives every strong legal arrival97,
and safe nonterminal weak inputs98. BOTH are strictly<100 and enter the
existing clock0 lift; no incoming repetition-count premise is required.
Neither budget is optimal distance. Complete arbitrary-history outcomes,
full FIDE correspondence and exact global WDL/DTZ remain separate obligations.

## Interfaces and conventions

A full wall has strong turn and S.y<R.y<W.y. Put n=7-R.y,1<=n<=6.
A close wall also has S.y+1=R.y. It is central if S.x is3 or4, and ready if
|R.x-W.x|>=2. An exit is a READY close wall with EITHER W.y>=R.y+2 OR W.x=S.x.
Thus an exit never discards a hanging-rook/check-safety condition.

All moves below use the frozen geometric StepM soundness at arbitrary flags.
Actual weak reply completeness is krk_safe_reply: the weak side has no rook
with which to castle; a distant OR protected rook cannot be captured. The
horizontal rook barrier holds whenever S is strictly below R. At every weak
turn a legal reply witness is supplied; there is no vacuous stalemate branch.
Finite all-reply phases compose with MateWithin, costing2 per full pair.

Logical reflections/axis swaps are StepM geometry transports followed by the
existing same-budget kernel transport, not symmetries of full RAW histories.
Use a canonical noRights source where the existing transport requires it.

### Primitive actions

* A non-null horizontal rook relocation on the wall rank with destination
  file margin>=3 is legal and every weak reply remains above the wall with
  margin>=2. Weak replies are nonempty by the frozen wall-rook action.
* With lower-band ranks S.y=r-1,R.y=r,W.y=r+1, a strong king file step
  toward W at file offset>=2 and rook file margin>=3 is legal. EVERY reply
  either exits upward, aligns files, or retains its direction and rook margin
  >=2. Non-exit weak replies change file by EXACTLY1.
* A strong king step staying strictly below the rook is legal if its destination
  stays at least two ranks from W. If the current rook file margin is>=2,
  it is uncapturable on the ensuing weak turn. Nonemptiness follows from a
  horizontal weak neighbour off the rook file; the frozen barrier witness uses
  precisely margin>=2, not>=3. Subsequent margin may fall to1 at a STRONG turn.

No primitive assumes a free tempo. All rook moves must be distinct; choices
and boundary cases are checked below.

## 1. Oriented pursuit and the10-ply central exit bound

Orient files so S.x=s<W.x=u, using x or7-x. Let v be the oriented rook file.
Ranks are not changed by this orientation. For a lower-band non-exit define
d=u-s>0. A king-file advance preserves the parity of d: one strong +1 and a
weak +/-1 change d by0 or-2. A rook tempo flips the parity. A weak reply that
goes upward is an EARLY exit; the remainder of its budget is not spent.

Use these actual rook destinations, in oriented coordinates:

    Normalize: 0 if u>=3, otherwise7.
    Wait:      if u>=4, 0 unless v=0, then1;
               if u=3, 0 unless v=0, then7;
               if u<=2, 7 unless v=7, then6.

At d=1 use Wait, including when the old rook is threatened. At d>=2 use a
king advance when margin>=3, otherwise Normalize. Stop at a ready aligned/
upper exit. An initial upper exit with insufficient margin is repaired first.
For an initially aligned but unready central state, first use a far>=4
horizontal rook relocation, then the same policy for whichever direction remains.

Every Wait is distinct and has BEFORE-move file margin>=3. Normalize is needed
only at margin<=2, so its >=3 target is distinct. At s>=1,d>=2, u>=3 and
Normalize is0. When d=1,u<=2 the forward files7/6 have ample margin; at u=3
the special7 avoids an invalid one-file checking exit. These checks forbid the
old silent one-file capture/stalemate repair.

For s>=3, u>=s+1>=4. Wait always places R on0/1; Normalize always places it
on0. Once R is on0/1, every continued non-exit has u>=s+1>=4 and every wide
input has u>=s+2>=5; no further normalization is needed. One eventual d=1
wait makes d even (or exits), so no later d=1 occurs under king advances.

Before the first relocation an arbitrary rook can require at most ONE
normalization: a wide good state cannot have a rook>=3 files AHEAD, since
u>=s+2>=5 and files end at7. A behind rook that becomes too close is relocated
once to0; it may then need the single waiting tempo just described. Thus at
most TWO rook tempos occur, and at most6-s<=3 king advances. This is at most
five pairs, TEN plies to an exit. The final king file cannot be0/7: a king step
requires offset>=2, so a continued oriented king never advances beyond6.

Initial central alignment/unready: the far relocation costs one pair. A
lower-band reply aligns or is at offset1; an upper reply exits if ready. The
offset1 wait places the rook on the corresponding back0/1 and makes offset2
or exits. At most3 king steps remain: again at most five pairs TOTAL. If an
initial upper/unready relocation drops to the lower band without changing
file, this does not invalidate the count: there is still at most one later wait
after the back relocation. No parity-flip claim is made for an upper-band reply.

Conclusion Pcentral=10 for ANY central close wall, including a threatened rook.
The output is an exit with rook margin>=2 and king file in[1,6]. Both directions
and arbitrary flags are retained; early upper replies are charged as prefixes.

## 2. Collinear positive-file start:16-ply exit bound

This special INITIAL shape is needed by the guarded-cut continuation:
S.x=R.x=b,1<=b<=6, W.x>b, with a close wall. Its upper-ready case exits at0.
The formalisation review replaced the original low-file pursuit case split
with this shorter escort argument. In that split, a last king step could have
entry margin2, so citing the frozen margin3 pursuit action there was too strong.
The replacement uses exactly the margin2 below-wall primitive stated above.

More generally, ANY close wall with S.x in[1,6] reaches a full central close
wall in at most THREE pairs. If S is already central, use Section1 directly.
Otherwise, when the initial rook margin is<3, relocate R to a far file at
distance>=4; this is distinct and its weak reply leaves margin>=3. Otherwise
omit that pair. At most TWO same-rank king steps then move S toward[3,4].
Before the first step margin>=3; after its weak reply margin>=2, sufficient
for the second step. Both king targets stay below R, at least two ranks from
W. All weak replies stay above R, and the final margin may be1: Section1
accepts exactly this full central wall without requiring readiness. Each weak
node has the margin2 horizontal reply witness. No weak file-motion/parity
assumption or upper-to-lower special case is needed in this prefix.

The prefix costs at most6 plies and Section1 costs10, giving16. Use this
sharper budget in the integrated route. This argument
does not require collinearity or a specified weak file, so it applies in
particular to the exact guarded-entry shape. It adds no separate research goal.

Conclusion Pcolumn=16, output ready exit after Section1, final strong file
in[1,6]. Only the intermediate escort endpoint is full and may be unready.

## 3. One rank advance and a six-ply central restoration

At a ready exit: if lower-band/aligned, use the frozen two-file opposition
check. It is mate in1 at the edge; otherwise the check and EVERY reply cost2,
raise the rook rank by1 and leave the strong king two ranks below that rook.
If upper, raise the rook rank by1 in one rook move. File margin>=2 BEFORE
the weak turn makes capture impossible. A horizontal neighbour off the rook
file witnesses a reply; all actual replies stay above the raised rook. This
variant needs only the barrier conclusion, not the older distant-rook>=2
POST-reply conclusion that demanded entry margin>=3. Post-margin may be1.

After either nonterminal action, the king's file is in[1,6]. If rook/weak file
margin<3, relocate to a far file with margin>=4, costing2 and leaving margin
>=3. Otherwise do not relocate. Move the king one rank up and one file toward
the central interval[3,4] (or keep its file if central). Every destination is
still at least two ranks from W. Before this king move margin>=3, after every
reply margin>=2. If the king file is now2 or5, take one more horizontal step
into[3,4]. Before that weak turn margin>=2 excludes capture; its successor
may have margin1, which Section1 explicitly permits at a STRONG root.

This restores a full CENTRAL close wall within at most THREE pairs, SIX plies.
Its n decreases by1. Every weak node has a horizontal legal witness; rook
capture, stalemate and a missing move at a board edge are not discarded.

## 4. Central walls at small n

Let T(n)=18*(n-1)+11 for1<=n<=3 (the same recurrence works for larger n,
but we use cuts there). Section1 costs10 to an exit. At n1 no upper exit is
possible; the aligned check mates in1. At n>=2, exit advance costs2, restoration
costs6, then T(n-1). Hence T(n)=10+2+6+T(n-1). Numerals:

    T(1)=11, T(2)=29, T(3)=47.

This is a quantified all-defence recurrence with actual chess actions, not
an upper-envelope number substituted for a strategy.

## 5. Guarded narrow cuts: width2/3 mates within55

Canonical guarded NE input S=(a-1,b-1),R=(a,b),W.x>a,W.y>b, with
2<=w=7-a<=4 and1<=h=7-b<=6. Move S UP to(a-1,b), costing one pair.
The rook stays protected. Both upward/right rook rays into the weak quadrant
are unblocked; weak replies cannot cross either or capture the rook. A horizontal
neighbour in[a+1,7] witnesses a legal reply because w>=2; its file remains at
least two files from S. This proof does NOT claim that move is safe at w=h=1:
there it stalemates, and that unused case is excluded explicitly.

Swap axes. The active wall is close, n=w, its strong and rook file are both b,
and the weak file is>b. Section2 gives an exit within16. If w1 were included
one would need a separate terminal argument; WE DO NOT INCLUDE IT. For w>=2,
advance2, restoration6, and T(w-1), with w-1<=3. Total

    G(w)=2+16+2+6+[18*(w-2)+11] = 18*w+1.

Thus w2 costs37, w3 costs55, w4 costs73. The global cut below uses ONLY w2/3.
This covers the whole required cut-continuation family, all other dimensions
h1..6, not one selected corner. No 1x1 formalisation is needed for this route.

## 6. Protected perpendicular cut from a central close wall

If lower-band W is at file offset>=2 from central S, move R horizontally on
its current rank to the file one step from S TOWARD W. If already there,
the guarded box already holds and no null rook move is made. Otherwise the
ray is clear and the destination rook is diagonally protected by S. Every
weak reply preserves both rays' side constraints; capture is impossible.
The weak file interval toward its edge has length2 or3 (S.x3/4), giving a
horizontal legal reply witness. No one-square stalemate box is created.

Reflect horizontally if necessary. The endpoint is exactly Section5 with
width2/3 and other dimension n<=6. Cost<=2+55=57, independently of n.

At a READY central close root: an upper/aligned root is already an exit.
A wide lower root cuts immediately. At offset1 use a distinct horizontal
rook tempo with destination margin>=3; every reply is upper, aligned, or wide.
Thus at most2 plies of SEARCH precede an exit or cut. A FULL central root
may first need a far rook repair if margin<2; after that pair margin>=3.
Full search therefore costs<=4. All newly selected rook tempos are paid.

## 7. Whole central bounds, with ready/full distinguished

Let F(n) bound FULL central close walls. For n1..3 use Section4. For n4..6,
full search leads either to a cut or to a rank advance plus full restoration:

    F(n) <= max(4+2+55, 4+2+6+F(n-1)).
    F(1..6) = 11,29,47,61,73,85.

For READY roots the first search costs2 instead4; the child after restoration
is FULL, not silently ready. Therefore

    R(1..3) <= 11,29,47,
    R(4)<=max(59,10+47)=59,
    R(5)<=max(59,10+61)=71,
    R(6)<=max(59,10+73)=83.

The initial ready/full distinction is essential to the final93, not notation.
Neither the hanging-rook successor nor its two-ply repair is forgotten.

## 8. Initial wall centralisation, preserving every weak reply

From any full wall at rook rank r, target the strong king's rank r-1 and a
nearest central file3/4. Each king move advances the still-missing coordinates
by one, so t=max(r-1-S.y, distance(S.x,[3,4])) king moves suffice. Destinations
stay strictly below R and at least two ranks from W, so they are legal.

The implemented proof groups the king moves into blocks of TWO. At a block
start, repair if margin<3, using a distinct far-file relocation with margin>=4;
its weak reply leaves margin>=3. Each king/reply pair reduces margin by at
most1, so both moves are safe. Repeat at distance t-2. A final ONE-move block
uses the same preparation and ends at margin>=2. At distance0 only, repair
if margin<2. Thus there are at most floor(t/2)+1 repairs, including the
possible final repair after an even t. The bound includes t0. This conservative
block policy is the policy formalised, rather than an assumed free tempo.

All weak nodes have legal horizontal witnesses, all moves keep the original
rook rank, all weak replies stay above it, and no diagonal king approach crosses
or lands on R. Output is CENTRAL, close and READY. Since r=7-n:

| n | bound on t | centralisation plies | ready remainder | total |
|---|---|---|---|---|
|6|3|10|83|93|
|5|3|10|71|81|
|4|3|10|59|69|
|3|3|10|47|57|
|2|4|14|29|43|
|1|5|16|11|27|

Each total is<=93. This closes the strengthened ALL-wall93 strategy on paper if
the separate audit validates the pursuit, composition, transport and every
nonempty/terminal branch. No Lean or freeze status is inferred from the table.

## Verification admission and frontier

The needed new lemmas are exactly the phase actions/costs above: central and
collinear exit bounds, six-ply restoration, guarded narrow-cut continuation,
ready/full central induction and initial costed centralisation. Existing frozen
statements lose these file/phase relations or carry73 per rank, so they do not
prove95 by substitution. The margin2 rank-advance barrier variant is needed by
Section3, not admitted as general library work. Exit immediately into this
global proof. No standalone corner7 freeze or unrelated prerequisite is planned.

Known controls remain: no-wait cycles, protected1x1 stalemate, width4 escort/
check-restore cycles. The proposed policy avoids those rules: it permits only
ready opposition checks and guarded cuts of width2/3; it never iterates the
failed box-shrink rule. Selected local policy traces may test this construction
but cannot establish the universal claim. The [separate paper audit](../audits/EC-C052_KRK_CENTRAL_WALL_PAPER.md)
records LOCAL_VERIFIED scope and remaining formal obligations. Fresh own-source
Gate F and separate Gate Z are still required after Lean.

## 9. Clock-zero outcome coverage on BOTH turns

The two-ply gain is needed by the missing weak-turn clock0 domain:98 now
fits the strict<100 lift, unlike the earlier100. On every admitted RAW KRK
state with clock0, the strong side actually wins exactly when the board has
strong turn OR is already mate OR has a safe rook and a legal move. For weak
turn this is the frozen clock-free safe-rook/mate classification; use weak98
then the frozen incoming-count-free clock0 lift. On strong turn, the admitted
trace cannot be initial (initial is not KRK), so it ends with a kernel-legal
incoming move. Strong arrival97 and the same lift give actual win. Conversely,
an actual RAW winning policy yields a RAW forcing certificate; projection
gives clock-free forcing, and the frozen board classification gives exactly
the stated criterion. Dead/stalemated or capturable-rook weak roots therefore
fail the winning criterion. Existing strong holding and complementary weak
holding supply their strategy interpretation; no full FIDE correspondence or
positive-clock classification is asserted. This is a complete named subdomain,
not another conditional geometric family or a redefinition of winning.

The original95/99/100 published source has a distinct verification record.
The stronger93/97/98 source and the clock0 classification require their own
exact-source checks before promotion; no result from the earlier checkout is
attributed to the tightened source. No separate95 bundle is to be frozen.

## Observed final own-source Gate F

Own published proof source `2311abe71bc1a4eed47026feccd5ba5a0760d5bb`; NEW GitHub clone `C:\engame-checkouts\s090-gate-f93`, .lake absent before full243-job build exit0 in372.594s. Complete421-report runner exit0 at2026-10-21T13:11:36Z; all26 exact main types and standard-three axioms inspected. Entire working/clean runner and all published formal bytes match,204 transitive modules/246 source/config files hashed. Official native Windows Lean4.35.0, inherited environment. Hosted CI unobserved. Separate fresh Gate Z pending.

The final93/97/98 and explicit clock0 winning criterion are FORMAL_VERIFIED.
This supersedes pending-F wording in earlier chronological notes; no claim of
Gate Z, ledger change, positive-clock completeness, FIDE or exact distances.

## S091 separate own-source Gate Z and freeze

Own proof source `2311abe71bc1a4eed47026feccd5ba5a0760d5bb`; separate NEW GitHub clone `C:\engame-checkouts\s091-gate-z`, .lake absent,243-job full build exit0 in367.828s; complete421-report runner exit0 at2026-10-21T13:20:15Z. Entire own Gate F source/import/declaration inventories and full runner match; standard-three axioms only. All29 complete modules/26 main declarations frozen as EC-T0048. Hosted CI unobserved.

[Immutable EC-T0048 manifest](../theorems/frozen/EC-T0048/v1.md) records the
exact full scope and module boundary. Earlier frozen sources/rows are preserved.
Positive-clock/history, full FIDE and exact distance obligations remain OPEN.
