# S089 — Guarded small-box mating attack

2026-10-21. Direct continuation of EC-C050 after the normalized large-box phase
was frozen as EC-T0047. A sufficiently SHORT whole <=4x4 finish remains unproved. No
new global numeric bound, class classification or frozen theorem is asserted.

## Principal obligation and accounting

For every guarded box in a proved coordinate frame, strong king diagonally
outside the rook corner, weak king strictly in the opposite quadrant, both
dimensions<=4, give an actual all-defence mating strategy with a DERIVED uniform
ply cap F small enough for the combined budget. The existing frozen wall proof
ALREADY gives these normalized inputs a finite MateWithin292 ceiling:
73*(7-b)<=292 since b>=3. Finite mating/termination here is NOT the missing
claim. We need a shorter finish to meet the clock-safe global target.
Then separately prove arbitrary guarded-box entry at cost E and the
needed phase transports. Any global bound must pay ALL these costs. The paper
large-box entry cap32 ends at a small box, not mate, and is not itself a frozen
transport/iteration theorem. An inequality such as E+32+F<=95 is an obligation,
not permission to assume F or E. At an already guarded root E=0, F<=63 would
be sufficient for32+F<=95; that63 is a derived budget TARGET, not a proved
chess bound. Arbitrary entry must still be paid. Existing442/443 global ceilings
remain unchanged.

Sources are the project's frozen KRK model, actual safe-reply completeness,
step_sound, two-file edge check, wall/box geometry and EC-T0047. No tablebase,
engine, game-value lookahead, class enumeration or position-value certificates.

## A closed terminal case: seven plies for the guarded 1x1 corner

In normalized coordinates take S=f6=(5,5), R=g7=(6,6), W=h8=(7,7), strong
turn. This is an exact KRK root, arbitrary flags and either material colour.
It is the guarded NE 1x1 case. The following clock-free policy mates within
SEVEN board plies, retaining every legal weak reply:

    Ra7, ...Kg8 forced; Rb7, ...Kf8 OR ...Kh8.
    If ...Kf8: Rb8#.
    If ...Kh8: Kg6, ...Kg8 forced; Rb8#.

These are ordinary moves in the active frame; algebraic labels specify squares,
not a restriction to White material. Reflection/axis versions require the
existing geometric/budget transport, not full history symmetry.

Proof of every action and reply:

1. Ra7 moves horizontally along rank6. Its path meets neither king, and its
   destination is empty. The strong king remains two ranks from W. At the weak
   turn the rook is distant and cannot be captured. A weak king starting h8 can
   only reach files g/h, ranks7/8. Rank7 is attacked by Ra7 with no intervening
   piece; remaining on h8 is not a move. Only Kg8 remains, and it is legal:
   its rank separation from S=f6 is2 and it is off both rook rays.
2. Rb7 is a legal one-square rook move, still distant from W=g8. Every legal
   weak move stays on rank8, since rank7 is attacked. From g8 its only other
   files on that rank are f and h. Both are on board, off the rook file, and
   two ranks from S. Hence BOTH Kf8 and Kh8 are legal and this list is complete.
3. With W=f8, Rb8 is legal and gives check. The weak side has no other piece
   and cannot castle without a rook. A move on rank8 remains under the rook's
   unblocked ray. The only lower neighbouring rank is7 and every possible file
   there (e/f/g) is adjacent to S=f6. Capturing Rb8 is not a unit king move.
   Thus no legal reply exists and this is actual named mate in5 plies.
4. With W=h8, Kg6 moves S from f6 to g6, a one-square move onto an empty square
   still two ranks from W. Rb7 remains distant. All weak rank7 moves are attacked
   by the rook; the only remaining moving neighbour on rank8 is g8. It is legal,
   being two ranks from S=g6 and off both rook rays. After forced Kg8, Rb8 is
   legal and checking. All rank8 neighbours are rook-attacked; rank7 neighbours
   f/g/h are adjacent to S=g6. Rb8 is too distant to capture. Hence actual mate
   follows in7 plies on this branch.

This resolves the terminal trap by temporarily reopening the box, NOT by
shrinking it into stalemate. Every nonterminal weak node has its explicit legal
reply above. The normal root is nondead by this actual finite mating policy.
No compatible initial-rooted clock0 history is asserted. A hypothetical admitted
root with an eventual formally supplied MateWithin7 could use the existing
fresh-history lift, but no new RAW theorem is proved in this session.

Status of this terminal lemma: paper-verified after a separate same-agent audit;
NOT Lean verified, Gate F checked or frozen. It is not a full small-box result.

## Rejected repair: check and restore the rook

The large-box policy can cross the rook file. A tempting small-box repair is
to return the rook with check, then return the supporting king, hoping the
check has forced progress. This can return the exact board in eight plies.

Start S=c3=(2,2), R=d4=(3,3), W=f5=(5,4), strong turn:

    Kd3 Ke5, Re4 Kd5, Rd4 Ke5, Kc3 Kf5.

All rook positions at weak turns are protected. The two rook moves give checks,
but the king replies evade them, and the final board/turn equals the root.
Room and critical-square distance are functions of that board, so neither a
strict room measure nor their strictly decreasing combination can justify
this entire cycle. The selected local ordinary-move diagnostic must validate
all eight moves before this is called computationally observed. No admitted
infinite RAW play, optimal-distance claim or counterexample to a better mating
policy follows. The rule is rejected; the global EC-C050 claim is not.

## Additional attempted replacements and their unresolved conditions

* Quiet shrink only: after S has moved to support one axis, the weak king can
  stay one square from that rook coordinate by moving along the other axis.
  A proposed shrink along that other axis can leave the rook unprotected and
  immediately capturable. Supporting one contraction does not protect both.
* Approaching the corner: the next king square may be occupied by the rook,
  or adjacent to W. A formal policy must exhibit an actual legal alternative,
  not count a blocked diagonal as one unit of progress.
* Opposed kings with rook file margin1: a rook check along the weak king's rank
  can leave the checking rook capturable. The frozen two-file check theorem
  cannot be invoked with a one-file margin. The corner policy above first
  establishes a distant rook and retains the induced replies.
* Room+critical-square-distance potential: merely naming this quantity gives
  no all-reply decrease, and the explicit check-and-restore cycle defeats a
  strict board-only decrease along that policy. Another action/phase and its
  actual cost inequality are needed.

## Exact frontier

The 1x1 finish is closed on paper, with a derived7 cap. Guarded boxes of larger
dimensions up to4x4 have no sufficiently SHORT all-defence mating policy in this
attempt; their old finite292 ceiling remains available. Consequently the needed
short F for the full small-box domain, arbitrary entry E,
their transports/composition and the global sub100 certificate remain OPEN.
No new Lean or freeze is justified for the WHOLE finish; no new ledger row.
All47 frozen bundles are unchanged. Full low-clock/incoming-history outcomes,
FIDE correspondence and exact global WDL/DTZ are additional open obligations.
