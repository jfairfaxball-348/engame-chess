# S029 — Two-file check, bounded pursuit and a closed rook-wall family

Classical rook technique, 2026-10-19; no novelty claim. FIDE 2023 kernel, exact KRK, either strong colour σ, arbitrary flags. Clock/repetition history is absent. No tablebase, engine, stored evaluations or class enumeration supplies the proof.

## Exact claims

EC-C016: with opposed same-file kings two ranks apart, strong turn, rook off the lone king's rank and at least two files away, the chosen checking rook move is legal. At the upper edge it mates; otherwise its nonempty defending reply set consists entirely of one-rank upward king steps. A surviving rook may be hanging on the following strong turn; no unsupported four-ply king-up claim is made.

EC-C017: in a lower band S.rank+1=R.rank and W.rank=R.rank+1, with rook/lone file distance at least two, an oriented pursuit strategy forces an aligned-file or upper-band exit, conditional on those exits being winning. Every defence is covered. An explicit bounded normalization prevents waiting loops and a decreasing distance of the strong king's file to the approached edge proves finite pursuit.

EC-C018: every exact KRK position with strong to move and **S.rank<R.rank<W.rank** satisfies `ForceMate σ q`. No initial file-margin, rook-protection, global-arrival or PhaseImage assumption is needed. It is a conditional geometric-family forced-mate theorem, not arbitrary-arrival KRK setup or full WDL. It includes every proved S028 PhaseImage. The broader invariant deliberately allows a threatened rook on a *strong* turn, which is repaired before the next defending turn.

## Common legal-action facts

Both kings lie off the rook's rank. A horizontal rook move along that rank is unobstructed, with king separation at least two. To normalize a rook with file distance less than two, move it to file a if W is on e–h, else h. This is a different square, with file margin at least four. With any chosen horizontal target at margin at least three, every weak reply is non-capturing by EC-T0010, stays strictly above the rank wall, and leaves file margin at least two. A horizontal neighbour of W supplies a legal reply, including at files a/h: the initial margin ensures the target is off the rook file, and the king rank separation is at least two. Thus no defending branch is justified vacuously.

For an actual tempo when the rook is already on the far file, use the second-far file: on W files e–h choose a unless the rook is already on a, in which case b; on W files a–d choose h unless already on h, in which case g. The target differs from the source and has margin at least three. This is an actual rook move, not an assumed pass.

In a lower band a legal weak reply cannot descend onto the rook rank. If it does not rise into the upper band, its rank stays fixed and its file changes by exactly one. This dichotomy uses arbitrary-kernel-reply completeness, not a cooperative move assumption.

## Two-file check

The checking target is (R.file,W.rank). With same-file kings, distinct rook file and rook off W's rank, the rook move is legal. File margin two excludes capture on the first weak reply. Existing symbolic opposition geometry proves that every reply rises one rank; no reply exists at rank 7, giving actual checkmate of the named opponent. Below rank 7, a straight-up weak step supplies nonemptiness. The new wall is at the old W rank. It is strictly above the old wall when used from the aligned lower band. This does not weaken the hypotheses of the immutable EC-T0011 four-ply theorem.

## Bounded oriented pursuit

Use orientation d: rightward coordinate x for pursuit to h, leftward coordinate 7−x for pursuit to a. These are coordinate inequalities only; actual legal moves are constructed directly in both directions, with no assumed kernel reflection. Fix a rook rank y and strong rank y−1. A strict sign (oriented W file greater than oriented S file) persists until alignment or an upward exit.

Induct on remaining oriented strong-king distance 7−oriented(S.file).

A **good** state has offset at least two and rook/lone file margin at least three. Move S one file in the pursuit direction. The rank gap of two makes the king move legal; the rook is off the king's rank. Every legal reply is non-capturing and nonempty. An upward reply is an upper-band exit, an aligned reply is an alignment exit, and every other same-band reply retains direction and margin≥2 with the strong king one file nearer the edge. Apply the induction hypothesis to the latter. This is the only recursive pursuit call, and its measure strictly decreases.

An offset-at-least-two state with margin two is normalized by moving the rook to F(x), the far edge from the old lone file x. Every reply has margin≥3. Same-band replies either leave offset at least two (now good), or reach alignment, or have offset one. The last case forces the old offset to be exactly two and the reply to be toward S. Perform a distinct far/second-far waiting move. If this second reply is neither upward nor aligned, its file returns to x. Its new rook margin is at least three:

- rightward pursuit: x≤3 gives second-far g (distance≥3); x=4 switches a→h (distance 3); x≥5 gives second-far b (distance≥4);
- leftward pursuit: the corresponding x≥4, x=3 and x≤2 cases give the same lower bound.

These are symbolic interval cases, not per-position enumeration. The return is now good, so a king step follows. Normalization cannot loop: it contains at most two rook turns before the good state or an exit.

For offset one, make a distinct far/second-far waiting move. A non-exit same-band reply must move away to offset two; margin is still at least two. Apply the previous offset-at-least-two argument. Thus before each recursive king-file advance there are at most three rook turns; all are explicit legal actions with nonempty arbitrary-reply sets. The old chasing cycle is avoided because offset one uses a rook tempo rather than crossing to the lone file.

## Nested wall induction and closed continuation

Induct first on 7−R.rank, then on R.rank−S.rank. Prove the ready case (rook/lone file margin≥2) before normalizing the remaining case at the same measures.

- If W is at least two ranks above R, raise R one rank. Its two-file margin excludes capture; every legal reply stays above the raised wall and preserves KRK. The next strong-turn rook may be hanging, but the outer induction applies to *all* strict rank-wall states at the higher rook rank and supplies the repair. A horizontal weak step proves nonemptiness.
- Otherwise W.rank=R.rank+1. If S is at least two ranks below R, move S one rank up. It remains below the rook; W is at least two ranks from the new king. All replies preserve KRK and the same wall. The inner rank-gap measure decreases, regardless of a possible hanging rook. A horizontal weak reply exists from the ready two-file margin.
- Otherwise both are in the lower band. Apply the bounded pursuit theorem. Aligned exits use the two-file check and hence the outer induction at the raised check rank (or immediate edge mate). Upward exits use the first bullet. Thus the exit-winning assumption is discharged by strictly higher-rank facts, not the current goal.
- Finally, if the original file margin is less than two, choose the far horizontal rook normalization. Every reply is a ready state at the same rook/strong ranks. The already proved ready case handles these without a recursive same-measure call.

Compose each chosen strong move and every defending reply with the frozen `forceMate_choose` and `forceMate_defend`. Their finite-branching rule yields a uniform finite ply bound from the proved well-founded induction; no arbitrary winning continuation or mere liveness assumption is introduced. All nonempty defending nodes have a proved continuation, so the forcing semantics' deadness stop is respected.

## Scope that remains open

This closes the separated rank-wall/PhaseImage family only. Arbitrary legal strong-turn KRK arrivals need not admit this wall; safe setup from arbitrary geometry remains a separate EC-C011 obligation. No complete WDL, clock/repetition, exact distance, seven-piece parity or initial-position claim follows. Frozen ledger remains unchanged until a later Gate Z session.

## Attack on arbitrary setup: a proved subfamily and a concrete obstruction

A safe direct setup subfamily is also available. If W.rank≥S.rank+2, the rook is on a different file from S, and its file distance from W is at least two, move R vertically to (R.file,S.rank+1). If it is already on that rank, the main wall theorem applies immediately. Otherwise neither king blocks the vertical segment (both are on other files), the move is legal, and every weak reply is non-capturing and stays above the new wall. A horizontal reply witnesses nonemptiness. Apply the wall theorem to every strong-turn successor and the forcing one-step rules. This is `krk_vertical_wall_entry_force`, not a universal arbitrary-arrival setup theorem.

The remaining setup is substantive. With White Ka1/Rd4 and Black Kc3, the naive Rd2 creates a rank wall but allows Kxd2; Rb4 creates a file wall but allows Kxb4. Both capture replies leave KK. A safe multi-move rook retreat and a possible change of axis are needed, rather than merely choosing a square geometrically between the kings. Equal-rank kings also require an axis interchange, and downward separation requires a proved reflected policy. No general kernel symmetry for forcing is assumed. These cases remain outside EC-C018's initial separated-rank/vertical-entry hypotheses and keep EC-C011 PROPOSED.
