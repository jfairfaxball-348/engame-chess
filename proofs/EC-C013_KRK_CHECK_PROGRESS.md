# EC-C013 — An opposed-kings checking phase with strict rank progress

S026, Gate L proof (2026-10-19). Classical rook technique; no novelty claim. General FIDE 2023 kernel, either strong colour and any flags. Coordinates are file x and rank y in 0…7. No class-wide enumeration, engine or tablebase is used.

## Exact entry family
The strong side is to move in KRK with strong king S, rook R and lone king W. The kings are opposed vertically:

- x(S)=x(W), y(W)=y(S)+2;
- |x(R)−x(W)|≥4;
- y(R)≠y(W).

Let C=(x(R),y(W)). The first chosen move is R→C, a vertical rook move. It is legal: neither king lies on the rook's file, the target is empty, and the kings stay two ranks apart. It gives check along W's rank. The rook is not king-protected, but its file distance makes capture impossible.

## First defending reply, or mate
For **every** legal reply W→T, SafeRook completeness gives a non-capturing king step. A target on W's old rank is attacked by the rook; the lower strong king cannot block that rank. A target one rank lower is at most one file and one rank from S, hence illegal. Therefore y(T)=y(W)+1, and |x(T)−x(W)|≤1.

If y(W)=7, no such on-board reply exists: the check is mate. The original position has a one-ply forcing win under EC-T0008. This is a general mate-in-one family, not a single tested position.

Otherwise a reply exists: W can step straight up. It is three ranks from S, not on C's file or rank, and on the board. Thus the first phase cannot stalemate. Its upper-edge potential 7−y(W) decreases strictly through every legal reply, and the rook remains at file distance at least three from T.

## Follow-up king phase
After an arbitrary first reply, choose S′=(x(S),y(S)+1). The king step S→S′ is legal: the lone king T is still two ranks above S′, and C is on a different rank. Let U be the resulting lone-to-move position. Its rook is at rank y(W), its strong king strictly below, and T strictly above; the rook is at file distance at least three from T. EC-C012's distant barrier theorem therefore covers **every** legal second reply T→V and gives y(V)>y(W).

The second reply set is nonempty. Choose either horizontal neighbour of T that lies on the board (step right unless T is on file h, then step left). It stays two ranks above S′. Its file differs from x(W) by at most two, so it cannot lie on the rook file, which is at least four files from x(W). It also lies off the rook rank. Hence this explicit horizontal move is legal, and U is not stalemate.

For every second reply, |x(V)−x(W)|≤2 (two unit king steps). Consequently |x(C)−x(V)|≥2 and the rook remains safe from an immediate capture. The resulting strong-to-move position satisfies:

- y(S′)=y(S)+1;
- y(S′)<y(C)<y(V);
- d∞(C,V)≥2;
- 7−y(V)<7−y(W).

Thus this **four-ply phase** makes genuine all-defences progress and returns a distant-rook separating-rank configuration, or it mates in one ply in the edge case. No assumed winning continuation is used in the argument.

## Why the distance margin is four
A margin of two suffices for the first check, but not the follow-up. White Ka1/Rc1, Black Ka3: Rc3+ Kb4, Ka2 permits Kxc3. At margin three, Ka1/Rd1 versus Ka3: Rd3+ Kb4, Ka2 Kc4 leaves the rook en prise. Margin four accounts for both defending plies and preserves distance at least two. These controls will be checked locally and in representative kernel examples.

## Remaining setup/tempo gap (EC-C011 remains PROPOSED)
The final state need not have opposed kings: the lone king may be up to two files from S′ or more than two ranks above it. Arbitrary strong-to-move legal KRK positions also need not enter this family. A full strategy must force entry or re-entry into a rotated/reflected opposed family, or achieve another strict contraction, while preserving rook safety and avoiding stalemate. Repeatedly chasing the lone king's file does not suffice: on the edge a king can reverse direction when the chasing king follows, and lateral movement need not decrease a rank potential. An adaptive box/opposition or tempo argument remains necessary. This paper proves the stated advancing family, not the general KRK forced-win theorem or WDL classification.

**Termination-rule boundary.** All nonterminal positions of this phase are live: safe weak-turn nodes with nonempty replies use `krk_safe_weak_live`; strong-turn successors of legal KRK moves use EC-T0007. The initial state inherits liveness from its checked successor (or the terminal mate). Thus the legal paths do not require play to continue after a dead-position draw. No complete forcing continuation is inferred from this liveness fact.
