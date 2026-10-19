# EC-C010 — A protected rook is a rank barrier for every legal lone-king reply

Gate L proof, S024 (2026-10-19). Classical rook/king geometry, no novelty claim. Squares have file x and rank y in 0…7, Chebyshev king distance d∞. All positions and legal moves below are in the general FIDE 2023 kernel, either colour and any castling/en-passant flags.

## Statement
Let q contain exactly strong king S, strong rook R, lone king W, on distinct squares, with the lone king to move. Assume d∞(S,R)=1, y(S)<y(R), and y(R)<y(W). Then **for every legal successor q′** there is a square T such that:

- q′ has the same strong king and rook, and the lone king at T, with the strong side to move;
- d∞(W,T)=1, d∞(S,T)≥2 and the rook does not attack T on the resulting board;
- y(T)>y(R).

Thus rook protection and separation are preserved through every legal defending reply. This says nothing about existence of a reply, decreasing a rank, or reaching mate.

## Kernel move extraction (including captures)
Only the lone king has the mover's colour. It has no rook and cannot castle, regardless of flags; it cannot promote or perform en passant. Any legal move is therefore one king step W→T, and the resulting board overwrites T, empties W and leaves other squares unchanged. The target cannot be S, since capturing a king is forbidden. Legality says the king on T is not attacked after the move.

In particular d∞(S,T)≥2: S remains present, so adjacency would put the moving king in check; equality T=S is already excluded. If T=R and R is protected (d∞(S,R)=1), this is impossible. Hence the rook survives. The remaining board is exactly K+R vs K, and absence of self-check excludes both strong-king adjacency and a clear rook ray to T. This supplies **completeness for all kernel legal replies**, not merely soundness of the cooperative move model. Captures must be excluded before using its non-capturing `StepM.lone` description.

## Barrier proof
Suppose y(T)≤y(R). Since y(W)>y(R) and a king step changes rank by at most one, y(T)=y(R). T is not R. The rook and T therefore share a rank. S is strictly below that rank, so cannot obstruct their ray. The lone king on T is an endpoint and cannot obstruct its own incoming rook ray. Hence the rook attacks T after the move, contradicting legality. Therefore y(T)>y(R).

The finite measure B=7−y(R), the number of ranks strictly above R, is unchanged by a lone-king reply, and the king remains in that region. This is a genuine invariant, **not a decreasing potential**. Its decrease by strong-side play requires a new proof.

## Why the hypotheses and conclusion are narrow
- Protection is needed: if R is hanging, a legal capture can erase the barrier.
- The strict inequality y(S)<y(R) is essential. With White Ke4, Rd4, Black Kg5 (Black to move), Kg4 can cross onto the rook's rank because Ke4 blocks the ray and Kg4 is two files away. Thus “king no higher than rook” would be false.
- Nonempty replies cannot be inferred: White Kc6, Rb7, Black Ka8, Black to move satisfies protection and both strict rank inequalities but is stalemate. It is not a forced win.
- Arbitrary flags do not create lone-side castling because that side has no rook. The proof uses only king moves and kernel self-check.
- Both colours are uniform; the coordinate “above” is an absolute geometric direction, not pawn movement. Horizontal/lower barriers require their corresponding statements; none are silently assumed.

## Remaining forcing gap
Confinement alone permits indefinite cycles. What remains is a strategy that safely establishes and advances a suitable confinement invariant, avoids stalemate, and ensures a natural-valued phase/rank measure decreases against **every** defence. Neither the cooperative route in EC-T0007 nor this barrier theorem proves that progress assertion.

## Attempted progress step and exact obstruction

One might try to raise the rook above its old rank while keeping S fixed and preserving king protection. This is impossible under the strict separation hypothesis: y(S)<y(R)<y(T) gives y(T)−y(S)≥2, hence d∞(S,T)≥2. The lemma `protected_rank_raise_unprotected` records this obstruction. Therefore a forcing proof cannot simply repeat the protected-rank theorem after every rook advance. It needs a larger safety condition (for example a rook too distant for immediate capture, or protected), together with a phase for repositioning the strong king and a separately proved progress measure. This identifies a concrete failure of the first attempted descent scheme, not a claimed impossibility of rook mate.
