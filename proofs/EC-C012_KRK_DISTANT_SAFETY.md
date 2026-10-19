# EC-C012 — Distant-or-protected rook safety and arbitrary reply completeness

S026, Gate L proof (2026-10-19). Classical king/rook geometry; no novelty claim. General FIDE 2023 legal-move kernel, exact KRK material, either colour, arbitrary flags, lone king to move. No claim about clocks, repetition or global reachability.

Define `SafeRook(S,R,W)` by d∞(R,W)≥2 or d∞(S,R)=1. **Theorem:** under this condition every kernel-legal lone-king reply preserves KRK, is a non-capturing `StepM.lone` move, changes the lone king by one square, and ends with kings at distance at least two and no rook ray checking the lone king. It does not assert that a reply exists or that safety against capture is preserved for a later turn.

Proof: extract the arbitrary kernel-legal move as in EC-T0009. The mover is the unique lone king; no lone rook means no castling, and a king cannot promote or capture a king. If its target were R, the move distance would be d∞(W,R)=1. This contradicts the distant disjunct. In the protected disjunct, the surviving strong king would attack the destination, contradicting post-move self-check safety. Thus the rook survives. The resulting board is exactly KRK; legality then gives both king separation and absence of a rook ray. Initial check is allowed: safety is checked on the resulting board.

**Extended barrier:** if the strong king lies strictly below the rook rank and the lone king strictly above it, `SafeRook` suffices to keep every legal lone-king reply above the rook rank. First use the preceding completeness theorem to exclude capture; then apply the pure geometric `rook_rank_barrier` of EC-T0009. This extends confinement to an unprotected but distant rook without changing frozen modules.

This is an immediate safety theorem only. If the distance disjunct fails and the rook is not protected, geometry permits an immediate capture: since squares are distinct, the weak king is adjacent to R and S is at distance at least two from R. The explicit king step W→R then leaves safe K vs K. A complete kernel equivalence for capture availability is a useful later statement; it is not needed or claimed as part of the formal sufficiency bundle here.

**Liveness bridge.** If the safe lone-to-move state has at least one legal reply, completeness gives a strong-to-move KRK successor after a legal move. It is live by EC-T0007. Prefixing its mating path shows the preceding state is live too (`krk_safe_weak_live`). Consequently the nonempty, safe weak-turn states used in the checking phase are not dead draws.
