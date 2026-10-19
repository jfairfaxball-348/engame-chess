# S024 strategy attempt: from confinement to forced mate

The general clock-free KRK target remains unproved. The successful first step is all-defences reply confinement (EC-C010), which provides the universal quantifier missing from the cooperative EC-T0007 route.

A first attempted descent scheme was to retain immediate king protection, hold the strong king fixed below the rook, and raise the rook rank. It fails symbolically: the new rank is at least two above the king, so the rook loses protection. This is proved in `protected_rank_raise_unprotected`. The barrier invariant therefore cannot simply be re-applied after that proposed action.

The likely next state description must allow a distant rook as well as a protected one. At a lone-king turn, a rook at Chebyshev distance at least two cannot be captured on that move; if adjacent it needs adequate king protection. However, “safe from immediate capture” alone does not imply non-stalemate, confinement, eventual progress, or a uniform bound. Each must be supplied separately.

A proposed lexicographic argument would track a confinement region, the strong king's approach to a useful supporting line, and a tempo/relocation phase. The primary measure must decrease only after a verified finite phase, not necessarily after each ply. We have not established an action that restores the necessary invariant and strictly decreases such a measure for all possible replies. In particular, checking/edge phases and quiet waiting moves require independent stalemate checks; a universal over an empty reply set cannot close a win.

No candidate proof is promoted on this proposal. S025 freezes the two completed prerequisites; S026 is to resolve this specific progress/setup gap on paper before further formalisation of EC-C011.
