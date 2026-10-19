# S026 — A genuine advancing phase, and the remaining re-entry gap

The protected-rook advance from S024 could not keep protection with a fixed lower king. S026 replaces that restriction by immediate safety from distance or protection, and proves arbitrary kernel reply completeness and the extended barrier.

The successful construction starts with vertically opposed kings two ranks apart and a rook at least four files away. Check along the lone king's rank. Every reply rises one rank; at the top edge this is mate. Otherwise advance the strong king one rank. Every subsequent reply remains beyond the new rook barrier, at distance at least two from the rook, with strictly smaller `7 - weakRank`. Both defending reply sets are proved nonempty when not mate. This is an explicit finite phase against all defences, not a cooperative route or an assumed winning continuation.

Two weaker margins were falsified: a two-file margin permits second-reply capture; three files can leave the rook hanging. Both controls are kernel-checked. The chosen four-file margin absorbs two possible file steps. The local diagnostic checks only 24 selected configurations and their two reply sets; it does not construct a class graph or compute WDL.

The full theorem is not closed. A legal phase can return Ka2/Rh3 versus Kc4, strong to move: the kings are not on the same file. Applying the opposed-kings theorem again would therefore be invalid. Pure lateral following also offers no established strict descent: the lone king can change direction, and an invariant wall alone does not establish termination. A king-approach, tempo or adaptive-axis phase is required to force re-entry or another contraction.

The narrow image worth attacking has rook one rank above the strong king, weak king one or two ranks above the rook, file offset at most two between kings, rook at least four files from the strong king and at least two king steps from the weak king. These are suggested by the actual two unit replies; they need an explicit image-bound lemma before formal reuse. The remaining all-defences policy must handle the edge and waiting moves without stalemate or rook loss. Safe setup from arbitrary legal strong-to-move arrivals is a separate obligation as well.

EC-C012/013 are prerequisites. EC-C011 stays PROPOSED; no full FIDE WDL, clock/repetition result, distance theorem, seven-piece parity or initial-position draw is claimed.
