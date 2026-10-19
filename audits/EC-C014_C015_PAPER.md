# S028 adversarial paper audit — phase image and rank contraction

Same-agent audit before Lean implementation; no independent external review.

- Exact image rank interval requires arbitrary-reply completeness and the rook barrier, not just unit distance: the raw second step could return to the rook rank without legality.
- Image file displacement is two, not one; Ka2/Rh3/Kc4 already falsifies opposed-file restoration. A final lone king can be two ranks above the rook; the family cannot require a fixed vertical gap.
- The four-file rook/strong margin follows because the chosen king-up preserves its file, not because every king move would do so.
- Rank advance constructs a Fin 8 target using the weak king's upper rank bound; an edge source cannot satisfy the hypotheses. A king below the source cannot block the rook's vertical segment; the lone king is above the destination.
- Reply existence is constructive at both file edges. Three-file separation leaves at least two after either horizontal witness and after any actual reply.
- A two-file margin can leave the raised rook hanging after a diagonal reply. A one-rank weak/rook gap can permit immediate rook capture after raising, so the upper-band hypothesis is substantive.
- Barrier-rank potential falls across exactly this phase, not every ply of an unspecified global strategy. The phase may break the one-rank strong-king/rook gap and therefore does not close a repeated invariant.
- No kernel rotation/reflection is assumed. Both colours are parameters to the same direct move proofs; all flags are arbitrary.
- Kernel examples and selected local trajectories will be used for failed-policy controls only. No class-wide graph, solved-position table, minimax/retrograde value or engine result enters either argument.
- The remaining all-defences policy from the entire image family and safe setup from arbitrary legal arrivals are unresolved obligations. EC-C011 must remain PROPOSED.

Further rescue audit: a two-file upper-band margin is enough for initial capture exclusion, but not final immediate safety. The repair must happen on the strong turn before any extra weak reply. The far-file target is selected from the current lone-king file; its four-file distance guarantees it differs from any unsafe old rook. The row is unobstructed because both kings are strictly off it. Horizontal reply existence needs king rank separation at least two; in the rank-raise application it is at least three. The repair keeps the raised rank, so it cannot undo the contracted rank strip. It does not solve the lower-band tempo problem.
