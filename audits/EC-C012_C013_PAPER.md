# S026 paper audit — distant safety and the opposed-kings phase

Same-agent adversarial audit, before Lean implementation; no independent external review or novelty claim.

- Arbitrary kernel replies must be extracted before applying non-capturing model geometry. Distant safety excludes capture through move distance; protection through post-move check. Initial check is not excluded.
- The checking rook move is vertical on a file distinct from both kings, so neither king obstructs it. The destination differs from the old rook square by the rank hypothesis.
- A reply below the checked king is covered by the opposed strong king; same-rank replies are on the rook ray. No claim about a cooperative reply substitutes for this universal argument.
- Edge case: no upward on-board rank at y(W)=7 means actual checkmate, with the correct winning colour and zero-ply goal after the chosen move. Away from the edge the straight-up reply supplies nonemptiness.
- The king follow-up preserves a vertical gap of two. A horizontal weak-king reply is always available, including at files a/h; this explicitly excludes stalemate.
- A two-file rook margin fails because the second reply may capture; a three-file margin can leave the rook hanging. The four-file margin is used in the four-ply result. Local controls are recorded in `scripts/krk_check_phase_diagnostic.py`.
- The diagnostic samples 24 chosen configurations in both colour orientations and explores only their first and second reply sets. It is an error-finding supplement, not a proof or table of class outcomes.
- The strict potential decrease is through the whole declared phase. It does not assert that every intervening ply decreases a measure.
- Returned separating-rank states are not silently asserted to meet the opposed-kings entry hypotheses. The setup/re-entry/tempo gap is explicit; EC-C011 remains proposed.
- A full movement/reflection equivalence of the general kernel is not assumed. The proof uses explicit king/rook moves that are sound for any flags; no pawn direction or castling symmetry enters.
