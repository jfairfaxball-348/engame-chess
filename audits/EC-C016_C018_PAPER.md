# S029 adversarial paper audit

Same-agent review before formalisation, no independent external audit.

- Two-file checking covers only the first check/reply; a later hanging rook must be repaired on the strong turn. It does not inherit the frozen four-file king-up theorem.
- Strict rank separation excludes both blockers on the rook row and king adjacency. An initially threatened rook is allowed only on the strong turn, when the prescribed normalization acts first.
- Actual waiting moves must differ from the source. Far/second-far selection guarantees this, including the d/e switch, and retains margin≥3 before a weak reply.
- Every weak reply begins with safe capture exclusion and is extracted from kernel Legal. A same-band step must change its file by one; lower steps are barred by the rook ray.
- Orientation reflects coordinate inequalities only. Construct actual left/right moves; never infer arbitrary kernel symmetry or flags symmetry.
- A chase at offset one reproduces the old cycle; the policy waits instead. At offset≥2 a king step cannot permit a sign reversal without an alignment exit.
- Normalization has a potentially dangerous offset-two→one branch. The next non-exit waiting reply must return to the original lone file; the source/target edge cases must be proved to recover margin≥3 before another king step. Do not recurse at the same pursuit measure.
- King-file induction terminates at the approached boundary; impossible off-board chasing must be eliminated from the offset hypothesis, not supplied a clipped or stationary move.
- Raising the rook can increase the king/rook gap. Nested outer rook-rank and inner king-gap induction deliberately admits that state. Normalization at unchanged measures uses an already proved ready case, not circular recursion.
- Reply existence needs explicit witnesses at all board edges. Deadness/liveness cannot replace a nonempty reply set or a forcing continuation.
- Main claim remains conditional on strict rank-wall geometry; arbitrary-arrival setup and EC-C011 must not be promoted without a separate argument.

Direct-entry audit: the rook's file must differ from the strong king's file to avoid a blocked vertical segment; the two-file lone-king margin prevents a capture on the new weak turn. If the rook is already on the target rank, use the wall result rather than a zero move. Ka1/Rd4/Kc3 permits both Rd2 Kxd2 and Rb4 Kxb4; a geometric wall alone on a weak turn is insufficient. Equal-rank/downward/axis-switch arbitrary setup is not proved by the new theorem.
