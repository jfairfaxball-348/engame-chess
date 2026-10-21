# S092 separate audit of the full-history barrier reduction

2026-10-21. Same-agent separate reasoning pass, not external review.

Root distinction: banning every old-count>=2 root would wrongly forbid a
strong player declining its own optional claim. Exempt only the initial root;
weak root still requires count<3. Future strong vertices are NOT exempt because
the preceding weak side may claim an INTENDED repetition. The paper handles
that parent, not an imagined strong current claim.

Mate/terminal boundaries: mate leaves precede claim/automatic-draw handling.
At a root terminal draw, Ongoing is false and no nonmate win is inferred.
The high-clock strong B=1 branch must immediately mate. Weak B<=1 has no
nonmate all-reply tree because turns force two plies before any mate leaf.
Equality h+mate-depth=100 is permitted; strict<100 is not used as necessity.

Repeated-key concern: an arbitrary C_H tree need not be key-simple. The
sufficiency direction explicitly REPLACES it by a least-rank A_H policy and
proves rank key-invariance using the existing exact legal-child interface.
This construction is required and not yet a Lean theorem. At a forbidden
root, future A_H lines cannot return to its key; if a return were mate, key
mate-invariance contradicts the original nonmate root. At an allowed root,
use A_H from the root rather than attach an unrelated child policy.

Incoming-count concern: H includes the root, and every future occurrence is
added to that exact count. An allowed future key has old count<=1 and occurs
only once on the new line, so count<=2, not1. A weak intended move is covered
because ALL its actual legal children remain in the policy tree. No favourable
branch or capturable-rook draw is dropped; ordinary winning excludes dead KK.

Clock/legality concern: each winning material-preserving edge is quiet by a
frozen theorem. No root-specific reset assumption. The budget's two-ply weak
tail forbids clock99 at every nonmate weak node. Full key congruence preserves
actual exact legal children and mate, including raw flags; no reflection or
unproved EP-none assertion substitutes for it. Ongoing/history admissibility
is reconstructed from nondeadness, nonempty replies and the actual thresholds.

Verdict: complete PAPER reduction argument for the selected route, with its
least-rank fixed-barrier step still unformalised. It is NOT the requested
compact evaluated outcome formula. The principal geometric evaluation and
matching lower bounds remain OPEN. No standalone framework/freeze is admitted.
