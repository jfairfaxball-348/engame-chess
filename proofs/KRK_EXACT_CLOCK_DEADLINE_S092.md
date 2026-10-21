# S092 necessary time component of the full KRK outcome criterion

2026-10-21. EC-C053, working dependency of the positive-clock/history route.
LOCAL_VERIFIED paper; local Lean checks passed; no own-source F/Z or freeze.
No class-completion claim. Classical optional-
claim logic, not a novelty claim. No engine, tablebase or enumeration.

For EVERY admitted RAW state s with exact KRK material of strong colour sigma,
let h be its actual trace clock. Define

    B(s) = max(1,100-h) if strong turn; 100-h otherwise.

Natural subtraction is intended. Any actual mate-winning certificate W(n,s)
can be replaced by W(B(s),s), on the SAME incoming history with every opponent
board move and current/intended claim retained. Consequently actual winning
implies clock-free MateWithin(B(s),erase(s)). Neither converse is asserted.

This supplies the exact clock threshold needed before deriving geometric draw
regions. The generic150-h termination horizon does not supply it, and the
strict<100 sufficient lift cannot be used as a necessary distance condition.
It is not a compact outcome formula by itself and will not be frozen alone
as a substitute for the selected full-domain criterion.

## Proof, all turns/histories and endpoints

Induct on the given certificate n. A root already at the named mate has W0,
so monotonicity gives every target budget including B=0. A non-goal certificate
has an ongoing root and its actual chosen/defended rule branch.

Every winning child remains KRK and has clock EXACTLY h+1: frozen
winning_child_quiet excludes captures to dead KK by winning projection.
The actual legal step flips turn. These facts retain all flags/claims/history.

Strong root: choose the same certified child. If it is already mate, this is
an actual one-ply win, and B>=1 at ANY h. This covers mate at clock100 or150
and does not grant the weak side an extra claim turn after mate. Otherwise
the weak child is ongoing and winning. The frozen weak h>=99 nonforcing
theorem forces its clock<=98, hence parent h<=97. Its inductively shortened
budget is100-(h+1)=99-h; adding the chosen move gives100-h=B(s). No strong
optional claim is forbidden; the same chosen board move is used.

Weak root: retain the original no-claim fact and NONEMPTY reply set. A winning
ongoing weak root must have h<=98 by the same frozen theorem (at h>=99 a
winning nonzeroing child would provide an intended fifty-move claim). For
EVERY actual reply, winning_child_quiet gives strong KRK at clock h+1. Its
inductive budget is max(1,100-(h+1))=99-h, because h<=98. Add the defending
move to obtain100-h=B(s). ALL replies and original no-claim evidence remain.

The induction is on the supplied certificate, not a board enumeration or an
assumed optimal policy. It neither computes an outcome nor erases repetitions.
For an actual winning policy, the frozen policy/certificate equivalence gives
such an n. The frozen same-budget projection then gives the necessary geometric
MateWithin bound on the erased board. Forcing/dead/terminal assumptions have
not been replaced with a weaker move game.

## Use and remaining direct obstacle

The time component in a proposed full criterion must permit the equality
h+distance=100 when appropriate and the high-clock immediate-mate exception.
To declare a remaining region drawn on time grounds, prove that EVERY strong
choice exceeds B; a lower bound for our nonoptimal wall policy is insufficient.
Conversely a clock-free bound<=B does not control old repeated keys. The
incoming-barrier / geometric-cost criterion and full FIDE correspondence are
still OPEN. Return immediately to that comparison; do not expand this step
into a generic claim framework or further unadmitted foundations.
