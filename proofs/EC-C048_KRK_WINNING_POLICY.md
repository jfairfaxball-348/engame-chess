# EC-C048 — Actual winning policies for every admitted RAW KRK history

S082,2026-10-21. LOCAL_VERIFIED after the separate pre-Lean paper audit.
Classical finite game strategy
argument, no novelty claim. Existing admitted RAW layer, full rule recurrence,
actual total legal policies, compliant paths and universal KRK fuel are the
only ingredients. No tablebase, engine, board enumeration or stored certificates.

## Exact independent strategy definition

Fix named player c, actual admitted State s, and a total Policy pi:State->Option
State. LegalPolicy and PolicyPath are EXACTLY the frozen actual policy/board
path definitions, retaining every opponent move. Define WinningSafety(c,pi,s):
for EVERY compliant finite path of length n from s to t,

* if t is not ongoing, then t is already Goal(c), actual opponent checkmate;
* if t is ongoing and c to move, pi(t) is Some child (never a chosen draw claim);
* if t is ongoing and c.opp to move, there is NO available correct current OR
  intended claim. The opponent's claim action cannot be pruned or ignored.

Define ActualWin(c,s) independently as existence of pi and a natural B such
that pi is globally legal, WinningSafety holds, and EVERY compliant board path
from s has length<=B. B counts board plies; a correct claim would stop at zero
additional board plies and is excluded exactly as above. A terminal root named
mate has B=0. A terminal draw/opposite mate fails WinningSafety on the zero path.
The explicit finite cap prevents an infinite-policy cycle making the terminal
condition vacuously true. This is not RuleMateWithin renamed as a definition.

Claim: for every admitted exact KRK root of either material colour, either named
winner, both turns/all actual flags/incoming trace/clock/counts, ActualWin(c,s)
iff the EXISTING full RuleForceMate(c,s). More generally forward construction
works on frozen KRK-or-terminal Region. Extract the forward policy with cap
fuel(s). Conversely ANY independently defined globally legal bounded winning
policy of horizon B gives the exact existing RuleMateWithin(c,B,s), with no
KRK premise needed for this converse. Prove actual terminal continuation and
mate within fuel for such a policy from Region.

Exact missing KRK step: holding/nonforcing duality does not assert that a
positive finite certificate is an actual winning history policy. A naive policy
which always chooses SOME F-child could cycle on an unrestricted graph; the
concrete KRK fuel is the smallest existing fact which rules this out here.
Exit after the strategy equivalence and actual mate endpoint proof, returning
directly to remaining low-clock/history geometry and exact distances. This
bridge alone does not decide those inputs or close KRK.

## 1. Exact action structure of a finite certificate

At any ongoing state no Goal is possible, because the ongoing guard supplies
a legal reply whereas actual mate has none. Invert ANY full F certificate.
At c-turn its non-goal recurrence branch chooses an actual admitted child t
with F(c,t). At c.opp-turn it forbids CanClaim and covers EVERY actual board
child with F(c,child), preserving nonemptiness. Wrong turn branches contradict
the opposite-colour identity. No child is discarded for ending in draw; instead
such a child refutes the claimed certificate. At a terminal, F iff actual Goal
by the existing terminal inversion theorem.

## 2. A globally legal certificate-preserving winner policy

Use classical choice at each full history. At an ongoing c-turn satisfying F,
choose Some actual F-child from section1, even if c could claim a draw. At an
ongoing c-turn outside F choose an arbitrary legal child from full reply
lifting. At irrelevant opponent/terminal nodes choose None. No off-branch
illegal action remains. The constructed policy is globally legal and never
chooses None at its own ongoing F-node. Every selected board child of an
ongoing F-node also satisfies F.

Induct along all compliant prefixes from an F-root. Own steps use its chosen
Some child; opponent steps use ALL-child closure of section1. Therefore F
holds at every prefix, every opponent ongoing claim is impossible, own ongoing
None is impossible, and every terminal prefix is already named Goal. This
establishes WinningSafety. It does not, by itself, forbid infinite play.

From a KRK-or-terminal Region root, erase the policy condition and use the
frozen all-board-path bound fuel(end)+n<=fuel(root). This gives the missing
uniform finite horizon B=fuel(root), for ALL compliant paths. No rank-decreasing
claim is made for the arbitrary F-child policy outside Region. Now the actual
policy meets every clause of ActualWin, including termination.

## 3. Converse extracts the original exact B-ply certificate

Fix ANY globally legal policy with WinningSafety and horizon B. Induct on B,
with arbitrary current root s and inherited global policy.

If root is terminal, WinningSafety at its zero path gives Goal; at every B
this is already W(c,B,s). Otherwise root is ongoing.

On c-turn, WinningSafety at the zero path excludes None. Split the actual
Option value and obtain Some t; global legality supplies the actual edge.
On c.opp-turn, WinningSafety forbids claims and ongoing supplies a legal child.
EVERY board child there is compliant, because c does not control this turn.
Thus both cases have a compliant child; if B=0 the one-step path violates the
horizon. Write B=k+1.

For a compliant edge s->t, transfer WinningSafety by prefixing it to EVERY
compliant child path. The root horizon gives n+1<=k+1 for each child path,
hence n<=k: same global policy wins at that child with horizon k. Own turn
uses induction for its selected child. Opponent turn applies induction to
EVERY actual child, retaining the original nonempty witness and no-claim guard.
Rebuild the EXACT frozen W(c,k+1,s) recurrence. This proves the same B budget,
not an existential abstraction or unproved finite-game slogan. No maximum
over enumerated boards or move lists is needed; the policy's uniform horizon
already bounds all children.

Existentially quantify B to obtain F. Combine with section2 on Region for the
claimed iff. For any named player at an exact KRK root, terminal and all-history
input coverage is explicit; no rule correspondence is assumed.

## 4. Genuine maximal outcomes and existence

Take ANY legal WinningSafety policy from a Region root. Frozen stopped-policy
continuation supplies an actual compliant path within fuel(root) ending raw
terminal or at an own selected correct claim. Its own-claim alternative
contradicts WinningSafety's own ongoing Some condition. Hence endpoint is raw
terminal and WinningSafety makes it Goal(c), not merely terminal fuel0.
All maximal compliant paths have the same property via the frozen maximal/
stopped iff; no arbitrary short prefix is falsely called complete. Opponent
claims at any prefix are explicitly impossible by WinningSafety. Infinite
board play is excluded by the existing fuel bound (or the ActualWin horizon).

Thus every actual complete action play against the policy ends in named mate;
successful claims are neither delayed turns nor omitted adversarial options.
At a zero-length terminal mate root, the stated endpoint is itself. A terminal
draw cannot satisfy the winning policy. Mate at clock150 remains mate-first.

## Boundary

This directly proves actual strategy soundness/completeness of the chosen RAW
finite forcing semantics on ALL admitted KRK histories, and preserves exact B
in the policy-to-certificate direction. It is not an evaluated low-clock
geometric outcome formula, full FIDE key/rights/claim/adjudication correspondence,
global numeric DTM or Syzygy WDL/DTZ parity. Those remain required for KRK closure.
