# EC-C046 — All-history admitted RAW KRK holding policies

S078, 2026-10-21. Classical bounded-game strategy argument, no novelty
claim. Sources are the existing actual RAW history layer, claim thresholds,
RuleMateWithin recurrence and EC-T0042 universal KRK termination. No tablebase,
engine oracle, exhaustive board enumeration, stored certificate or FIDE parity
claim. This argument concerns the actual chosen RAW model.

## Exact claim and missing KRK step

Fix a material colour sigma, either player c and an existing admitted history s.
Assume Region_sigma(s): exact KRK of sigma, or terminal. In particular every
admitted exact KRK root is covered, on either turn, with all actual flags and
the complete incoming trace, every clock and every repetition count.

A policy pi_c is a function from admitted histories to Option State. At each
ONGOING c-turn, None denotes a correct available claim; Some t denotes an actual
admitted BoardStep s t. Policy legality requires exactly that disjunction at
every ongoing c-turn. On other turns/terminal states its value is irrelevant.
State includes the entire history, so this is a history-dependent strategy,
even though it is a function of State. None is not a pass or resignation.
Available claims include current AND intended thresholds of the existing layer.

A policy-compliant finite board path retains EVERY legal step at opponent
turns. At c-turns it requires pi_c(s)=Some child. If pi_c(s)=None, play ends
immediately in a claim draw at that parent, with zero additional board plies.
Opponents may also choose any correct claim and end with a draw; those stopping
actions produce no further board path and cannot create a mate against c.
No terminal board moves are legal in this typed admitted action model.

RuleHold(c,s) means there EXISTS a LEGAL policy such that EVERY finite compliant
path from s, including its zero-length prefix, avoids Goal(c.opp) at its endpoint.
This is an independent strategy definition, not a complement by definition.

Prove RuleHold(c,s) iff NOT RuleForceMate(layer,c.opp,s). Also every such policy
path from Region has length at most fuel(s), maximal compliant board endpoints
are either raw terminal or an ongoing c-turn at which pi=None is a correct claim,
and a stopped compliant continuation exists within the same board-ply horizon.
Thus no infinite uncompleted board play is being used as a holding loophole.

Blocked step: EC-T0042 gives an all-branch finite horizon but no defensive
selection. Existing sufficient winning families and key-simple strategies
do not cover arbitrary incoming counts. Smallest missing lemma is saturation:
any actual finite rule-mate certificate at a Region node has a certificate
within that node's fuel. This makes the child winning budgets uniform and
unlocks defensive choice. Exit immediately into policy legality/safety/converse;
do not call this a geometric KRK outcome formula or full class closure.

## 1. Monotonicity and saturation

Write W_a(n,s) for the FROZEN RuleMateWithin(layer,a,n,s), F_a(s) for existence
of such n, and P(s) for frozen fuel. Goal(a,s) implies W_a(n,s) for all n:
at zero use Goal, and at a successor take its immediate-goal disjunct.
Induction on n gives W_a(n,s) -> W_a(n+1,s): in a non-goal branch use the
induction hypothesis at all child certificates, keeping the identical ongoing,
turn, nonempty and no-claim guards. Iteration gives monotonicity n<=m.

Saturation: for every Region node s and every n, W_a(n,s) implies W_a(P(s),s).
Use strong induction on P(s), with arbitrary certificate budget n and state s.
If the certificate takes Goal, use Goal at P(s). Otherwise its ongoing branch
has an admitted child: chosen witness on a-turn, retained nonempty witness on
a.opp-turn. Every child has Region and P(child)+1<=P(s) by EC-T0042, so P(s)>0.
Write P(s)=k+1. At each certified child, strong induction gives a certificate
within P(child)<=k; monotonicity raises it to k. Rebuild the EXACT existing
recurrence at k+1 with its original turn/claim/nonempty conditions. At P(s)=0
an ongoing nonempty branch contradicts the strict fuel inequality. No child
is removed because it draws, and no finiteness enumeration is involved.

Consequently F_a(s) iff W_a(P(s),s) on Region. This is a bounded-certificate
equivalence, not an independently useful board/history outcome characterisation.

## 2. Defensive local choice and all-opponent preservation

Let a=c.opp and assume Region(s) and NOT F_a(s). Then NOT Goal(a,s), since Goal
itself is a zero certificate.

At an ongoing a-turn, EVERY admitted child t also fails F_a. Otherwise its
finite certificate at n would give W_a(n+1,s) by the winner-choice branch,
contradicting NOT F_a(s). All children retain Region by EC-T0042. Opponent
claims may end earlier in a draw and need no child invariant.

At an ongoing c-turn, if CanClaim(s), choose None. If NOT CanClaim(s), there
exists an admitted child t with NOT F_a(t). Suppose contrariwise every child
has F_a. Ongoing supplies a legal reply and full lifting supplies a typed child.
Set P(s)=k+1 using strict fuel descent. Saturation and P(t)<=k put EVERY child
within budget k. The defender-all-replies branch of the frozen recurrence,
with c=a.opp, no claim and nonempty replies, now gives W_a(k+1,s), contradiction.
Therefore choose an actual non-winning child; its Region follows from descent.

This proof does not infer draw from failure of a sufficient clock/histogram
certificate. It uses failure of the FULL opponent forcing predicate and proves
an actual defensive strategy for that complement.

## 3. Global legal policy and invariant

Use classical choice at every admitted state, never a stored per-position table.
At an ongoing c-turn with CanClaim, choose None. Without a claim, if Region and
NOT F_a hold, choose a child supplied by section2. At any remaining ongoing
c-turn choose an arbitrary actual child supplied by full reply lifting. On all
irrelevant states choose None. This produces a globally legal policy; no legality
requirement is imposed on terminal/opponent-turn values.

Induct over every finite policy path rooted at the given safe Region node.
Zero retains the same state and section2 excludes opponent Goal. For a step,
Region is preserved universally. On an opponent turn section2 covers EVERY
actual legal child. On a c-turn compliance requires Some child; the constructed
policy's safe-choice property gives NOT F_a at that child. Continue induction.
No claim creates a child, and each allowed claim draws. Every reachable prefix
therefore avoids the opponent's actual mate. This establishes RuleHold.

## 4. Converse: any holding policy excludes every finite opponent certificate

Fix ANY globally legal c-policy with all compliant prefixes safe. Induct on a
putative certificate W_a(n,s), retaining the same global policy and root safety.
If Goal(a,s), the zero path contradicts safety. In the non-goal branch:

* On a-turn, the certificate's selected legal child is compliant because c
  does not control that turn. Prefixing this step shows all compliant paths
  from the child are safe. Apply induction to its certified smaller budget.
* On c-turn, the certificate asserts NO CanClaim. Policy legality therefore
  excludes None and supplies Some actual child. Its move is compliant and
  the universal certificate covers it. Prefixing transfers safety; induction
  contradicts that child's certificate.

No finite certificate can coexist with the holding policy. Existentially
quantify n for NOT F_a(s). This converse does not need Region; the forward
direction needs its uniform finite horizon. Together they prove the exact iff.

## 5. Real stopped outcomes and board-ply horizon

Forget the policy constraint in any compliant path; it is precisely a frozen
typed Path. EC-T0042 gives endpoint Region and P(end)+length<=P(root).
An infinite board play would have prefixes longer than P(root), impossible.

At a maximal compliant endpoint t, if raw terminal it has already stopped.
Otherwise it is ongoing and has legal children. If opponent turn, any actual
child is compliant, contradicting maximality. If c-turn and pi=Some u, legality
gives a compliant successor, also contradicting maximality. Thus c-turn and
pi=None, and policy legality gives CanClaim: execute the correct zero-ply draw
claim. Conversely terminal or c-turn/None excludes compliant successors.
Opponent claims also legitimately stop at any earlier ongoing opponent node.

A stopped compliant continuation exists by strong induction on P: stop at raw
terminal or own chosen claim; otherwise choose the policy's actual child on own
turn or any legal child on opponent turn, decrease P, and prepend the step.
It has at most P(root) board plies. Any such stopped continuation from a holding
root avoids opponent mate; it may draw or win for the holder. No assertion that
every terminal is draw is made; mate at150 remains actual mate-first.

## Scope and next obligation

This directly discharges the missing strategy/complement relationship for all
admitted RAW KRK histories and their terminal region. It does not decide the
predicate by a geometric formula, furnish full FIDE repetition/rights/claim
correspondence, prove numeric optimal distances, identify exact five-valued WDL
or DTZ, or close KRK. The policy is classical/noncomputable, not a tablebase.
After proof/audit/formal verification return to necessary-and-sufficient
KRK history/geometry outcomes, actual rules correspondence and distance
optimality. A generic theorem's existence is not class closure.
