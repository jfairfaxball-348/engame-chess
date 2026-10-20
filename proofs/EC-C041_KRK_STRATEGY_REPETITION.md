# EC-C041 — Key-simple finite-rank KRK strategy

2026-10-20, S070. Classical finite-attractor/rank argument, no novelty claim.
Sources: frozen clock-free MateWithin/ForceMate (EC-T0008), normalized raw-key
legal congruence (EC-T0030), and numerical KRK bound (EC-T0037). Paper and separate
same-agent audit precede Lean. No engine, tablebase, class enumeration, stored
position certificate or computed optimal-distance table is involved.

## Admission against the direct KRK target

1. Blocked milestone B step: the winning KRK strategy must control repetition
   on its chosen strong moves and ALL legal defending branches, including all
   legal intended-move children at weak nodes.
2. The frozen 508-ply bound proves termination, not uniqueness of normalized
   keys. Phase labels are not in the key, and EC-C039 assumes every raw path,
   including unchosen strong moves. The known raw chase cycle rules out using
   such an assumption as a general strategy certificate.
3. The smallest needed interface is same-budget MateWithin invariance under
   equal raw keys. This makes the least mate budget equal on equal keys. A
   least-budget winning strategy then has strictly decreasing rank on every
   retained edge, yielding pairwise distinct keys on every finite play line.
   Applying EC-T0037 supplies a root rank at most 508 and play lines at most
   508 plies. This is a concrete KRK strategy payoff, not unrelated bookkeeping.
4. Exit criterion: once this certificate is verified, return to actual stored
   raw traces, incoming-history occurrence counts and rule-layer lifting. Do
   not infer full FIDE key correctness or install another generic lemma series.

## Exact definitions and principal claim

Fix winner colour σ. Write MW(N,q)=MateWithin σ N q and Win(q)=ForceMate σ q.
The existing noncomputable raw key K(q)=RawRepetition.key q is the full position
with its ep field replaced by the legality-filtered effective ep target. This
paper claims only properties of THAT key and kernel; no full FIDE iff is assumed.

Define d(q) to be the least N with MW(N,q), if Win(q); set d(q)=0 otherwise.
A least natural witness exists by well-ordering, and is unique as a number.
The default zero for nonwinning positions is a total-function convention only,
never a statement that they are mated. Every policy vertex is explicitly winning.
No executable evaluator or position lookup table is constructed.

A policy edge q→r means Legal q r, Win(q), Win(r), and d(r)<d(q). A policy line
is a nonempty finite list [q0,...,qk] of winning positions with a policy edge at
every adjacent pair; a singleton winning position is permitted. Legal is the
actual kernel relation, with its actual move and full endpoint witnesses.

For EVERY exact strong-turn KRK legal arrival q (either strong colour, arbitrary
flags), the following holds:

- Win(q), MW(508,q), and d(q)≤508.
- At every winning nonmate strong node a policy edge exists. At every winning
  nonmate weak node the legal reply set is NONEMPTY and EVERY legal reply is a
  policy edge. No weak move is filtered by its outcome or by child ongoingness.
- Every finite policy line starting at q has pairwise distinct K keys and at
  most 509 vertices, i.e. at most 508 board plies. Every vertex remains winning.
  More generally any policy line has at most d(first)+1 vertices.
- A winning node with no policy edge is actual named opponent mate. A mate has
  rank zero and no policy edge. Thus a maximal policy play terminates in named
  mate, not stalemate, wrong-colour mate, capture-to-KK or an invented pass.

This chooses a new least-budget strategy within the frozen clock-free attractor.
It does NOT assert that every raw line, every winning move, or the concrete frozen
geometric policy is key-simple. A policy is permissive among decreasing strong
moves; choosing any such move is safe. Defender edges retain all legal moves.

## 1. Equal-key root interface

If K(q)=K(r), their boards and turns agree, since normalization changes only ep.
Their castling rights also agree; arbitrary raw ep values need not agree.
The frozen key_legal_congr theorem gives for EVERY actual move m equal Boolean
legality, and identical FULL played endpoints whenever m is legal. Hence for
EVERY Position z, Legal q z iff Legal r z: reuse the same actual move, legality
and full endpoint equality. This is not merely equality of successor keys.

Check depends only on board and queried colour. Therefore inCheck q c equals
inCheck r c for every colour c. Combining equal turn, check and exact legal
successor sets gives MateGoal σ q iff MateGoal σ r. Nonempty replies and absence
of replies are preserved, including root mate and stalemate.

## 2. Equal-key same-budget invariance

For every N, MW(N,q) iff MW(N,r). Symmetry reduces to the forward direction.
At N=0 use the goal correspondence. At N=n+1, an early goal maps likewise.
Otherwise use the fixed-budget recurrence. The chosen strong child is an
IDENTICAL Position legal from r; its given MW(n,child) is unchanged. Root turn
is preserved. The strong fixed-budget constructor supplies MW(n+1,r).
At a weak node reuse a common legal witness for nonemptiness and send EVERY
legal r-child back to the identical q-child, retaining its MW(n,child) premise.
The fixed-budget defending constructor supplies MW(n+1,r).

Nondeadness of r must not be assumed from its key. Those constructors prove it
from a common legal child with a finite path to named mate. Thus no unproved
DeadK congruence or global kernel/FIDE isomorphism is used. In fact no recursive
induction is necessary, since the immediate full endpoints are identical.
Existentially quantifying N also gives Win(q) iff Win(r).

## 3. Least-budget specification and key invariance

For Win(q), MW(d(q),q); and for ANY N with MW(N,q), d(q)≤N. A root goal has
MW(0,q), hence d(q)=0. Conversely if Win(q) and d(q)=0, its specification is
MW(0,q)=MateGoal σ q. The Win premise is essential because of the total default.

Equal keys preserve Win and all MW budgets by §2, so their least winning budgets
are equal by two applications of minimality. If neither is winning, both use the
specified default zero. Thus d is equal on equal keys over all raw positions,
without identifying ineffective raw ep fields or inventing new legality.

## 4. Strict descent and complete defensive branching

At Win(q) with no MateGoal, d(q)>0. Write d(q)=n+1 and invert its exact MW
certificate. The goal branch is impossible. If q.turn=σ, the defending-turn
branch contradicts colour opposition; the strong branch supplies an actual
legal child with MW(n,child). The child is winning and its least rank is at
most n, strictly below d(q). Thus a policy edge exists.

If q.turn=σ.opp, the strong branch contradicts opposition. The defending branch
supplies nonempty legal replies and MW(n,child) for EVERY legal child. Each is
winning with rank at most n. Consequently EVERY legal reply is a policy edge,
including any legal move a defender could announce for a claim. No favourable
reply is chosen. A legal capture to dead KK cannot be among these winning children,
as already implied by the frozen forcing obstruction. No new capture exclusion
is silently imposed on Legal.

Every colour is either σ or its opponent. Therefore a winning nonmate node
cannot lack policy edges. Actual named mate has rank zero and so no smaller
natural rank. With the converse in §3 this proves the stated terminal endpoint
characterization, with the winning-node premise retained.

## 5. Full-line nonrepetition and length

Induct on a policy line. In a singleton there are no later vertices, keys are
pairwise distinct, and length 1≤d(first)+1. For a line headed by q→r, every
later vertex is winning and has rank below d(q): r by the edge; subsequent
vertices by the induction hypothesis and transitivity through d(r)<d(q).
If its key equalled K(q), §3 would make its rank d(q), a contradiction. The
tail keys are pairwise distinct by induction. This proves PAIRWISE key inequality
for all distinct indices, not merely adjacent inequality or endpoint inequality.

The tail has length at most d(r)+1; adding q gives total length at most
d(r)+2≤d(q)+1. Thus an infinite policy play cannot exist: arbitrarily long finite
prefixes would contradict this natural bound. If a finite play is maximal,
§4 says its last winning vertex is actual named mate. The theorem does not treat
an arbitrarily truncated prefix as already mated.

Finally EC-T0037 gives MW(508,q) for every stated KRK arrival, so d(q)≤508 by
minimality. Substitution in the line theorem gives at most 509 vertices/508 plies.
Both colours and all kernel flags are included without a symmetry assumption.
This preserves every defending branch of the NEW rank strategy.

## 6. Actual history and remaining gaps

Pairwise new-line keys do not exclude repetitions against the incoming stored
history. A future policy key might already have occurred twice before this
strategy starts; one new occurrence can enable a draw claim. S070 does not
supply a bound for those old counts, does not truncate history after a reset,
and does not substitute current-old-key counts for prospective-new-key counts.
The next direct step must combine this policy with actual RawTrace append and
the incoming full-history histogram, including every weak intended child.

The 508 ceiling exceeds 100; no strict clock+n<100 family is asserted using that
ceiling. A smaller variable least budget with explicit clock/history conditions
could support a narrower sufficient family, but its lifting is still to prove.
No complete history-aware KRK outcome, holding theorem, exact FIDE/Syzygy WDL/DTZ
convention or class closure follows. Failure of a sufficient certificate gives
no draw theorem. Although the rank is defined by least clock-free budget, no
numerical evaluation or external distance-parity claim is made.

Status at paper creation: LOCAL_VERIFIED after separate same-agent adversarial
audit; Lean/Gate F and separate Gate Z pending. The theorem ledger remains at
37 frozen bundles. Mathematical input coverage for rule-aware wins is unchanged.

S070 verification addendum: exact paper statements FORMAL_VERIFIED at `fe7efa687ae1481db405cf8808d9ad3437906861`; [observed evidence](../sessions/evidence/S070/README.md). Separate Gate Z remains pending. Earlier paper-creation status is historical.
