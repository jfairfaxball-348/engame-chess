# S092 all-history reduction to fixed incoming-key barriers

2026-10-21. PAPER argument, working component of the direct full-domain route.
NOT an evaluated geometric outcome formula, NOT Gate F/frozen, NOT KRK closure.
No tablebase, engine, class enumeration or per-position values. This argument
removes the evolving history from the remaining geometric problem; it does
not solve that geometric problem by renaming a recurrence.

Fix an admitted exact KRK root s, strong colour sigma, board q, clock h and
the ENTIRE original trace H (including q). Let c_H(k) count original positions
with normalized RAW key k. Use the existing RAW key, not a new FIDE claim.
Let B(s) be the exact turn-dependent budget from the companion deadline proof.

Define C_H(n,q) by existence of a finite CLOCK-FREE chess mate-strategy tree
of height<=n: choose one actual legal move at strong nodes, retain EVERY legal
move at weak nodes with a nonempty reply set, and end at named board mate.
Every NONROOT, NONMATE vertex v must have c_H(key(v))<2. The root is exempt
from this barrier. No claim, clock or evolving count occurs in this board tree.
This is an intermediate fixed-barrier geometric problem, NOT the requested
compact outcome criterion or permission to solve it by exhaustive enumeration.

The proposed full reduction is

    ActualWin_sigma(s) iff
      Goal_sigma(q) OR
      [Ongoing(s) AND (strongTurn(q) OR c_H(key(q))<3)
       AND C_H(B(s),q)].

All incoming histories, turns, terminal states and actual claim branches are
retained by this equivalence. The remaining principal gap is to EVALUATE the
fixed-barrier geometric condition by a compact explicit formula with matching
defender lower bounds. No converse from ordinary clock-free distance is claimed.

## Necessity

An actual winning policy has a frozen RAW certificate. The companion exact
deadline argument shortens it on the SAME incoming history to B(s). A nonmate
root is ongoing; a weak root has no current claim, giving root count<3.

Erase this finite winning tree. Every winning child remains exact KRK and
is a nonzeroing actual legal move, by frozen winning_child_quiet. Future
nonmate vertices cannot cross the stated fixed barrier:

* If a nonroot weak vertex has original count>=2, its new occurrence makes
  the full count>=3, so its current repetition claim contradicts winning.
* If a nonroot strong vertex has original count>=2, its WEAK parent could
  announce that exact actual legal move as an intended repetition claim.
  The parent no-claim condition is contradicted even if the child would draw.
* A named mate is accepted immediately. No post-mate claim turn is inserted.

Each branch retains all actual defender replies. Finiteness of the tree uses
only finite move branching (finite source/destination/promotion choices), not
enumeration of an endgame class. Hence C_H(B,q). This direction needs no
cycle-removal lemma or assumed history-independent winning policy.

## Sufficiency: first obtain a key-simple FIXED-barrier policy

Let A_H be the same board objective with the barrier ALSO imposed at its root
unless the root is mate. Barrier membership and mate depend only on the RAW
key. The frozen strategy_key_interface gives equal turns, checks, exact legal
children and mate for equal keys; it is not merely a board symmetry claim.
Therefore A_H's least sufficient ply budget is key-invariant. At a strong
winning node choose a least-budget child; at a weak node retain EVERY legal
child. Every nonterminal edge strictly decreases that least budget. Equal
keys would have equal budgets, so no key repeats on any such policy line.
The policy stays within the supplied height bound, not an unbounded new search.

This is the standard least-rank argument applied to this SPECIFIC fixed-barrier
objective. It has not yet been formalised. No generic forbidden-game library
is admitted, and this paragraph is not an evaluated geometric formula.

If the original root is allowed, C_H is exactly the A_H objective at the root,
so use its key-simple policy from there. If the root is forbidden, it is
nonmate and c_H(key(q))>=2. Keep its chosen move or all its defending moves,
then use A_H's key-simple policy from each child. A future nonmate root-key
repeat is impossible because it is forbidden. A future mate with that key is
also impossible: key-invariance of mate would make the original root mate.
Thus the FULL line including its exempt root is key-simple in both cases.
The original root exception is essential for a strong player declining its
own optional repetition claim; do not simply ban every root in the barrier.

## Lift that policy to the SAME actual incoming history

Each future nonmate key occurs at most once along the line and has original
count<=1, so its total occurrence count is<=2. The original root may have more
occurrences: Ongoing excludes automatic draw, a weak root additionally has
count<3, and a strong root may decline its own claim. No future root-key repeat
occurs. At weak nodes, EVERY legal intended child is in the retained policy
tree, has a new allowed key and total count<=2. Weak children have strong turn,
so none can be a named mate exception. Thus current AND intended repetition
claims are unavailable to every defending weak node. No historical count is
pruned, compressed or silently reset.

For the ordinary case B=100-h, a nonmate weak node at depth k must have at
least TWO plies remaining to a leaf: turns alternate, every mate leaf is weak
to move, and a nonempty weak reply must first reach a strong node. Hence
k+2<=B, h+k<=98 and its prospective nonzeroing child clock<=99. There is no
current or intended fifty-move claim. All nonmate future nodes have clock<100,
so automatic75-move draws cannot intervene either. For a strong root with
B=1 (the high-clock exception), the only possible strategy is immediate mate;
Ongoing at the root and mate precedence at its child suffice, even if the
mating move reaches150. A weak root with B<=1 cannot have a nonmate tree;
the same two-ply observation excludes the apparent boundary cases.

Erasing barriers gives an ordinary clock-free mate tree, so each nonmate
vertex is nondead with a real legal continuation. Together with the clock/
count facts this proves ongoingness at every needed prefix. Append actual
moves to the original admitted trace using frozen reply completeness. The
terminal goal is actual board mate. All weak moves and claims have been
handled; the frozen certificate/policy bridge gives ActualWin.

## Remaining exact gap and return criterion

The reduction has NOT evaluated C_H. An unrestricted clock-free bound<=B is
only necessary, not sufficient: it can enter a key with original count>=2.
Nor does failure of the wall93 policy prove a lower bound for C_H. Need a
compact analytic characterisation of these fixed-barrier regions and matching
lower bounds against every legal strong move. Full FIDE correspondence of the
RAW key/claim model and exact global distance/WDL-DTZ remain separately OPEN.
Formalise no new framework solely to report this reduction as material closure.
