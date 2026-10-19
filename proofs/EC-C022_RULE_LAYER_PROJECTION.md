# EC-C022 — same-budget projection from an abstract rule layer

S033. Classical finite reachability-game simulation; no novelty claim.
Sources: frozen EC-T0008 (`Rules/ForcingDefinitions.lean`, `ForceMate.lean`),
the S032 rule/history specification §5, and its retained design audit. No engine,
tablebase, graph enumeration or per-position certificates enter this argument.

## Exact definitions and hypotheses

Let X be any type, e:X→Position an erasure, B:X→X→Prop the actual-board-move
relation, O:X→Prop an ongoing predicate, and C:X→Prop claim availability.
These data are independent of the named winner σ and ply budget n. At EVERY
ongoing state s assume ordinary interface proofs:

(A) For every t, B(s,t) implies Legal(e(s),e(t)).
(B) For EVERY kernel successor r, Legal(e(s),r) implies existence of t with
    B(s,t) and e(t)=r.
(C) O(s) implies NOT DeadK(e(s)).

The proof fields quantify over all states; they are not additional Lean axioms
and do not assume that any successor wins. No hypothesis restricts B to children
which remain ongoing. In particular, draw-ending replies may NOT be removed.
No KRK, legal-arrival, reachability, finite-X, numerical clock or repetition
hypothesis is needed by this abstract implication.

Define Gσ(s)=MateGoal σ (e(s)), the EXACT frozen named-colour board-mate goal.
Define Rσ(0,s)=Gσ(s), and

```
Rσ(n+1,s) := Gσ(s) OR
 (O(s) AND
   (((e(s)).turn=σ AND ∃t, B(s,t) AND Rσ(n,t)) OR
    ((e(s)).turn=σ.opp AND NOT C(s) AND
      (∃t, B(s,t)) AND ∀t, B(s,t) → Rσ(n,t))))
```

RuleForceMate σ s means ∃n, Rσ(n,s). R measures BOARD plies; a successful
correct claim ends in draw, not a move in B. The winner may decline its claim;
the defender's available claim prevents a recursive winning branch. Nonempty
board replies prevent vacuous stalemate wins. A later concrete automatic draw
must have O false and Gσ false. This document does not implement that concrete
history classifier or certify its agreement with the FIDE clauses.

Frozen MateWithin has the same terminal/turn/existential/universal structure,
with Legal moves and NOT DeadK in place of B and O, and no claim guard.

## Theorem 1 — finite-budget projection

For all types X, all e,B,O,C and proofs A–C, both colours σ, all n∈N and s∈X,

`Rσ(n,s) → MateWithin σ n (e(s))`.

Proof by induction on n, universally quantifying s at each induction step.

Base n=0: the premise is exactly Gσ(s), hence exactly the frozen MateGoal.
This proves MateWithin σ 0 (e(s)). Zero-ply actual mate is not delayed by claims.

Successor n+1: if Gσ(s) holds, use the terminal disjunct of frozen MateWithin.
Otherwise the premise supplies O(s) and one of two recursive alternatives.
Hypothesis C supplies NOT DeadK(e(s)).

- Winner turn: choose t with B(s,t) and Rσ(n,t). A projects that move to
  Legal(e(s),e(t)); induction gives MateWithin σ n (e(t)). The turn equality
  is already the required frozen equality. Assemble the strong branch at n+1.
- Defender turn: the premise includes NOT C(s), a B-successor witness t0 and
  Rσ(n,t) for EVERY B-successor. A projects t0, proving frozen reply
  nonemptiness. Now fix an ARBITRARY raw Legal(e(s),r). B supplies a lifted t
  with B(s,t) and e(t)=r. The universal premise supplies Rσ(n,t); induction
  gives MateWithin σ n (e(t)), then equality substitution gives the desired
  MateWithin σ n r. Thus EVERY raw kernel reply is covered. Retain the turn
  equality and assemble the frozen weak branch. Dropping the no-claim guard
  is valid only in this projection direction.

Each recursive use decreases n by one, regardless of whether the child is
ongoing. All other branches are terminal. The SAME n is retained; no
finite-branching maximum, new rank or reachability-only weakening is used. QED.

## Theorem 2 — forcing projection

For all the same layer data, σ and s,
`RuleForceMate σ s → ForceMate σ (e(s))`.

Choose the premise's witness n, apply Theorem 1, and use that identical n as
the frozen ForceMate witness. QED. No choice of n depending on an opponent's
reply is introduced; a uniform bound is supplied by the premise.

## Nonvacuity and semantic boundary

The interface has an elementary mathematical instance: X=Position, e=id,
B=Legal, O(q)=NOT DeadK q, C(q)=False. A and B are the identity legal-move
proofs and C is O itself; hence the interface is consistent without assuming
any particular winning state. This artificial no-claim layer mirrors the
clock-free recurrence. It is NOT a FIDE history implementation, is not a new
chess outcome claim, and need not expand this session into an extra test suite.

The theorem is a conditional interface theorem, not a proof that arbitrary
history erasure preserves a winning strategy. Future concrete use must prove
A–C for its actual states and interpret O, C and G correctly. No converse is
claimed: a defender's current/intended draw claim may destroy a clock-free win.
Neither a numerical KRK bound nor repetition safety follows from finite rank.
No holding/determinacy, history compression, exact DTM/DTZ, full FIDE WDL,
Syzygy convention or initial-position claim follows from these two implications.
