# S030 same-agent adversarial paper audit

The strategy transport above was checked against these failure modes before Lean:

- Arbitrary kernel reflection is false because castling is asymmetric. The
  source is required to have no castling rights. Extra strong choices in the
  target do not harm an existential strategy; weak replies have no rook to castle.
- A captured rook cannot be projected to a three-piece move. Safety must be
  derived at each weak winning source, then transported. A merely live position
  does not supply that safety. The adjacent unprotected capture gives a dead KK
  obstruction, not just failure of a proposed policy.
- No legal replies is not a universal-win case: transport preserves actual
  checkmate at terminal nodes and a witnessed reply at nonterminal weak nodes.
- Deadness is not assumed invariant. The existing choose/defend constructors
  derive nondeadness from the transported winning continuations.
- The induction decreases the source budget, even though target bounds are
  reassembled by finite branching and need not equal the source bound.
- Setup remains unproved: the axis chosen before a retreat may cease to have a
  gap of two. Same-rank rook/strong-king positions also block naive retreats.

Verdict: the restricted transport argument is sound subject to formal checks;
this audit does not approve arbitrary setup or full KRK outcome classification.

EC-C021 extension audit: the perpendicular switch uses post-reply separation,
not a preserved original gap. Outside-interval rook rank is essential to the
perpendicular safety margin. Source rank inequality excludes both blockers in
the horizontal retreat. Initial weak-rank rook placement must be excluded by
no incoming check. Same-rank strong king and rook, including near-file back-rank
cases, remain outside the off-rank statement. At most one retreat and one entry
prevents cycling. The first attempted append of this extension text used the
wrong working directory and failed; the clear-entry source was generated before
this text was saved. The argument above records the reasoning used to generate
it; the retreat formalisation follows this saved audit.

Same-rank completion audit: protected rook entry needs an explicit reply
witness; being protected alone does not exclude stalemate. The rank-zero
construction supplies that witness. The preparatory king move must occur
before giving the lone king a turn; post-reply separation proves it cannot
come down to rank one. No incoming rook check must be re-established on each
actual successor, not inherited from the old board. The completion still needs
formal validation of all these assertions before any general claim is made.

Flagship audit: canonical source distinctness and no-check facts must map,
not assume source has a legal predecessor. The geometric theorem therefore
uses no-check directly; legal arrival is only the final extraction corollary.
Weak-turn classification must keep zero-reply stalemate separate from mate,
and prohibit any KK reply, not merely require one winning reply. No global
reachable-from-initial premise is introduced or inferred.
