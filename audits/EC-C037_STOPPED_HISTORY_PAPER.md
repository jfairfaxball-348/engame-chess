# EC-C037 — Separate adversarial paper audit

S062, 2026-10-20, completed before Lean. Same-agent review, not independent
external audit. LOCAL_VERIFIED relative to the chosen raw classifier.

Attempted falsifications and outcomes:

- Zero length: start is True, not an unjustified initial ongoing theorem. The
  first move still requires the actual parent classifier ongoing.
- Terminal parent versus terminal child: snoc tests the parent ONLY. A mate,
  stalemate, dead or numeric-draw child is admitted; a terminal parent cannot
  append. Adding child-ongoing would wrongly prune adverse terminal replies.
- Exact history: snoc retains q/prior/m/hm; classifier receives ⟨q,prior⟩, so no
  erased-history substitution or arbitrary-seed counts alter the endpoint test.
- Legality quantifiers: for every actual m/hm in (1); every Legal successor in
  (2). Extracting its actual witness supplies append, RawBoardStep and endpoint
  equality together. Promotions/both colours/raw flags need no case split.
- Prior terminal prefix: recursion retains Admissible prior, so checking only
  the immediate parent cannot accidentally discard older obligations.
- Claims: optional 100/3 opportunities can be declined; raw automatic triggers
  use the frozen classifier. Successful/invalid claims are not board-move data.
- Vacuity: no existential claim that a particular initial-rooted game reaches a
  terminal endpoint is made. Terminal-child handling is a quantified implication,
  not a full-game witness. Ongoing parents' legal successors are not filtered.

Both directions and the complete reply construction have no remaining logical
gap. Kernel/FIDE correspondence, historical rights/key semantics and real claim
procedure remain separate obligations; no full Layer or rule-aware outcome is
claimed. No enumeration, engine/tablebase, stored certificate or novelty claim.
