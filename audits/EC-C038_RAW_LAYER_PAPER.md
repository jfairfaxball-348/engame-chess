# EC-C038 — Separate adversarial paper audit

S064, completed before Lean. Same-agent review, not independent external audit.

- Every Layer obligation has a concrete proof: raw step soundness, actual
  admitted child from EVERY Legal successor, and ongoing nondeadness.
- A terminal child remains an element of the subtype. Requiring child ongoing
  would destroy reply completeness; the construction never does so.
- A terminal parent has no admitted actual next step by the frozen append guard.
  Start/current endpoint are not mistakenly required ongoing by subtype formation.
- CanClaim is raw availability, kept separate from automatic status. Certificates
  use the frozen semantics; this does not prove real FIDE claim correctness.
- The subtype stores the original trace and proof, not a history reconstruction.
  Witness child is exactly the appended state supplied by the frozen theorem;
  endpoint equality and RawBoardStep are both retained, including promotions.
- Same budget means literally the SAME n, no off-by-one board/claim ply shift.
  No certificate existence or reverse projection follows from this implication.
- Quantifiers cover all admitted states, colours, n (including zero) and moves,
  without restricting material/flags. At n=0 the certificate is the erased goal.

All exact interface/projection arguments close. LOCAL_VERIFIED relative to raw
classifier/claim semantics only. FIDE key/rights-history/real claim procedure,
rule-aware KRK outcome/strategy/distance remain open. No novelty, enumeration,
oracle/certificates or full-game witness is claimed.
