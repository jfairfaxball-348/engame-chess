# EC-C030 — Adversarial paper audit

S048, before Lean authoring. Same-agent separate review, not an independent
external audit. The complete symbolic proof is in the standalone paper.

Attempted falsifications: missing source returns false for isPseudo and cannot
activate epCapture; wrong-colour pawn fails the outer colour guard and source
Pawn event; all nonpawns similarly disable raw epCapture. For a king, canCastle
reads board/turn/rights but never ep; attacks likewise read board only. Same-file
single/double pawn moves have dx=0, hence no capture geometry. Occupied captures
have false EP empty-destination test. Arbitrary promotion choices remain unchanged
in both pseudo tests and play arrivals. Source=destination retains play's original
destination-first ordering and disables distinct-file EP shape. Both colours,
arbitrary malformed markers/rights and arbitrary e use the same branch proof.
Output ep is recomputed, so equal board alone is not the claimed conclusion.

Rejected weakening: ¬LegalEP is insufficient. An illegal/pinned EP-shaped move
can still trigger raw play's off-destination removal. H explicitly excludes the
raw shape; legal EP-shaped moves must be handled separately in future proofs.
No legality premise is smuggled into the exact statement. No concrete pinned or
full promotion/castling/threshold game was run. No gap found in the stated claim.
Gate L: complete local argument; register LOCAL_VERIFIED, Gate F pending.
