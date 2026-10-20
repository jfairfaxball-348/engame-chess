# EC-C032 — Adversarial paper audit

S052 before Lean authoring; same-agent separate review, not independent external
audit. Exact argument in paper. Equality must be full normalized record equality:
equal board with different turn, rights or effective marker does not establish
premise. No inverse or FIDE identity iff inferred from legal move coincidence.
Two raw markers differing only when no legal EP exists normalize together; frozen
preservation handles the resulting ordinary/illegal-EP cases without unconditional
raw play equality. Legal equality must first supply r legality before invoking
its full endpoint clause. Both directions of Boolean equality retained.

Every actual Move/promotion included, both colours, king/castling, source=dst,
absent/wrong-colour sources, pinned/pseudo-only EP, no-legal-move positions.
All are covered by frozen preservation plus exact equality; no endpoint assertion
on illegal moves or adverse reply pruning. No global DecidableEq Position needed,
no claim of executable key/hash. No concrete full-game run or enumeration/oracle.
No gap found in exact one-way congruence. LOCAL_VERIFIED; Gate F pending.
