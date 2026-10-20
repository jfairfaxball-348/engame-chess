# EC-C031 — Adversarial paper review

S050 before Lean authoring. Separate same-agent review, not independent external
audit. Exact statement and complete proof in standalone paper.

Absent/wrong-colour/nonpawn/king/castling cases are outside Pawn shape and use
frozen OrdinaryEP with full endpoint equality, not just equal boards. Same-file
pawn single/double and occupied captures also outside shape. Move promotion
fields unchanged, both colours treated uniformly. Source=destination is outside
shape. Arbitrary malformed markers and flags admitted; no reachability premise.
If ANY legal EP witness exists, marker retained even when current m differs.
If none exists, diagonal empty-dst source pawn cannot be legal originally;
normalized marker none makes pseudo-legal EP impossible too. This includes
pseudo-only EP exposing self-check: no claim of raw play equality on that branch.
No inCheck equality is assumed when raw played positions might differ.

Attempted weakening to unconditional play equality rejected (illegal EP-shaped
raw play may remove flank piece). Legal-only second clause is essential.
Conversely Boolean legal equality checks normalized moves as well as original
ones, so no new adverse reply can appear. Board/turn identity justifies Pawn
transport; full play identity in ordinary branch justifies self-check test.
No concrete pinned or compatible full promotion/castling/threshold game run;
controls are symbolic. Complete argument found; LOCAL_VERIFIED, Gate F pending.
