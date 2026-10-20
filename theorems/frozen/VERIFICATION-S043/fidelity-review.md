# S043 — Generic raw key-occurrence fidelity review

Same-agent review, not independent external audit. Reviewed actual EC-C027
paper/audits, complete source definitions/proof, Gate F definition/main/axiom
logs, full source/import hashes and clean-source identity. No Lean edits needed.
occurrences universally quantifies fixed key:Position→K with explicit DecidableEq.
It filters full Trace.positions including root/current and every prior endpoint.
append_occurrences rewrites frozen append_spec position-list equality; filter
append and singleton length give old queried count plus exactly one iff the
new endpoint matches. Same map/query on both sides; correct propositional
equality is decided, not an untrusted Boolean comparison. No count seed/vector,
clock truncation, erased-history substitution or material/turn/terminal filter.
All legal raw appends including resets/adverse draw-ending children remain.

Symbolic root/absent/equal/new/nonconsecutive/constant-key/equal-erasure/reset/
earlier-draw controls found no gap. [A,B,A] followed by B has new-current count
2 rather than old-current A count+1=3; not asserted a compatible chess game.
No initial-rooted promotion/ep/castling/threshold prefix run or required.
Full bundle is Definitions and Append modules. Gate F main standard-three only;
a NEW Gate Z at OWN full source remains required before freezing.
Generic counting is not a FIDE key, low-repetition certificate, claims/terminal
admissibility/adjudication, strategy/lifting, numerical KRK, WDL/DTZ/Syzygy or
initial-position result. Classical list counting, no novelty/tablebase/engine.
