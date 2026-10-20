# EC-C030 — Lean fidelity review

S048. Same-agent review, not independent external audit. Main
RawRepetition.ordinary_ep_irrelevance exactly preserves isPseudo and FULL play
under the paper guard. noCapture proves the raw EP conjunction false for every
marker, then play unfolds identically including fresh output ep. Source option,
colour and piece-kind cases isolate the only pawnMoveOK ep dependency; same-file
or occupied-destination branches eliminate it. No shared definition changes.

Initial shell write used formal/ as cwd with root-relative paths; no source was
written, empty stray directories removed. First actual incremental build failed
only on wrong-colour Boolean simplification; full failure log retained. Explicit
Bool.eq_false_iff/beq_iff_eq resolved that step without statement changes.
Final incremental 75-job build and COMPLETE working AxiomCheck exit 0, no warnings;
277 allowed axiom reports, main standard-three. Clean Gate F pending.
