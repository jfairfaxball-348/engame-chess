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

## Observed Gate F

Own source `c4c900036dcffd209d6c08f27e2323637852c940`; new exact GitHub clone, no .lake before build; 75-job build exit 0 in 502.587s; complete AxiomCheck exit 0 at 2026-10-20T12:05:15Z, 277 allowed reports. Main standard-three; entire working/clean output byte-identical.
All formal source bytes match own anchor, source/transitive hashes and clean
HEAD/tree/status retained. Official core Lean4.35.0; no dependencies/shim.
Root-cwd elan identity lookup failed before clean verification; repeated in
formal/ successfully. No Lean failure in fresh clone. Hosted CI unobserved.
