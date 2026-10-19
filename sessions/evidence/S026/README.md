# S026 exact-source Gate F evidence

- Proof-source: `e8daef6daee088c3adaf1c21b51c0a8f1e31103d`. Fresh GitHub clone, detached at that commit, no `.lake`.
- Gate F completed UTC: `2026-10-19T08:00:05Z`. `clean-build.log`: 29 jobs, 296.85 seconds, exit 0.
- `clean-axioms.log`: all 197 reports within standard axiom subsets, including 17 new declarations and the full four-ply statement. Working and clean report content matches. `working-axioms.log` is retained for comparison.
- `source-sha256.txt`: the three new Lean modules, matched to the closeout tree. No frozen module changed.
- `forbidden-tokens.log`: zero forbidden tokens.
- `negative-controls.log`: three deliberately false capture/safety/re-entry claims rejected by Lean.
- `python-tests.log`: all 33 tests passed.
- `phase-diagnostic.json`: 24 chosen configurations, both colours; 8 edge mates, 44 first replies, 194 second replies; two failed-margin controls. No class graph, fixpoint or external evaluations were used. This diagnostic is supplementary, not a proof.

Core-only Lean 4.35.0, release commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. Host executable-path shim documented with `theorems/frozen/EC-T0007/verification-environment.md`; official binaries and proof/kernel routines unmodified. Remote CI is not asserted as observed.

Gate Z is not yet run for EC-C012/013. The general KRK forcing candidate EC-C011 remains PROPOSED.
