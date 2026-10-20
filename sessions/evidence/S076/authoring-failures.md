# S076 retained authoring failures

All command invocations, exits, durations and UTC starts are retained in
working-commands.jsonl; all full logs remain alongside this file.

- 01: Targets reserved binder `at` and dependent equality elimination; replaced
  binder and used Piece.kind projection for impossible king/pawn equalities.
- 02: Castle attempted rewrite of hidden turn before unfolding canCastle.
- 03: Castle passed; later removed four unused simp arguments.
- 04: Strong used unavailable `swap` tactic; replaced by explicit castle test
  and disjunction elimination. 05 passed.
- 06: Closure used simp-only without the decidable-equality Boolean reduction;
  ordinary simp closes the actual no-pawn inequality. 07 passed.
- 08: shared Definitions lacked the KRK import and classical decidability for
  noncomputable fuel; explicit dependency and local classical scope added.
- 09 Step and 10 complete cap/terminal continuation passed. Full working library
  build and COMPLETE runner then passed. No failure is represented as success.

A command containing an unnecessary `rm -f` temporary marker cleanup was rejected
by automatic approval review before execution. Continued without cleanup; no
proof step or publication depended on deletion.

The quick post-build axiom validation initially failed on existing multiline
axiom formatting because it split on comma-space only. Whitespace normalization
(as already used by verify.py) validates all354 reports; retained explanation
and successful check are in working-report-validation.log. No Lean change or
Gate F promotion depended on that quick-check failure.
