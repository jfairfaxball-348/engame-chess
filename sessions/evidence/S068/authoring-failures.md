# Retained authoring failures

Before the structured working-command wrapper was installed, the following
commands were run with redirected full logs. Exact timing/UTC were not captured;
file timestamps are incidental, not reconstructed timing evidence.

- A toolchain-version command at repository root (rather than formal/) failed:
  `error: no default toolchain configured`. No toolchain configuration changed.
- First scratch-file write/build invocation used formal/ as cwd while using
  repository-root paths. Bash/Python reported work/write_s068.py absent. No
  project source was created by that failed write. Corrected cwd to root.
- working-build-01.log: explicit Transport and LowerBand targets; LowerBand
  wrapper retained ForceMate result in a copied multiline declaration. Changed
  the NEW wrapper to the paper's MateWithin (56+E). Transport/Pursuit passed.
- working-build-02.log: Wall target; missed replacement of rescue constructors,
  zero-budget inference at hmate, and non-definitional arithmetic around +2.
  Fixed to fixed-budget pair, explicit n=0 and monotonic padding.
- working-build-03.log: Wall target after the rescue-constructor fix; remaining
  zero-budget and arithmetic fixes followed. Full log retained.
- working-build-04.log: Wall target passed.
- working-build-05.log: Setup target; copied Entry multiline result still
  ForceMate. Changed NEW result to paper budget 506.
- working-build-06.log: Setup target; same missed multiline result in ClearEntry.
  Changed NEW result to 506. BackRank multiline result also changed to 508.
- working-build-07.log: complete Setup target passed, including all geometry.
- working-build-08.log: full aggregate build after splitting main declarations
  into separate modules; final status recorded in that log.

These were authoring mistakes in new files, not counterexamples to the paper or
changes to frozen modules. All target logs preserve exact Lean failures. Fresh
Gate F is a separate new published-source checkout, not any of these runs.
