# S070 authoring failures and exact repairs

All working commands use the structured wrapper, with full logs/exits/times/UTC
in working-commands.jsonl. These are authoring errors in NEW modules, not changes
to the paper statement or frozen source.

1. working-build-01: KeyInterface needed explicit normalization unfolding for
   board/turn field equality; Legal stores endpoint=play, so endpoint equality
   composition was reversed. Corrected the direction without changing endpoints.
2. working-build-02: core Lean lacks the by_contra tactic. Least-witness proof
   used explicit classical case split; later uses Classical.byContradiction.
3. working-build-03: list-indexed StrategyLine cannot be directly inducted at a
   nonvariable q::tail index. Generalised the index and recovered head/tail by
   equality before proving the full certificate. Terminal colour cases needed
   explicit Colour.opp unfolding. Deprecated dif_pos/neg names produced warnings;
   replaced with dite_eq_left/right. Least theorem separated from rank definition.
4. working-build-04: all target modules passed. Final aggregate build and complete
   AxiomCheck passed without warnings; all nine new statements inspected.

No statements weakened. No Lean dependency/shim/toolchain/TLS/checksum changes.
Fresh published-source Gate F is separate from these incremental authoring runs.
