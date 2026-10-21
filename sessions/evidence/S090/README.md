# S090 integrated central wall95 evidence

Authoring: all35 actual Lean invocations, including failures, exact commands,
exit codes, UTC and durations in `commands.jsonl` and `working-*.log`.
Final local full build `working-034.log`:241 jobs, exit0. Complete runner
`working-035.log`:419 allowed reports, exact24 new statements, exit0.
No frozen source edit or ledger row. Candidate LOCAL_VERIFIED; Gate F/Z pending.

The paper is `proofs/EC-C052_KRK_CENTRAL_WALL_95.md`; separate same-agent
paper and Lean audits are under `audits/`. No external audit is claimed.

`central_wall_diagnostic.py` / `central-wall.json`: nine explicitly named roots,
four immediate local reply selectors,36 selected CLOCK-FREE paths, maximum49
plies. Separate ordinary-edge validator checks every chosen edge; phase budgets
and inspected weak-node safety/nonemptiness checked. This is not enumeration,
game values, universal strategy verification or a RAW history witness.

`verify.py OWN_SHA NEW_CLONE NEW_OUTPUT` is the fresh own-source Gate F runner,
adapted from S078 with explicit24-main list,27 complete modules,419 expected
reports and full equality to the local runner. It creates a NEW GitHub clone,
checks .lake is absent, builds, runs AxiomCheck and checks source/executable/
dependency identities. Each command has a1200-second ceiling. Gate Z must use
a separate fresh checkout. Frozen sources and scientific claims are unchanged
until those gates actually pass. Hosted CI is unobserved at this checkpoint.
