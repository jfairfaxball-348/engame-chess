# NEXT SESSION — S068: Formalise the explicit KRK strategy bound

Owner has explicitly resumed research and requested consecutive sessions until
asked to stop (2026-10-20). Continue the direct KRK attack; stop before KQK.
Follow AGENTS.md, charter and proof protocol; fetch all remote heads, merge prior
unmerged work and start latest main. Commit/push branch, merge/push main and
compare identities, never force main. Full stable progress table, Syzygy last.

Read proofs/EC-C040_KRK_QUANTITATIVE_BOUND.md and its separate same-agent audit
at audits/EC-C040_KRK_QUANTITATIVE_PAPER.md. EC-C040 is LOCAL_VERIFIED only.
Principal claim: both colours, arbitrary target flags, exact strong-turn KRK
with no weak check (hence every legal strong-turn arrival) has MateWithin at
508 plies. For a rank wall n=7−R.y,g=R.y−S.y, use U(n)=84*n and
A(n,g)=84*(n−1)+62+4*(g−1). Pursuit with uniform exit budget E costs ≤8*m+E,
m=remaining oriented strong-file distance≤7. Setup costs ≤4 plies. Every weak
reply and nonempty witness is retained. Same-budget transport from noRights
source is NEW; frozen existential transport alone is insufficient.

Formalise the exact paper statement in NEW modules, one main theorem per module,
shared definitions separately. Preserve all frozen modules/records. Add mains
and helpers to AxiomCheck and aggregate imports. Use fixed-budget choose/defend,
not finite-branching sums. Audit n=1/edge mate, g normalization overhead, up to
three rook tempos before pursuit advance, threatened-rook rescue, back-rank and
axis-switch setup, all weak branches, source noRights and arbitrary target flags.
The bound is deliberately coarse and nonoptimal; no exact distance, FIDE rule-aware
win or occurrence uniqueness follows. EC-C039 remains freeze backlog; do not
replace the numerical KRK proof with generic library work.

Run appropriate changed-module/importer incremental checks and complete runner.
Publish OWN full proof-source SHA, then ONE NEW GitHub clone with no .lake before
full lake build and complete AxiomCheck. Official core Lean4.35.0,
ELAN_HOME=/workspace/.tools/elan, inherited proxy/CA; no dependency/shim/TLS/checksum
changes. Retain actual logs, commands/exits/times/UTC, executable/toolchain,
clean HEAD/tree/status, complete source/transitive hashes and working/clean
runner equality; standard-three axioms only. Observe results before promotion.
Gate Z separate. If formalisation is blocked preserve exact failure and next
KRK-specific obligation; do not weaken the statement silently.

Update candidate/roadmap/README/progress/completion tracker, session ledger and
sessions/S068_KRK_QUANTITATIVE_LEAN.md with actual evidence and FULL next prompt.
Report exact bound/new coverage or unchanged coverage. Following successful Gate F,
install separate Gate Z for this numerical KRK result, then return to strategy
history safety and sharper budgets. 508 cannot satisfy clock+n<100; finite macro
progress does not imply no repeated normalized keys or handle incoming history.
Complete FIDE integration, every-history outcomes, holding and exact WDL/DTZ
remain open. Continue consecutive authorised sessions until owner asks to stop.
