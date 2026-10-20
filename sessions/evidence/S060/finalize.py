"""Finalize selected raw endpoint classifier theorem from observed Gate F."""
import json
from pathlib import Path
root=Path(__file__).resolve().parents[3];out=root/'sessions/evidence/S060';s=json.loads((out/'summary.json').read_text());sha=s['proof_source'];assert sha=='c3cbef551dbf7e16d002815d0a508540439e6ef6' and s['build_exit']==s['axiom_statement_exit']==0
result=f"Own source `{sha}`; NEW GitHub clone `{s['fresh_clone']}`, no .lake before build. Full {s['build_jobs']}-job build exit 0, {s['build_seconds']}s; COMPLETE AxiomCheck exit 0 at {s['verified_utc']}, {s['total_axiom_reports']} allowed reports. Main standard-three; whole working/clean report identical."
checks='''Exact main inspected, every formal byte matches own anchor; full source/transitive
SHA256, clean HEAD/tree/status, full logs/commands/exits/times/UTC/toolchain retained.
Official core Lean4.35.0 release eb6cafb7290e8bd5f2937522d8d804f58f02bafc,
no dependencies/shim/TLS/checksum change. Both new modules forbidden scan zero.
Incremental 86-job build/full working runner and clean verification passed FIRST
attempt, no warnings/failures/repeated clean build. Relevant ledger/evidence/
preservation/full-table/full-prompt/local-link/diff checks passed; all prior
protected files/33 rows unchanged, aggregate imports/runner additive. No unrelated
diagnostics/trivial tests. Hosted CI unobserved; existing environment/proxy sufficient.'''
scope='''Selected next concrete prerequisite after reviewing S032 §4 and existing kernel.
NEW RawAdjudication Stalemated/DrawTrigger/EndpointStatus/classify definitions:
MatedK first gives opposite-turn winner, then stalemate/dead/150-ply/fivefold gives
draw, otherwise ongoing. Main exact ongoing IFF nondead, some actual kernel Legal
successor, clock<150/count<5. Forward no-successor Bool check split yields mate or
stalemate contradiction; reverse successor refutes mate/stale then all draw
triggers excluded. No legal reply pruned. All raw states/traces/flags/colours;
no valid-history/material assumption. Optional100/3 claims remain separate.'''
limits='''Raw classifier component, NOT full FIDE adjudication/history correctness. Mate
priority at150 explicit; mate/fivefold malformed overlap priority is chosen raw
model, not extra Article9.6.1 precedence. Admissibility excludes feasible overlap
only after a separate proof. Existing S032 rules mapping retained, not redone.
No full key/rights-history, no-earlier-terminal histories/real claim protocol,
concrete FIDE Layer/strategy lifting, numerical KRK, holding/outcome, WDL/DTZ or
initial value. Paper and separate audit BEFORE Lean; same-agent review, not
independent external audit.149/150,4/5,optional100/3,mate/stale/dead overlap,
no-successor controls symbolic, no full-game diagnostic/enumeration/oracle/stored
certificate/novelty. Existing retained FIDE source used, no new retrieval.'''
p=root/'research/CANDIDATES.md';t=p.read_text().replace('LOCAL_VERIFIED (S060, 2026-10-20); Gate F pending','FORMAL_VERIFIED (S060, 2026-10-20); Gate Z pending').replace('Optional100/3 claims remain separate.',result+' [Evidence](../sessions/evidence/S060/README.md). Optional100/3 claims remain separate.');p.write_text(t)
p=root/'audits/EC-C036_ENDPOINT_LEAN.md';p.write_text(p.read_text()+'\n## Observed Gate F\n\n'+result+'\n\n'+checks+'\n')
p=root/'docs/SESSION_PROGRESS.md';t=p.read_text().replace('through S059.','through S060.').replace('raw threshold/exact exclusion prerequisites frozen |','raw threshold/exact exclusion prerequisites frozen; raw ongoing classifier formally verified |');delta='Session change: S060 formally verified exact ongoing guards for the raw mate-first endpoint classifier; 33 bundles remain frozen and material-class coverage is unchanged.';t=t.replace(next(l for l in t.splitlines() if l.startswith('Session change:')),delta);p.write_text(t)
p=root/'README.md';t=p.read_text().replace('**After S059.**','**After S060.**').replace('- Next: S060, select the next concrete terminal/history prerequisite.','- Next: S061, separate own-source freeze of the raw endpoint classifier.');t+='\n- S060: EC-C036 **FORMAL_VERIFIED**, raw mate-first classifier ongoing iff nondead/legal successor/clock<150/count<5. [Paper](proofs/EC-C036_RAW_ENDPOINT_CLASSIFIER.md), [evidence](sessions/evidence/S060/README.md).\n';p.write_text(t)
p=root/'docs/ROADMAP.md';p.write_text(p.read_text().replace('S060 reviews the next concrete terminal/history prerequisite.','S060 selected and formally verified EC-C036, exact raw mate-first ongoing guards ([paper](../proofs/EC-C036_RAW_ENDPOINT_CLASSIFIER.md), [evidence](../sessions/evidence/S060/README.md)); S061 separate freeze next.'))
(out/'README.md').write_text(f'''# S060 — Raw mate-first ongoing classifier Gate F

{result}

{scope}

{checks}

{limits}

Reproduce: `python sessions/evidence/S060/verify.py REPO_ROOT NEW_OUTPUT NEW_CLONE {sha}`
Validate: `python sessions/evidence/S060/validate.py`.
''')
table='\n'.join(l for l in (root/'docs/SESSION_PROGRESS.md').read_text().splitlines() if l.startswith('|'));prompt=(root/'NEXT_SESSION.md').read_text().strip()
(root/'sessions/S060_RAW_ENDPOINT_CLASSIFIER.md').write_text(f'''# S060 — Raw mate-first endpoint classifier ongoing guards

2026-10-20, base main 7fa1f04e19c9f6ceaab505cb2e80311c60d20ea3,
branch session/s060-raw-endpoint-classifier. All-heads fetch, no prior unmerged
work, existing checkout; consecutive sessions/publication authorised.
EC-C036 FORMAL_VERIFIED, Gate Z pending.

{scope}

[Paper](../proofs/EC-C036_RAW_ENDPOINT_CLASSIFIER.md),
[paper audit](../audits/EC-C036_ENDPOINT_PAPER.md),
[Lean fidelity](../audits/EC-C036_ENDPOINT_LEAN.md).

{limits}

## Observed verification and publication

{result}

{checks}

[Evidence](evidence/S060/README.md). Own source pushed before clean clone;
closeout commit/push branch, merge/push main and remote identity verified and
retained in Git/observed publication. Continue installed S061 until stopped.

## Required progress table

{table}

{delta}

## Full installed S061 prompt

{prompt}
''')
p=root/'sessions/SESSION_LEDGER.md';t=p.read_text().replace('Full session closeouts live','| S060 | 2026-10-20 | EC-C036 raw mate-first endpoint classifier (Gate L/F) | Exact ongoing nondead/legal-move/150-ply/fivefold guards. [Closeout](S060_RAW_ENDPOINT_CLASSIFIER.md) | None — 33 frozen bundles |\n\nFull session closeouts live');p.write_text(t)
print(result)
