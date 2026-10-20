"""Finalize S056 from observed own-source Gate F only."""
import json
from pathlib import Path
root=Path(__file__).resolve().parents[3];out=root/'sessions/evidence/S056';s=json.loads((out/'summary.json').read_text());sha=s['proof_source']
assert sha=='1f262968c80a1352c156f6e0c07dd5132c432b13' and s['build_exit']==s['axiom_statement_exit']==0
result=f"Own source `{sha}`; NEW GitHub clone `{s['fresh_clone']}`, no .lake before build. Full {s['build_jobs']}-job build exit 0, {s['build_seconds']}s; COMPLETE AxiomCheck exit 0 at {s['verified_utc']}, {s['total_axiom_reports']} allowed reports. Main standard-three, entire working/clean report identical."
checks='''Exact main inspected; every formal byte matches own anchor. Full source/transitive
SHA256, clean HEAD/tree/status, full logs/commands/exits/times/UTC/toolchain retained.
Official core Lean4.35.0 release eb6cafb7290e8bd5f2937522d8d804f58f02bafc,
no dependency/shim/TLS/checksum change; both new modules forbidden scan zero.
Incremental 83-job build/full working runner and clean verification passed first
attempt without warnings/failures/repeated clean build. Relevant ledger/evidence/
preservation/full-table/full-prompt/local-link/diff checks passed, all prior
protected files and31 rows unchanged, aggregates additive only. No unrelated
diagnostics/trivial tests. Hosted CI unobserved; existing environment/proxy sufficient.'''
scope='''NEW RawClaims shared predicates retain root clock/count and EVERY actual legal
intended append. Under explicit root clock+1<100, currentcount<3 and every legal
intended new-key old-history query<2, AvailableThreshold is false. Frozen clock
append bound and concrete current count append law exclude both actual child
thresholds; root conditions exclude current disjunct. Every adverse intended move,
actual indexed trace/hm, colour/flag/promotion retained. No terminal/material/
history/strategy restriction, reset truncation or old-current-query shortcut.'''
limits='''Raw bookkeeping, NOT certified FIDE CanClaim/adjudication; frozen Layer unchanged.
No FIDE key/rights-history identity, no-earlier-terminal histories, real claims/
automatic draw/mate precedence, strategy lifting, numerical KRK, holding/outcome,
WDL/DTZ/Syzygy or initial value. Explicit hypotheses not a strategy-tree certificate.
Same-agent paper/Lean audits, not independent external audit. Boundary98/99/100,
1/2/3, no-reply vacuity/zeroing/pseudo-only/new-query controls symbolic; no concrete
full-game run, enumeration/engine/tablebase/stored certificate or novelty claim.'''
p=root/'research/CANDIDATES.md';t=p.read_text().replace('LOCAL_VERIFIED (S056, 2026-10-20); Gate F pending','FORMAL_VERIFIED (S056, 2026-10-20); Gate Z pending').replace('Raw bookkeeping predicates only; no certified FIDE CanClaim/adjudication or numerical KRK witness.',result+' [Evidence](../sessions/evidence/S056/README.md). Raw bookkeeping predicates only; no certified FIDE CanClaim/adjudication or numerical KRK witness.');p.write_text(t)
p=root/'audits/EC-C034_THRESHOLD_LEAN.md';p.write_text(p.read_text()+'\n## Observed Gate F\n\n'+result+'\n\n'+checks+'\n')
p=root/'docs/SESSION_PROGRESS.md';t=p.read_text().replace('through S055.','through S056.').replace('normalization/key/count prerequisites frozen |','normalization/key/count prerequisites frozen; raw threshold certificate formally verified |');delta='Session change: S056 formally verified a raw current/intended clock-and-repetition threshold exclusion certificate; 31 bundles remain frozen and material-class coverage is unchanged.';t=t.replace(next(l for l in t.splitlines() if l.startswith('Session change:')),delta);p.write_text(t)
p=root/'README.md';t=p.read_text().replace('**After S055.**','**After S056.**').replace('- Next: S056, raw current/intended threshold exclusion certificate.','- Next: S057, separate exact-source freeze of the raw threshold certificate.');t+='\n- S056: EC-C034 **FORMAL_VERIFIED**, explicit root and EVERY legal intended-move bounds exclude raw clock/repetition thresholds. [Paper](proofs/EC-C034_RAW_THRESHOLD_CERTIFICATE.md), [evidence](sessions/evidence/S056/README.md). Raw bookkeeping, not certified FIDE claims.\n';p.write_text(t)
p=root/'docs/ROADMAP.md';p.write_text(p.read_text().replace('S056 targets a raw current/intended threshold exclusion certificate.','S056 formally verified EC-C034, raw current/intended threshold exclusion under explicit root/ALL legal intended-child budgets ([paper](../proofs/EC-C034_RAW_THRESHOLD_CERTIFICATE.md), [evidence](../sessions/evidence/S056/README.md)); S057 separate freeze next.'))
(out/'README.md').write_text(f'''# S056 — Raw threshold exclusion Gate F

{result}

{scope}

{checks}

{limits}

Reproduce: `python sessions/evidence/S056/verify.py REPO_ROOT NEW_OUTPUT NEW_CLONE {sha}`
Validate: `python sessions/evidence/S056/validate.py`.
''')
table='\n'.join(l for l in (root/'docs/SESSION_PROGRESS.md').read_text().splitlines() if l.startswith('|'));prompt=(root/'NEXT_SESSION.md').read_text().strip()
(root/'sessions/S056_RAW_THRESHOLD_CERTIFICATE.md').write_text(f'''# S056 — Raw threshold exclusion certificate

2026-10-20, base main 1f5aaad9e5b51eb61a7967429a50cf5bc5452bb3,
branch session/s056-raw-threshold-certificate. All-heads fetch, no prior unmerged
work, existing checkout; consecutive sessions/publication authorised.
EC-C034 FORMAL_VERIFIED, Gate Z pending.

## Exact result and audit

{scope}

Standalone [paper](../proofs/EC-C034_RAW_THRESHOLD_CERTIFICATE.md) and separate
[paper audit](../audits/EC-C034_THRESHOLD_PAPER.md) BEFORE Lean;
[Lean fidelity](../audits/EC-C034_THRESHOLD_LEAN.md).

{limits}

## Observed verification and publication

{result}

{checks}

[Evidence](evidence/S056/README.md). Own source published before clone. Closeout
commit/push branch, merge/push main and compare remote SHAs; final identities
retained in Git/observed publication checks. Continue installed S057 until stopped.

## Required progress table

{table}

{delta}

## Full installed S057 prompt

{prompt}
''')
p=root/'sessions/SESSION_LEDGER.md';t=p.read_text().replace('Full session closeouts live','| S056 | 2026-10-20 | EC-C034 raw threshold exclusion (Gate L/F) | Explicit root/ALL legal intended-child budgets exclude raw current/intended thresholds. [Closeout](S056_RAW_THRESHOLD_CERTIFICATE.md) | None — 31 frozen bundles |\n\nFull session closeouts live');p.write_text(t)
print(result)
