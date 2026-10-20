"""Freeze raw endpoint classifier only after observed own-source Gate Z."""
import csv,io,json
from pathlib import Path
root=Path(__file__).resolve().parents[4];out=root/'theorems/frozen/VERIFICATION-S061';s=json.loads((out/'summary.json').read_text());sha=s['proof_source'];assert sha=='c3cbef551dbf7e16d002815d0a508540439e6ef6' and s['build_exit']==s['axiom_statement_exit']==0
assert (out/'axioms-statements.log').read_bytes()==(root/'sessions/evidence/S060/axioms-statements.log').read_bytes()
result=f"Own source `{sha}`; NEW GitHub clone `{s['fresh_clone']}`, no .lake before build. Full {s['build_jobs']}-job build exit 0, {s['build_seconds']}s; COMPLETE AxiomCheck exit 0 at {s['verified_utc']}, {s['total_axiom_reports']} allowed reports. Main standard-three; full report identical to S060 Gate F."
scope='''Raw mate-first classify returns opposite-turn winner at MatedK, draw at remaining
stalemate/dead/150-ply/fivefold triggers, otherwise ongoing. EXACT ongoing iff
nondead, some actual Legal successor, clock<150/count<5. No-successor check Bool
split gives mate/stale forward; converse successor refutes both, remaining draw
triggers false. Optional100/3 claims separate. All raw states/traces/flags/colours,
no legal reply pruning/history/material filter. Raw malformed mate/fivefold overlap
priority is definition, NOT extra FIDE9.6.1 priority; lawful-history proof outstanding.'''
checks='''Every formal byte matches own anchor/current source; full source/transitive
SHA256, clean HEAD/tree/status, full logs/commands/exits/times/UTC/toolchain retained.
Official core Lean4.35.0 release eb6cafb7290e8bd5f2937522d8d804f58f02bafc,
no dependency/shim/TLS/checksum change. One new clean run, no failure/repeated build.
No source edit/incremental build. Relevant ledger tests/structure, preservation/
evidence/full-table/full-prompt/local-link/diff checks passed; prior protected files
and33 rows unchanged, exactly EC-T0034 appended. No unrelated diagnostics/trivial
tests; hosted CI unobserved.'''
limits='''Raw component NOT certified full FIDE adjudication. No key/rights-history identity,
no-earlier-terminal histories/real claim protocol, full FIDE Layer/strategy lifting,
numerical KRK, holding/outcome, WDL/DTZ or initial value. Same-agent audit, not
independent external review; symbolic149/150,4/5,optional100/3,overlap/no-successor
controls, no actual full-game diagnostic/enumeration/oracle/certificates/novelty.
Existing S032 rules mapping retained, no new source retrieval.'''
name=s['bundle_declarations'][0];log=(out/'axioms-statements.log').read_text();statement=name+' :'+log.split(name+' :')[1];sources='\n'.join(f'### {p}\n\n```lean\n{(root/p).read_text()}```\n' for p in s['complete_modules'])
p=root/'theorems/frozen/EC-T0034/v1.md';assert not p.exists();p.parent.mkdir();p.write_text(f'''# EC-T0034 v1 — Raw mate-first endpoint classifier ongoing guards

**FROZEN S061, 2026-10-20**, candidate EC-C036. Own source `{sha}`.
Main `{name}`. BOTH complete RawAdjudication Definitions/Ongoing immutable.

{scope}

[Paper](../../../proofs/EC-C036_RAW_ENDPOINT_CLASSIFIER.md),
[paper audit](../../../audits/EC-C036_ENDPOINT_PAPER.md),
[Lean audit](../../../audits/EC-C036_ENDPOINT_LEAN.md),
[freeze review](../VERIFICATION-S061/fidelity-review.md).
Trust official Lean kernel/standard-three axioms, A1 and existing owner-reviewed
FIDE2023 legal-move encoding. Prior frozen imports unchanged; corrections new module.

{limits}

## Exact main and axioms

```text
{statement.strip()}
```

## Complete immutable boundary

{sources}
## Observed Gate Z

{result}

{checks}

[Evidence](../VERIFICATION-S061/README.md).

## Transitive SHA256

```text
{(out/'dependency-sha256.txt').read_text()}```
''')
p=root/'theorems/LEDGER.csv';old=p.read_bytes();rows=list(csv.DictReader(io.StringIO(old.decode())));assert len(rows)==33;fields=list(rows[0]);row=dict(zip(fields,['EC-T0034','Raw mate-first endpoint classifier exact ongoing guards','theorems/frozen/EC-T0034/v1.md','proofs/EC-C036_RAW_ENDPOINT_CLASSIFIER.md','formal/EndgameChess/Rules/RawAdjudication/Ongoing.lean',name,'leanprover/lean4:v4.35.0',sha,s['verified_utc'],'FIDE Laws of Chess 2023 legal-move kernel; raw mate-first endpoint component','theorems/frozen/EC-T0034/v1.md','FROZEN','From EC-C036. New own-source Gate Z; complete RawAdjudication Definitions/Ongoing frozen. Ongoing iff nondead/legal successor/clock<150/current count<5. Standard three axioms. No full FIDE adjudication/history or numerical KRK result.']));b=io.StringIO(newline='');csv.DictWriter(b,fieldnames=fields,lineterminator='\n').writerow(row);p.write_bytes(old+b.getvalue().encode())
p=root/'research/CANDIDATES.md';p.write_text(p.read_text().replace('FORMAL_VERIFIED (S060, 2026-10-20); Gate Z pending','**FROZEN as [EC-T0034](../theorems/frozen/EC-T0034/v1.md)** (S061, 2026-10-20)'))
p=root/'docs/SESSION_PROGRESS.md';t=p.read_text().replace('through S060. Thirty-three','through S061. Thirty-four').replace('these are not thirty-three solved','these are not thirty-four solved').replace('raw threshold/exact exclusion prerequisites frozen; raw ongoing classifier formally verified','raw threshold/exclusion and endpoint classifier prerequisites frozen');delta='Session change: S061 froze the raw mate-first ongoing characterization as EC-T0034 after a new exact-source Gate Z check; 34 bundles are frozen and material-class coverage is unchanged.';t=t.replace(next(l for l in t.splitlines() if l.startswith('Session change:')),delta);p.write_text(t)
p=root/'README.md';t=p.read_text().replace('**After S060.** Thirty-three frozen theorem bundles (not thirty-three solved material classes).','**After S061.** Thirty-four frozen theorem bundles (not thirty-four solved material classes).').replace('- Next: S061, separate own-source freeze of the raw endpoint classifier.','- Next: S062, stopped-history append and full legal-reply lifting.');t+='\n- S061: EC-C036 frozen as [EC-T0034](theorems/frozen/EC-T0034/v1.md), raw endpoint definitions/ongoing characterization immutable. [Evidence](theorems/frozen/VERIFICATION-S061/README.md).\n';p.write_text(t)
p=root/'docs/ROADMAP.md';p.write_text(p.read_text().replace('S061 separate freeze next.','S061 froze this as EC-T0034 after new own-source Gate Z, 34 bundles; S062 targets stopped-history append/full-reply lifting.'))
p=root/'theorems/README.md';t=p.read_text().replace('EC-T0007–EC-T0033 were first frozen','EC-T0007–EC-T0034 were first frozen').replace('Current frozen count: **33 bundles**, not thirty-three solved','Current frozen count: **34 bundles**, not thirty-four solved');t+='\n- [EC-T0034](frozen/EC-T0034/v1.md): raw mate-first endpoint ongoing guards; both modules frozen S061. [Evidence](frozen/VERIFICATION-S061/README.md).\n';p.write_text(t)
(out/'README.md').write_text(f'''# S061 — Raw endpoint classifier Gate Z

{result}

{scope}

{checks}

{limits}

Reproduce: `python theorems/frozen/VERIFICATION-S061/reproduction/verify.py REPO_ROOT NEW_OUTPUT NEW_CLONE {sha}`
Validate: `python theorems/frozen/VERIFICATION-S061/reproduction/validate.py REPO_ROOT`.
''')
table='\n'.join(l for l in (root/'docs/SESSION_PROGRESS.md').read_text().splitlines() if l.startswith('|'));prompt=(root/'NEXT_SESSION.md').read_text().strip()
(root/'sessions/S061_FREEZE_RAW_ENDPOINT_CLASSIFIER.md').write_text(f'''# S061 — Freeze raw mate-first endpoint classifier

2026-10-20, base main 0314ce63b1684ffde6d92e4237f2f79c460880bc;
branch session/s061-freeze-raw-endpoint-classifier. All-heads fetch, no prior
unmerged work, existing checkout; consecutive sessions/publication authorised.
EC-C036 frozen as EC-T0034, 34 bundles; material-class coverage unchanged.

{scope}

[Review](../theorems/frozen/VERIFICATION-S061/fidelity-review.md).

{limits}

## Observed verification and publication

{result}

{checks}

[Evidence](../theorems/frozen/VERIFICATION-S061/README.md). Own source published
before clone. Commit/push branch, merge/push main and compare remote identities,
retained in Git/observed publication; continue installed S062 until owner stops.

## Required progress table

{table}

{delta}

## Full installed S062 prompt

{prompt}
''')
p=root/'sessions/SESSION_LEDGER.md';t=p.read_text().replace('Full session closeouts live','| S061 | 2026-10-20 | Freeze EC-C036 raw endpoint classifier (Gate Z) | New own-source 86-job build, 283 allowed reports; both complete modules frozen. [Closeout](S061_FREEZE_RAW_ENDPOINT_CLASSIFIER.md) | **+1 → EC-T0034 FROZEN** (34 bundles) |\n\nFull session closeouts live');p.write_text(t)
print(result)
