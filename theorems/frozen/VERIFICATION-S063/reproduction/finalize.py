"""Freeze EC-C037 only after the separate observed own-source Gate Z."""
import csv,io,json
from pathlib import Path
root=Path(__file__).resolve().parents[4];out=root/'theorems/frozen/VERIFICATION-S063';s=json.loads((out/'summary.json').read_text());sha=s['proof_source'];assert sha=='67850895bf6130a1f193c299597cd7d4ac209485' and s['build_exit']==s['axiom_statement_exit']==0
assert (out/'axioms-statements.log').read_bytes()==(root/'sessions/evidence/S062/axioms-statements.log').read_bytes()
result=f"Own proof source `{sha}`; NEW GitHub clone `{s['fresh_clone']}`, .lake absent before build. Full {s['build_jobs']}-job build exit 0 ({s['build_seconds']}s); complete AxiomCheck exit 0 at {s['verified_utc']}, {s['total_axiom_reports']} allowed reports. Main standard-three; full runner identical to S062 Gate F and all formal bytes identical."
scope='''StoppedHistory.Admissible uses actual indexed initial-rooted Trace: start=True,
snoc=admissible prior AND classify exact parent ongoing. Main conjunction for
EVERY raw s: EVERY legal m/hm has admissible actual append iff admissible ongoing
parent; from admissible ongoing s, EVERY Legal reply lifts to admissible actual
RawBoardStep with exact erasure. Terminal children/current endpoint allowed;
terminal parent cannot append, no child-ongoing filter. Exact q/prior/m/hm retained,
no erased-history reconstruction or arbitrary seed counts. Optional claim
opportunities may be declined; board traces have no successful/invalid claim.'''
limits='''Relative to CHOSEN RAW classifier only, not certified complete FIDE legal-history,
rights/key/adjudication/claim correspondence. No full Layer, converse strategy
lifting, numerical KRK, holding/outcome, WDL/DTZ or initial value. Same-agent
separate paper/Lean/freeze audits, not independent external review. Symbolic
zero/one-ply, parent/child terminal, every adverse terminal reply, both colours/
promotions/raw flags; no full-game run/enumeration/oracle/certificates/novelty.'''
checks='''One new exact-source Gate Z run, no formal-source edit/incremental build.
All logs/commands/exits/times/UTC, executable/toolchain, clean HEAD/tree/status,
full source/transitive SHA256 and working/Gate F equality retained. Official
core Lean4.35.0 release eb6cafb7290e8bd5f2937522d8d804f58f02bafc, no dependency/
shim/TLS/checksum changes. Inherited proxy/CA, current unrestricted/enforced
policy. No failure/interruption/repeated clean build. Hosted CI unobserved.
Relevant ledger tests/structure/evidence/preservation/full-table/full-prompt/
local-link/diff checks passed; all prior protected files and34 ledger rows
preserved; exactly EC-T0035 appended. No unrelated diagnostics/trivial tests.'''
name=s['bundle_declarations'][0];log=(out/'axioms-statements.log').read_text();statement=name+' :'+log.split(name+' :')[1];sources='\n'.join(f'### {p}\n\n```lean\n{(root/p).read_text()}```\n' for p in s['complete_modules'])
p=root/'theorems/frozen/EC-T0035/v1.md';assert not p.exists();p.parent.mkdir();p.write_text(f'''# EC-T0035 v1 — Stopped-history append and full legal-reply lifting

**FROZEN S063, 2026-10-20**, candidate EC-C037. Own source `{sha}`.
Main `{name}`. Complete StoppedHistory Definitions/AppendLifting immutable.

{scope}

[Paper](../../../proofs/EC-C037_STOPPED_HISTORY_LIFTING.md),
[paper audit](../../../audits/EC-C037_STOPPED_HISTORY_PAPER.md),
[Lean audit](../../../audits/EC-C037_STOPPED_HISTORY_LEAN.md),
[freeze review](../VERIFICATION-S063/fidelity-review.md).
Trust official Lean kernel, standard-three axioms, A1 and existing owner-reviewed
FIDE2023 legal-move kernel. Prior frozen imports unchanged; corrections new module.

{limits}

## Exact main and axioms

Axioms: `{s['bundle_axioms'][name]}`.

```text
{statement.strip()}
```

## Complete immutable boundary

{sources}
## Observed Gate Z

{result}

{checks}

[Evidence](../VERIFICATION-S063/README.md).

## Transitive SHA256

```text
{(out/'dependency-sha256.txt').read_text()}```
''')
p=root/'theorems/LEDGER.csv';old=p.read_bytes();rows=list(csv.DictReader(io.StringIO(old.decode())));assert len(rows)==34;fields=list(rows[0]);row=dict(zip(fields,['EC-T0035','Stopped-history actual append and full legal-reply lifting','theorems/frozen/EC-T0035/v1.md','proofs/EC-C037_STOPPED_HISTORY_LIFTING.md','formal/EndgameChess/Rules/StoppedHistory/AppendLifting.lean',name,'leanprover/lean4:v4.35.0',sha,s['verified_utc'],'FIDE Laws of Chess 2023 legal-move kernel; chosen raw stopped-history classifier','theorems/frozen/EC-T0035/v1.md','FROZEN','From EC-C037. Separate own-source Gate Z; complete StoppedHistory Definitions/AppendLifting frozen. Exact append iff and EVERY legal reply lifting including terminal children. Standard three axioms; no full FIDE correspondence or numerical KRK result.']));b=io.StringIO(newline='');csv.DictWriter(b,fieldnames=fields,lineterminator='\n').writerow(row);p.write_bytes(old+b.getvalue().encode())
p=root/'research/CANDIDATES.md';p.write_text(p.read_text().replace('FORMAL_VERIFIED (S062, 2026-10-20); Gate Z pending','**FROZEN as [EC-T0035](../theorems/frozen/EC-T0035/v1.md)** (S063, 2026-10-20)'))
p=root/'docs/SESSION_PROGRESS.md';t=p.read_text().replace('through S062. Thirty-four','through S063. Thirty-five').replace('these are not thirty-four solved','these are not thirty-five solved').replace('endpoint classifier prerequisites frozen; stopped-history append/reply lifting formally verified','endpoint classifier and stopped-history append/reply prerequisites frozen');delta='Session change: S063 froze stopped-history append and full legal-reply lifting as EC-T0035 after separate exact-source Gate Z; 35 bundles are frozen and material-class coverage is unchanged.';t=t.replace(next(l for l in t.splitlines() if l.startswith('Session change:')),delta);p.write_text(t)
p=root/'README.md';t=p.read_text().replace('**After S062.** Thirty-four frozen theorem bundles (not thirty-four solved material classes).','**After S063.** Thirty-five frozen theorem bundles (not thirty-five solved material classes).').replace('- Next: S063, separate own-source freeze of stopped-history append and full legal-reply lifting.','- Next: S064, concrete RAW Layer on admissible stopped histories.');t+='\n- S063: EC-C037 frozen as [EC-T0035](theorems/frozen/EC-T0035/v1.md), stopped-history definitions/append and full-reply lifting immutable. [Evidence](theorems/frozen/VERIFICATION-S063/README.md).\n';p.write_text(t)
p=root/'docs/ROADMAP.md';p.write_text(p.read_text().replace('S063 separate freeze next.','S063 froze this as EC-T0035 after separate own-source Gate Z, 35 bundles; S064 targets a concrete RAW Layer on admissible stopped histories.'))
p=root/'theorems/README.md';t=p.read_text().replace('EC-T0007–EC-T0034 were first frozen','EC-T0007–EC-T0035 were first frozen').replace('Current frozen count: **34 bundles**, not thirty-four solved','Current frozen count: **35 bundles**, not thirty-five solved');t+='\n- [EC-T0035](frozen/EC-T0035/v1.md): stopped-history append and full legal replies including terminal children; both modules frozen S063. [Evidence](frozen/VERIFICATION-S063/README.md).\n';p.write_text(t)
(out/'README.md').write_text(f'''# S063 — Stopped-history append/full replies Gate Z

{result}

{scope}

{checks}

{limits}

Reproduce: `python theorems/frozen/VERIFICATION-S063/reproduction/verify.py REPO_ROOT NEW_OUTPUT NEW_CLONE {sha}`.
Validate: `python theorems/frozen/VERIFICATION-S063/reproduction/validate.py REPO_ROOT`.
''')
table='\n'.join(l for l in (root/'docs/SESSION_PROGRESS.md').read_text().splitlines() if l.startswith('|'));prompt=(root/'NEXT_SESSION.md').read_text().strip()
(root/'sessions/S063_FREEZE_STOPPED_HISTORY_LIFTING.md').write_text(f'''# S063 — Freeze stopped-history append and full replies

2026-10-20. Base main c6af7d60175e0500880d40f8e83681af208b40b4,
branch session/s063-freeze-stopped-history-lifting. ALL-heads fetch, no prior
unmerged heads, existing checkout. Owner explicitly requested continuing until
KRK entirely finished/frozen, stopping BEFORE KQK; retained in installed prompt.
EC-C037 frozen as EC-T0035;35 bundles, not solved material classes.

{scope}

[Review](../theorems/frozen/VERIFICATION-S063/fidelity-review.md).

{limits}

## Observed verification and publication

{result}

{checks}

[Evidence](../theorems/frozen/VERIFICATION-S063/README.md). Source was published
before clone. Session committed/pushed, merged/pushed main and remote identities
compared at publication, observed in tool output/Git. Continue installed S064.

## Required progress table

{table}

{delta}

## Full installed S064 prompt

{prompt}
''')
p=root/'sessions/SESSION_LEDGER.md';p.write_text(p.read_text().replace('Full session closeouts live','| S063 | 2026-10-20 | Freeze EC-C037 stopped-history append/full replies (Gate Z) | New exact-source build and complete axiom audit; both modules frozen. [Closeout](S063_FREEZE_STOPPED_HISTORY_LIFTING.md) | **+1 → EC-T0035 FROZEN** (35 bundles) |\n\nFull session closeouts live'))
print(result)
