"""Freeze raw threshold certificate only after observed own-source Gate Z."""
import csv,io,json
from pathlib import Path
root=Path(__file__).resolve().parents[4];out=root/'theorems/frozen/VERIFICATION-S059';s=json.loads((out/'summary.json').read_text())
sha=s['proof_source'];assert sha=='c75b3760022717e586a789e47c09c03911a43a56';assert s['build_exit']==s['axiom_statement_exit']==0
assert (out/'axioms-statements.log').read_bytes()==(root/'sessions/evidence/S058/axioms-statements.log').read_bytes()
result=f"Own source `{sha}`; NEW GitHub clone `{s['fresh_clone']}`, no .lake before build. Full {s['build_jobs']}-job build exit 0 in {s['build_seconds']}s; COMPLETE AxiomCheck exit 0 at {s['verified_utc']}; {s['total_axiom_reports']} allowed reports. Main standard-three; whole report identical to S058 Gate F."
name=s['bundle_declarations'][0];log=(out/'axioms-statements.log').read_text();statement=name+' :'+log.split(name+' :')[1]
scope='''For every raw state s, no AvailableThreshold IFF rootclock<100/rootcount<3
and EVERY actual legal intended childclock<100/NEW endpoint OLD-history query<2.
Both directions, actual childclock retained rather than sufficient root+1 budget.
Root/child threshold injection gives forward strict Nat bounds, frozen actual
count append+1 gives query<2. Reverse bounds refute root and every intended child.
All actual indexed traces/hm/colours/flags/promotions retained; root independent,
no terminal/material/history/strategy restriction, reset/parent-query shortcut or
adverse intended move pruning. Raw bookkeeping NOT certified FIDE adjudication.'''
checks='''Every formal byte matches own anchor/current source; full source/transitive
SHA256, clean HEAD/tree/status and full logs/commands/exits/times/UTC/toolchain
retained. Official core Lean4.35.0 release eb6cafb7290e8bd5f2937522d8d804f58f02bafc,
no dependencies/shim/TLS/checksum change. Hosted CI unobserved. One new successful
clean run, no failure/repeated build; no source edit/incremental build. Relevant
ledger structure/tests, preservation/evidence/full-table/full-prompt/local-link/
diff checks passed; prior protected source/papers/audits/evidence/manifests and32
rows unchanged, exactly EC-T0033 appended. No unrelated diagnostics/trivial tests.'''
limits='''No full FIDE key/Article9.2.3/rights-history identity, repetition threshold/claim,
no-earlier-terminal histories, automatic-draw/mate precedence adjudication,
strategy lifting, numerical KRK, holding/outcome, WDL/DTZ/Syzygy or initial value.
Same-agent review, not independent external audit. Symbolic threshold99/100,2/3/zeroing/no-reply/pseudo-only controls,
not a compatible actual chess-game run. No enumeration/oracle/stored certificate,
executable hash/search or novelty claim.'''
sources='\n'.join(f'### {p}\n\n```lean\n{(root/p).read_text()}```\n' for p in s['complete_modules'])
p=root/'theorems/frozen/EC-T0033/v1.md';assert not p.exists();p.parent.mkdir();p.write_text(f'''# EC-T0033 v1 — Exact raw current and intended threshold exclusion

**FROZEN S059, 2026-10-20**, candidate EC-C035.
Own proof-source `{sha}`; main `{name}`.

{scope}

Complete RawClaims.ExclusionCharacterization below immutable; prior
frozen imports unchanged. Trust official Lean kernel, standard-three axioms, A1
and existing owner-reviewed FIDE2023 legal-move encoding. No new full FIDE bridge.
[Paper](../../../proofs/EC-C035_EXACT_RAW_THRESHOLD_EXCLUSION.md),
[paper audit](../../../audits/EC-C035_EXCLUSION_PAPER.md),
[Lean audit](../../../audits/EC-C035_EXCLUSION_LEAN.md),
[freeze fidelity](../VERIFICATION-S059/fidelity-review.md).

{limits}

## Exact main and axioms

```text
{statement.strip()}
```

## Complete immutable source boundary

{sources}
## Observed Gate Z

{result}

{checks}

[Evidence](../VERIFICATION-S059/README.md).

## Transitive SHA256

```text
{(out/'dependency-sha256.txt').read_text()}```
''')
p=root/'theorems/LEDGER.csv';old=p.read_bytes();rows=list(csv.DictReader(io.StringIO(old.decode())));assert len(rows)==32;fields=list(rows[0]);row=dict(zip(fields,['EC-T0033','Exact raw current and every legal intended threshold exclusion iff','theorems/frozen/EC-T0033/v1.md','proofs/EC-C035_EXACT_RAW_THRESHOLD_EXCLUSION.md','formal/EndgameChess/Rules/RawClaims/ExclusionCharacterization.lean',name,'leanprover/lean4:v4.35.0',sha,s['verified_utc'],'FIDE Laws of Chess 2023 legal-move kernel; raw clock/repetition threshold certificate only','theorems/frozen/EC-T0033/v1.md','FROZEN','From EC-C035. New own-source Gate Z; complete ExclusionCharacterization frozen. Exact root/ALL legal intended-child clock/new-key query threshold exclusion iff. Standard three axioms. No full FIDE identity/threshold/adjudication or numerical KRK claim.']));b=io.StringIO(newline='');csv.DictWriter(b,fieldnames=fields,lineterminator='\n').writerow(row);p.write_bytes(old+b.getvalue().encode())
p=root/'research/CANDIDATES.md';p.write_text(p.read_text().replace('FORMAL_VERIFIED (S058, 2026-10-20); Gate Z pending','**FROZEN as [EC-T0033](../theorems/frozen/EC-T0033/v1.md)** (S059, 2026-10-20)'))
p=root/'docs/SESSION_PROGRESS.md';t=p.read_text().replace('through S058. Thirty-two','through S059. Thirty-three').replace('these are not thirty-two solved','these are not thirty-three solved').replace('raw threshold prerequisites frozen; exact threshold iff formally verified','raw threshold/exact exclusion prerequisites frozen');delta='Session change: S059 froze the exact raw threshold exclusion characterization as EC-T0033 after a new exact-source Gate Z check; 33 bundles are frozen and material-class coverage is unchanged.';t=t.replace(next(l for l in t.splitlines() if l.startswith('Session change:')),delta);p.write_text(t)
p=root/'README.md';t=p.read_text().replace('**After S058.** Thirty-two frozen theorem bundles (not thirty-two solved material classes).','**After S059.** Thirty-three frozen theorem bundles (not thirty-three solved material classes).').replace('- Next: S059, separate own-source freeze of exact raw threshold exclusion.','- Next: S060, select the next concrete terminal/history prerequisite.');t+='\n- S059: EC-C035 frozen as [EC-T0033](theorems/frozen/EC-T0033/v1.md), complete characterization module immutable; separate own-source Gate Z passed. [Evidence](theorems/frozen/VERIFICATION-S059/README.md).\n';p.write_text(t)
p=root/'docs/ROADMAP.md';p.write_text(p.read_text().replace('S059 separate freeze next.','S059 froze this as EC-T0033 after new own-source Gate Z, 33 bundles; S060 reviews the next concrete terminal/history prerequisite.'))
p=root/'theorems/README.md';t=p.read_text().replace('EC-T0007–EC-T0032 were first frozen','EC-T0007–EC-T0033 were first frozen').replace('Current frozen count: **32 bundles**, not thirty-two solved','Current frozen count: **33 bundles**, not thirty-three solved');t+='\n- [EC-T0033](frozen/EC-T0033/v1.md): exact raw current and every intended threshold exclusion, S059 exact-source freeze. [Evidence](frozen/VERIFICATION-S059/README.md).\n';p.write_text(t)
(out/'README.md').write_text(f'''# S059 — Raw threshold exclusion certificate Gate Z

{result}

{checks}

{limits}

Reproduce: `python theorems/frozen/VERIFICATION-S059/reproduction/verify.py REPO_ROOT NEW_OUTPUT NEW_CLONE {sha}`
Validate: `python theorems/frozen/VERIFICATION-S059/reproduction/validate.py REPO_ROOT`.
''')
table='\n'.join(l for l in (root/'docs/SESSION_PROGRESS.md').read_text().splitlines() if l.startswith('|'));prompt=(root/'NEXT_SESSION.md').read_text().strip()
(root/'sessions/S059_FREEZE_EXACT_RAW_THRESHOLD_EXCLUSION.md').write_text(f'''# S059 — Freeze exact raw threshold exclusion characterization

2026-10-20, base main 1ff410bb4f2c92f25ca24cf1fab4fc791e28e02a,
branch session/s059-freeze-exact-raw-threshold-exclusion. Explicit all-heads fetch,
no prior unmerged work, existing checkout; owner authorises consecutive sessions
and publication. EC-C035 frozen as EC-T0033; 33 bundles, no class coverage upgrade.

## Exact result and fidelity

{scope}

Both complete modules frozen unchanged; paper/Lean/evidence fidelity reviewed.
[Review](../theorems/frozen/VERIFICATION-S059/fidelity-review.md).

{limits}

## Observed verification and publication

{result}

{checks}

[Evidence](../theorems/frozen/VERIFICATION-S059/README.md). Own source published
before clean clone. Commit/push branch, merge/push main and compare remote SHAs;
final identities retained in Git/observed publication checks. Continue S060 under
standing owner authorisation until told to stop.

## Required progress table

{table}

{delta}

## Full installed S060 prompt

{prompt}
''')
p=root/'sessions/SESSION_LEDGER.md';t=p.read_text().replace('Full session closeouts live','| S059 | 2026-10-20 | Freeze EC-C035 raw threshold exclusion (Gate Z) | New own-source 84-job build, 282 allowed reports; complete characterization module frozen. [Closeout](S059_FREEZE_EXACT_RAW_THRESHOLD_EXCLUSION.md) | **+1 → EC-T0033 FROZEN** (33 bundles) |\n\nFull session closeouts live');p.write_text(t)
print(result)
