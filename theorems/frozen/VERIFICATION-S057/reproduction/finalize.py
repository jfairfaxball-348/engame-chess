"""Freeze raw threshold certificate only after observed own-source Gate Z."""
import csv,io,json
from pathlib import Path
root=Path(__file__).resolve().parents[4];out=root/'theorems/frozen/VERIFICATION-S057';s=json.loads((out/'summary.json').read_text())
sha=s['proof_source'];assert sha=='1f262968c80a1352c156f6e0c07dd5132c432b13';assert s['build_exit']==s['axiom_statement_exit']==0
assert (out/'axioms-statements.log').read_bytes()==(root/'sessions/evidence/S056/axioms-statements.log').read_bytes()
result=f"Own source `{sha}`; NEW GitHub clone `{s['fresh_clone']}`, no .lake before build. Full {s['build_jobs']}-job build exit 0 in {s['build_seconds']}s; COMPLETE AxiomCheck exit 0 at {s['verified_utc']}; {s['total_axiom_reports']} allowed reports. Main standard-three; whole report identical to S056 Gate F."
name=s['bundle_declarations'][0];log=(out/'axioms-statements.log').read_text();statement=name+' :'+log.split(name+' :')[1]
scope='''For every raw state s, explicit root clock+1<100, root currentcount<3 and
EVERY actual legal intended new-key OLD-history query<2 imply no raw
AvailableThreshold. CurrentThreshold is root clock>=100 OR currentcount>=3;
IntendedThreshold existentially quantifies every actual legal append with a child
CurrentThreshold. Root arithmetic and frozen actual clock/count append laws
exclude both root and every child threshold. All indexed traces/hm/colours/flags/
promotions retained, no terminal/material/history/strategy restriction.
Raw predicates NOT certified FIDE CanClaim/adjudication; frozen Layer unchanged.'''
checks='''Every formal byte matches own anchor/current source; full source/transitive
SHA256, clean HEAD/tree/status and full logs/commands/exits/times/UTC/toolchain
retained. Official core Lean4.35.0 release eb6cafb7290e8bd5f2937522d8d804f58f02bafc,
no dependencies/shim/TLS/checksum change. Hosted CI unobserved. One new successful
clean run, no failure/repeated build; no source edit/incremental build. Relevant
ledger structure/tests, preservation/evidence/full-table/full-prompt/local-link/
diff checks passed; prior protected source/papers/audits/evidence/manifests and31
rows unchanged, exactly EC-T0032 appended. No unrelated diagnostics/trivial tests.'''
limits='''No full FIDE key/Article9.2.3/rights-history identity, repetition threshold/claim,
no-earlier-terminal histories, automatic-draw/mate precedence adjudication,
strategy lifting, numerical KRK, holding/outcome, WDL/DTZ/Syzygy or initial value.
Same-agent review, not independent external audit. Symbolic threshold99/100,2/3/zeroing/no-reply/pseudo-only controls,
not a compatible actual chess-game run. No enumeration/oracle/stored certificate,
executable hash/search or novelty claim.'''
sources='\n'.join(f'### {p}\n\n```lean\n{(root/p).read_text()}```\n' for p in s['complete_modules'])
p=root/'theorems/frozen/EC-T0032/v1.md';assert not p.exists();p.parent.mkdir();p.write_text(f'''# EC-T0032 v1 — Raw current and intended threshold exclusion

**FROZEN S057, 2026-10-20**, candidate EC-C034.
Own proof-source `{sha}`; main `{name}`.

{scope}

BOTH complete RawClaims.Definitions and RawClaims.Certificate below immutable; prior
frozen imports unchanged. Trust official Lean kernel, standard-three axioms, A1
and existing owner-reviewed FIDE2023 legal-move encoding. No new full FIDE bridge.
[Paper](../../../proofs/EC-C034_RAW_THRESHOLD_CERTIFICATE.md),
[paper audit](../../../audits/EC-C034_THRESHOLD_PAPER.md),
[Lean audit](../../../audits/EC-C034_THRESHOLD_LEAN.md),
[freeze fidelity](../VERIFICATION-S057/fidelity-review.md).

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

[Evidence](../VERIFICATION-S057/README.md).

## Transitive SHA256

```text
{(out/'dependency-sha256.txt').read_text()}```
''')
p=root/'theorems/LEDGER.csv';old=p.read_bytes();rows=list(csv.DictReader(io.StringIO(old.decode())));assert len(rows)==31;fields=list(rows[0]);row=dict(zip(fields,['EC-T0032','Raw current and every legal intended threshold exclusion certificate','theorems/frozen/EC-T0032/v1.md','proofs/EC-C034_RAW_THRESHOLD_CERTIFICATE.md','formal/EndgameChess/Rules/RawClaims/Certificate.lean',name,'leanprover/lean4:v4.35.0',sha,s['verified_utc'],'FIDE Laws of Chess 2023 legal-move kernel; raw clock/repetition threshold certificate only','theorems/frozen/EC-T0032/v1.md','FROZEN','From EC-C034. New own-source Gate Z; complete RawClaims.Definitions/Certificate frozen. Explicit root/ALL intended-child budgets exclude raw threshold availability. Standard three axioms. No full FIDE identity/threshold/adjudication or numerical KRK claim.']));b=io.StringIO(newline='');csv.DictWriter(b,fieldnames=fields,lineterminator='\n').writerow(row);p.write_bytes(old+b.getvalue().encode())
p=root/'research/CANDIDATES.md';p.write_text(p.read_text().replace('FORMAL_VERIFIED (S056, 2026-10-20); Gate Z pending','**FROZEN as [EC-T0032](../theorems/frozen/EC-T0032/v1.md)** (S057, 2026-10-20)'))
p=root/'docs/SESSION_PROGRESS.md';t=p.read_text().replace('through S056. Thirty-one','through S057. Thirty-two').replace('these are not thirty-one solved','these are not thirty-two solved').replace('normalization/key/count prerequisites frozen; raw threshold certificate formally verified','normalization/key/count and raw threshold prerequisites frozen');delta='Session change: S057 froze the raw threshold exclusion certificate as EC-T0032 after a new exact-source Gate Z check; 32 bundles are frozen and material-class coverage is unchanged.';t=t.replace(next(l for l in t.splitlines() if l.startswith('Session change:')),delta);p.write_text(t)
p=root/'README.md';t=p.read_text().replace('**After S056.** Thirty-one frozen theorem bundles (not thirty-one solved material classes).','**After S057.** Thirty-two frozen theorem bundles (not thirty-two solved material classes).').replace('- Next: S057, separate exact-source freeze of the raw threshold certificate.','- Next: S058, exact raw threshold exclusion characterization.');t+='\n- S057: EC-C034 frozen as [EC-T0032](theorems/frozen/EC-T0032/v1.md), both raw threshold modules immutable; separate own-source Gate Z passed. [Evidence](theorems/frozen/VERIFICATION-S057/README.md).\n';p.write_text(t)
p=root/'docs/ROADMAP.md';p.write_text(p.read_text().replace('S057 separate freeze next.','S057 froze this as EC-T0032 after new own-source Gate Z, 32 bundles; S058 targets exact raw threshold exclusion characterization.'))
p=root/'theorems/README.md';t=p.read_text().replace('EC-T0007–EC-T0031 were first frozen','EC-T0007–EC-T0032 were first frozen').replace('Current frozen count: **31 bundles**, not thirty-one solved','Current frozen count: **32 bundles**, not thirty-two solved');t+='\n- [EC-T0032](frozen/EC-T0032/v1.md): raw current and every intended threshold exclusion, S057 exact-source freeze. [Evidence](frozen/VERIFICATION-S057/README.md).\n';p.write_text(t)
(out/'README.md').write_text(f'''# S057 — Raw threshold exclusion certificate Gate Z

{result}

{checks}

{limits}

Reproduce: `python theorems/frozen/VERIFICATION-S057/reproduction/verify.py REPO_ROOT NEW_OUTPUT NEW_CLONE {sha}`
Validate: `python theorems/frozen/VERIFICATION-S057/reproduction/validate.py REPO_ROOT`.
''')
table='\n'.join(l for l in (root/'docs/SESSION_PROGRESS.md').read_text().splitlines() if l.startswith('|'));prompt=(root/'NEXT_SESSION.md').read_text().strip()
(root/'sessions/S057_FREEZE_RAW_THRESHOLD_CERTIFICATE.md').write_text(f'''# S057 — Freeze raw threshold exclusion certificate

2026-10-20, base main e475d700baafa5b9ed71a2a7b23be3c7f71a745c,
branch session/s057-freeze-raw-threshold-certificate. Explicit all-heads fetch,
no prior unmerged work, existing checkout; owner authorises consecutive sessions
and publication. EC-C034 frozen as EC-T0032; 32 bundles, no class coverage upgrade.

## Exact result and fidelity

{scope}

Both complete modules frozen unchanged; paper/Lean/evidence fidelity reviewed.
[Review](../theorems/frozen/VERIFICATION-S057/fidelity-review.md).

{limits}

## Observed verification and publication

{result}

{checks}

[Evidence](../theorems/frozen/VERIFICATION-S057/README.md). Own source published
before clean clone. Commit/push branch, merge/push main and compare remote SHAs;
final identities retained in Git/observed publication checks. Continue S058 under
standing owner authorisation until told to stop.

## Required progress table

{table}

{delta}

## Full installed S058 prompt

{prompt}
''')
p=root/'sessions/SESSION_LEDGER.md';t=p.read_text().replace('Full session closeouts live','| S057 | 2026-10-20 | Freeze EC-C034 raw threshold exclusion (Gate Z) | New own-source 83-job build, 281 allowed reports; both complete modules frozen. [Closeout](S057_FREEZE_RAW_THRESHOLD_CERTIFICATE.md) | **+1 → EC-T0032 FROZEN** (32 bundles) |\n\nFull session closeouts live');p.write_text(t)
print(result)
