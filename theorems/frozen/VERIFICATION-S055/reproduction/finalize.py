"""Freeze concrete count law only after observed own-source Gate Z."""
import csv,io,json
from pathlib import Path
root=Path(__file__).resolve().parents[4];out=root/'theorems/frozen/VERIFICATION-S055';s=json.loads((out/'summary.json').read_text())
sha=s['proof_source'];assert sha=='9fccb2f46c0edcd358c25885b1f4cdae0f770233';assert s['build_exit']==s['axiom_statement_exit']==0
assert (out/'axioms-statements.log').read_bytes()==(root/'sessions/evidence/S054/axioms-statements.log').read_bytes()
result=f"Own source `{sha}`; NEW GitHub clone `{s['fresh_clone']}`, no .lake before build. Full {s['build_jobs']}-job build exit 0 in {s['build_seconds']}s; COMPLETE AxiomCheck exit 0 at {s['verified_utc']}; {s['total_axiom_reports']} allowed reports. Main standard-three; whole report identical to S054 Gate F."
name=s['bundle_declarations'][0];log=(out/'axioms-statements.log').read_text();statement=name+' :'+log.split(name+' :')[1]
scope='''For every raw State s, actual Move m and legality proof hm, currentOccurrences
of actual append equals old FULL history count queried at NEW endpoint plusone.
Concrete wrappers use frozen full normalized key and SAME local classical equality.
Root/prior/current retained, no reset truncation or old-current-plus-one shortcut.
Actual indexed trace/hm unchanged. Frozen generic append law and reflexive new-key
indicator=1. Both colours/all flags/promotions/castling/EP/every actual legal reply;
no history/material/terminal/strategy filter or artificial moves without hm.'''
checks='''Every formal byte matches own anchor/current source; full source/transitive
SHA256, clean HEAD/tree/status and full logs/commands/exits/times/UTC/toolchain
retained. Official core Lean4.35.0 release eb6cafb7290e8bd5f2937522d8d804f58f02bafc,
no dependencies/shim/TLS/checksum change. Hosted CI unobserved. One new successful
clean run, no failure/repeated build; no source edit/incremental build. Relevant
ledger structure/tests, preservation/evidence/full-table/full-prompt/local-link/
diff checks passed; prior protected source/papers/audits/evidence/manifests and30
rows unchanged, exactly EC-T0031 appended. No unrelated diagnostics/trivial tests.'''
limits='''No full FIDE key/Article9.2.3/rights-history identity, repetition threshold/claim,
no-earlier-terminal histories, automatic-draw/mate precedence adjudication,
strategy lifting, numerical KRK, holding/outcome, WDL/DTZ/Syzygy or initial value.
Same-agent review, not independent external audit. Symbolic [A,B,A] thenB control,
not a compatible actual chess-game run. No enumeration/oracle/stored certificate,
executable hash/search or novelty claim.'''
sources='\n'.join(f'### {p}\n\n```lean\n{(root/p).read_text()}```\n' for p in s['complete_modules'])
p=root/'theorems/frozen/EC-T0031/v1.md';assert not p.exists();p.parent.mkdir();p.write_text(f'''# EC-T0031 v1 — Current normalized-key count after actual append

**FROZEN S055, 2026-10-20**, candidate EC-C033.
Own proof-source `{sha}`; main `{name}`.

{scope}

BOTH complete OccurrenceDefinitions and CurrentAppend below immutable; prior
frozen imports unchanged. Trust official Lean kernel, standard-three axioms, A1
and existing owner-reviewed FIDE2023 legal-move encoding. No new full FIDE bridge.
[Paper](../../../proofs/EC-C033_NORMALIZED_KEY_OCCURRENCES.md),
[paper audit](../../../audits/EC-C033_OCCURRENCES_PAPER.md),
[Lean audit](../../../audits/EC-C033_OCCURRENCES_LEAN.md),
[freeze fidelity](../VERIFICATION-S055/fidelity-review.md).

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

[Evidence](../VERIFICATION-S055/README.md).

## Transitive SHA256

```text
{(out/'dependency-sha256.txt').read_text()}```
''')
p=root/'theorems/LEDGER.csv';old=p.read_bytes();rows=list(csv.DictReader(io.StringIO(old.decode())));assert len(rows)==30;fields=list(rows[0]);row=dict(zip(fields,['EC-T0031','Current normalized-key occurrence count after actual legal append','theorems/frozen/EC-T0031/v1.md','proofs/EC-C033_NORMALIZED_KEY_OCCURRENCES.md','formal/EndgameChess/Rules/RawRepetition/CurrentAppend.lean',name,'leanprover/lean4:v4.35.0',sha,s['verified_utc'],'FIDE Laws of Chess 2023 legal-move kernel; concrete raw normalized-key count only','theorems/frozen/EC-T0031/v1.md','FROZEN','From EC-C033. New own-source Gate Z; complete OccurrenceDefinitions/CurrentAppend frozen. New current count equals old full history queried at NEW endpoint plus one. Standard three axioms. No full FIDE identity/threshold/adjudication or numerical KRK claim.']));b=io.StringIO(newline='');csv.DictWriter(b,fieldnames=fields,lineterminator='\n').writerow(row);p.write_bytes(old+b.getvalue().encode())
p=root/'research/CANDIDATES.md';p.write_text(p.read_text().replace('FORMAL_VERIFIED (S054, 2026-10-20); Gate Z pending','**FROZEN as [EC-T0031](../theorems/frozen/EC-T0031/v1.md)** (S055, 2026-10-20)'))
p=root/'docs/SESSION_PROGRESS.md';t=p.read_text().replace('through S054. Thirty','through S055. Thirty-one').replace('these are not thirty solved','these are not thirty-one solved').replace('normalization/key-congruence prerequisites frozen; concrete count law formally verified','normalization/key/count prerequisites frozen');delta='Session change: S055 froze the current normalized-key count append law as EC-T0031 after a new exact-source Gate Z check; 31 bundles are frozen and material-class coverage is unchanged.';t=t.replace(next(l for l in t.splitlines() if l.startswith('Session change:')),delta);p.write_text(t)
p=root/'README.md';t=p.read_text().replace('**After S054.** Thirty frozen theorem bundles (not thirty solved material classes).','**After S055.** Thirty-one frozen theorem bundles (not thirty-one solved material classes).').replace('- Next: S055, separate exact-source freeze of the normalized-key count law.','- Next: S056, raw current/intended threshold exclusion certificate.');t+='\n- S055: EC-C033 frozen as [EC-T0031](theorems/frozen/EC-T0031/v1.md), both count modules immutable; separate own-source Gate Z passed. [Evidence](theorems/frozen/VERIFICATION-S055/README.md).\n';p.write_text(t)
p=root/'docs/ROADMAP.md';p.write_text(p.read_text().replace('S055 separate freeze next.','S055 froze this as EC-T0031 after new own-source Gate Z, 31 bundles; S056 targets a raw current/intended threshold exclusion certificate.'))
p=root/'theorems/README.md';t=p.read_text().replace('EC-T0007–EC-T0030 were first frozen','EC-T0007–EC-T0031 were first frozen').replace('Current frozen count: **30 bundles**, not thirty solved','Current frozen count: **31 bundles**, not thirty-one solved');t+='\n- [EC-T0031](frozen/EC-T0031/v1.md): concrete current normalized-key count after actual append, S055 exact-source freeze. [Evidence](frozen/VERIFICATION-S055/README.md).\n';p.write_text(t)
(out/'README.md').write_text(f'''# S055 — Current normalized-key count Gate Z

{result}

{checks}

{limits}

Reproduce: `python theorems/frozen/VERIFICATION-S055/reproduction/verify.py REPO_ROOT NEW_OUTPUT NEW_CLONE {sha}`
Validate: `python theorems/frozen/VERIFICATION-S055/reproduction/validate.py REPO_ROOT`.
''')
table='\n'.join(l for l in (root/'docs/SESSION_PROGRESS.md').read_text().splitlines() if l.startswith('|'));prompt=(root/'NEXT_SESSION.md').read_text().strip()
(root/'sessions/S055_FREEZE_NORMALIZED_KEY_OCCURRENCES.md').write_text(f'''# S055 — Freeze current normalized-key count law

2026-10-20, base main 6d486105667638870e22ffc666897fce5f53025c,
branch session/s055-freeze-normalized-key-occurrences. Explicit all-heads fetch,
no prior unmerged work, existing checkout; owner authorises consecutive sessions
and publication. EC-C033 frozen as EC-T0031; 31 bundles, no class coverage upgrade.

## Exact result and fidelity

{scope}

Both complete modules frozen unchanged; paper/Lean/evidence fidelity reviewed.
[Review](../theorems/frozen/VERIFICATION-S055/fidelity-review.md).

{limits}

## Observed verification and publication

{result}

{checks}

[Evidence](../theorems/frozen/VERIFICATION-S055/README.md). Own source published
before clean clone. Commit/push branch, merge/push main and compare remote SHAs;
final identities retained in Git/observed publication checks. Continue S056 under
standing owner authorisation until told to stop.

## Required progress table

{table}

{delta}

## Full installed S056 prompt

{prompt}
''')
p=root/'sessions/SESSION_LEDGER.md';t=p.read_text().replace('Full session closeouts live','| S055 | 2026-10-20 | Freeze EC-C033 current normalized-key count (Gate Z) | New own-source 81-job build, 280 allowed reports; both complete modules frozen. [Closeout](S055_FREEZE_NORMALIZED_KEY_OCCURRENCES.md) | **+1 → EC-T0031 FROZEN** (31 bundles) |\n\nFull session closeouts live');p.write_text(t)
print(result)
