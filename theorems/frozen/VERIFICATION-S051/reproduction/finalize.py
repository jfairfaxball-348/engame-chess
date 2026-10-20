"""Freeze EC-C031 only after own-source Gate Z success."""
import csv,io,json
from pathlib import Path
root=Path(__file__).resolve().parents[4];out=root/'theorems/frozen/VERIFICATION-S051';s=json.loads((out/'summary.json').read_text())
sha=s['proof_source'];assert sha=='4d47b33549fc5286099cae0bd89de76b05fbeb42';assert s['build_exit']==s['axiom_statement_exit']==0
assert (out/'axioms-statements.log').read_bytes()==(root/'sessions/evidence/S050/axioms-statements.log').read_bytes()
result=f"Own proof-source `{sha}`; NEW GitHub clone `{s['fresh_clone']}`, no .lake before build. Full {s['build_jobs']}-job build exit 0 in {s['build_seconds']}s; COMPLETE AxiomCheck exit 0 at {s['verified_utc']}, {s['total_axiom_reports']} allowed reports. Main standard-three; entire report identical to S050 Gate F."
name=s['bundle_declarations'][0];log=(out/'axioms-statements.log').read_text();statement=name+' :'+log.split(name+' :')[1]
scope='''For every raw Position q and actual Move m, effective ep normalization preserves
Boolean isLegal, and for actual original legal moves preserves the FULL played
Position. No reachability/history/material/terminal/colour/promotion premise.
Available legal EP witness gives normalization identity. Without witness, ordinary
moves use frozen ep irrelevance plus same-turn self-check; EP-shaped moves are
illegal originally by frozen characterization, normalized pseudo false by nonzero
dx, empty dst and none marker. No equality of illegal raw EP endpoints asserted.
No adverse legal reply pruning or replacement of actual self-check legality.'''
sources='\n'.join(f'### {p}\n\n```lean\n{(root/p).read_text()}```\n' for p in s['complete_modules'])
p=root/'theorems/frozen/EC-T0029/v1.md';assert not p.exists();p.parent.mkdir();p.write_text(f'''# EC-T0029 v1 — Effective ep normalization preserves legal play

**FROZEN S051, 2026-10-20**, candidate EC-C031.
**Own proof-source:** `{sha}`. Main `{name}`.

## Exact scope and trust

{scope}

BOTH complete NormalizationDefinitions and Normalization modules below are
immutable, including shared normalizeEP. All prior imported frozen sources
unchanged. Corrections require new module/version, no silent edits.
[Paper](../../../proofs/EC-C031_EFFECTIVE_EP_NORMALIZATION.md),
[paper audit](../../../audits/EC-C031_NORMALIZATION_PAPER.md),
[Lean audit](../../../audits/EC-C031_NORMALIZATION_LEAN.md),
[freeze fidelity](../VERIFICATION-S051/fidelity-review.md).
Same-agent review, not independent external audit. Classical kernel reasoning,
no novelty/coordinate enumeration/engine/tablebase/stored certificate or concrete
full-game diagnostic. Trust official Lean kernel/standard-three axioms, A1 and
existing owner-reviewed FIDE2023 legal-move encoding. No new full English-FIDE
correspondence, lawful histories or arbitrary-flag validity claim.
No full repetition key/rights-history/claims/adjudication/mate precedence,
strategy lifting, numerical KRK, holding/outcome, WDL/DTZ or solved material class.

## Exact theorem and axioms

```text
{statement.strip()}
```

## Complete immutable source boundary

{sources}
## Observed Gate Z

{result}
Every formal byte matches own anchor/current source; full source/transitive hashes,
clean HEAD/tree/status and logs/commands/exits/times/UTC/toolchain retained.
Official core Lean4.35.0 release eb6cafb7290e8bd5f2937522d8d804f58f02bafc,
no dependency/shim/TLS/checksum change. Hosted CI unobserved.
[Evidence](../VERIFICATION-S051/README.md).

## Transitive SHA256

```text
{(out/'dependency-sha256.txt').read_text()}```
''')
p=root/'theorems/LEDGER.csv';old=p.read_bytes();rows=list(csv.DictReader(io.StringIO(old.decode())));assert len(rows)==28;fields=list(rows[0]);row=dict(zip(fields,['EC-T0029','Effective en-passant normalization preserves legality and full legal played endpoints','theorems/frozen/EC-T0029/v1.md','proofs/EC-C031_EFFECTIVE_EP_NORMALIZATION.md','formal/EndgameChess/Rules/RawRepetition/Normalization.lean',name,'leanprover/lean4:v4.35.0',sha,s['verified_utc'],'FIDE Laws of Chess 2023 legal-move kernel; effective ep normalization only','theorems/frozen/EC-T0029/v1.md','FROZEN','From EC-C031. New own-source Gate Z; complete NormalizationDefinitions/Normalization modules frozen. Boolean isLegal equality all raw q,m; full played Position equality for original legal moves. Standard three axioms. No full FIDE key or numerical KRK claim.']));buf=io.StringIO(newline='');csv.DictWriter(buf,fieldnames=fields,lineterminator='\n').writerow(row);p.write_bytes(old+buf.getvalue().encode())
p=root/'research/CANDIDATES.md';p.write_text(p.read_text().replace('FORMAL_VERIFIED (S050, 2026-10-20); Gate Z pending','**FROZEN as [EC-T0029](../theorems/frozen/EC-T0029/v1.md)** (S051, 2026-10-20)'))
p=root/'docs/SESSION_PROGRESS.md';t=p.read_text().replace('through S050. Twenty-eight','through S051. Twenty-nine').replace('these are not twenty-eight solved','these are not twenty-nine solved').replace('legal-ep and ordinary ep-irrelevance prerequisites frozen; normalization formally verified','legal-ep and normalization prerequisites frozen');delta='Session change: S051 froze effective-ep normalization preservation as EC-T0029 after a new exact-source Gate Z check; 29 bundles are frozen and material-class coverage is unchanged.';t=t.replace(next(l for l in t.splitlines() if l.startswith('Session change:')),delta);p.write_text(t)
p=root/'README.md';t=p.read_text().replace('**After S050.** Twenty-eight frozen theorem bundles (not twenty-eight solved material classes).','**After S051.** Twenty-nine frozen theorem bundles (not twenty-nine solved material classes).').replace('- Next: S051, separate exact-source freeze of effective ep normalization.','- Next: S052, normalized-key legal-move congruence.');t+='\n- S051: EC-C031 frozen as [EC-T0029](theorems/frozen/EC-T0029/v1.md), both normalization modules immutable; separate exact-source Gate Z passed. [Evidence](theorems/frozen/VERIFICATION-S051/README.md).\n';p.write_text(t)
p=root/'docs/ROADMAP.md';t=p.read_text().replace('S051 separate freeze next.','S051 froze this as EC-T0029 after new own-source Gate Z, 29 bundles; S052 targets normalized-key congruence.');p.write_text(t)
p=root/'theorems/README.md';t=p.read_text().replace('EC-T0007–EC-T0028 were first frozen','EC-T0007–EC-T0029 were first frozen').replace('Current frozen count: **28 bundles**, not twenty-eight solved','Current frozen count: **29 bundles**, not twenty-nine solved');t+='\n- [EC-T0029](frozen/EC-T0029/v1.md): effective-ep normalization legality/full-legal-endpoint preservation; both modules frozen S051. [Evidence](frozen/VERIFICATION-S051/README.md).\n';p.write_text(t)
(out/'README.md').write_text(f'''# S051 — Effective ep normalization Gate Z

{result}

Both complete new normalization definition/proof modules immutable. Exact main
inspected, all formal bytes match own anchor/current source; full source/transitive
SHA256, clean HEAD/tree/status, full logs/commands/exits/times/UTC/toolchain retained.
Official core Lean4.35.0, no dependency/shim/TLS/checksum change; hosted CI unobserved.
All prior source/records/28 rows preserved, exactly one new manifest/row. No source
edit/incremental build, unrelated diagnostics/trivial tests. Same-agent review,
not independent external audit. No full FIDE key/adjudication or KRK distance result.

Reproduce: `python theorems/frozen/VERIFICATION-S051/reproduction/verify.py REPO_ROOT NEW_OUTPUT NEW_CLONE {sha}`
Validate: `python theorems/frozen/VERIFICATION-S051/reproduction/validate.py REPO_ROOT`.
''')
table='\n'.join(l for l in (root/'docs/SESSION_PROGRESS.md').read_text().splitlines() if l.startswith('|'));prompt=(root/'NEXT_SESSION.md').read_text().strip()
(root/'sessions/S051_FREEZE_EFFECTIVE_EP_NORMALIZATION.md').write_text(f'''# S051 — Freeze effective ep normalization preservation

2026-10-20, base main be6469ea790c453f07663d5690e3ec6d0f0e71fb;
branch session/s051-freeze-effective-ep-normalization. All-heads fetch,
no prior unmerged work, existing checkout. Consecutive sessions/publication
authorised by owner. EC-C031 frozen as EC-T0029, 29 bundles; no class upgrade.

## Result and fidelity

{scope}

Both complete normalization modules frozen unchanged, exact paper and Lean fidelity
reviewed. [Review](../theorems/frozen/VERIFICATION-S051/fidelity-review.md).
Same-agent review, not independent external audit. Both colours, arbitrary flags,
promotions, missing/wrong-colour/nonpawn/king/castling/same-file/occupied/source=
destination/pseudo-only-selfcheck cases reviewed symbolically. No concrete full-game
diagnostic, enumeration/oracle/stored certificate or novelty claim. Initial S050
incremental simp failure and unchanged-statement rewrite correction reviewed.

## Observed evidence

{result}
[Evidence](../theorems/frozen/VERIFICATION-S051/README.md). Full source/transitive
hashes, clean HEAD/tree/status, full logs/commands/exits/times/UTC/toolchain retained.
Every formal byte matches own anchor/current source. Official core Lean4.35.0
release eb6cafb7290e8bd5f2937522d8d804f58f02bafc, no dependencies/shim or setup/
TLS/checksum change. Hosted CI unobserved. One new successful clean run, no repeated
build. No source edit/incremental build. Relevant ledger structure/tests,
preservation/evidence/full-table/full-prompt/local-link/diff checks passed; all
prior protected source/papers/audits/evidence/manifests and 28 rows preserved,
exactly EC-T0029 appended. No unrelated diagnostics/trivial tests.
Commit/push branch, merge/push main and compare remote SHAs; final identities
retained in Git/observed publication checks. Continue S052 unless owner stops.

## Limits and continuation

No full FIDE key/rights-history/claims/adjudication/mate precedence, strategy
lifting, numerical KRK, holding/outcome, WDL/DTZ/Syzygy or initial-position value.
S052 normalized-key congruence prerequisite installed, not a solved-class claim.

## Required progress table

{table}

{delta}

## Full installed S052 prompt

{prompt}
''')
p=root/'sessions/SESSION_LEDGER.md';t=p.read_text().replace('Full session closeouts live','| S051 | 2026-10-20 | Freeze EC-C031 effective ep normalization (Gate Z) | New own-source 77-job build, 278 allowed reports; both complete modules frozen. [Closeout](S051_FREEZE_EFFECTIVE_EP_NORMALIZATION.md) | **+1 → EC-T0029 FROZEN** (29 bundles) |\n\nFull session closeouts live');p.write_text(t)
print(result)
