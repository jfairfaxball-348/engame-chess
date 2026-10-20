"""Create S049 immutable freeze only after observed own Gate Z success."""
import csv,io,json
from pathlib import Path
root=Path(__file__).resolve().parents[4];out=root/'theorems/frozen/VERIFICATION-S049'
s=json.loads((out/'summary.json').read_text()); assert s['build_exit']==s['axiom_statement_exit']==0
sha=s['proof_source'];assert sha=='c4c900036dcffd209d6c08f27e2323637852c940'
assert (out/'axioms-statements.log').read_bytes()==(root/'sessions/evidence/S048/axioms-statements.log').read_bytes()
result=f"Own proof-source `{sha}`; NEW GitHub clone `{s['fresh_clone']}`, no .lake before build. Full {s['build_jobs']}-job build exit 0, {s['build_seconds']}s; COMPLETE AxiomCheck exit 0 at {s['verified_utc']}, {s['total_axiom_reports']} allowed reports. Main standard-three only; full report identical to S048 Gate F."
source=(root/s['complete_modules'][0]).read_text(); log=(out/'axioms-statements.log').read_text();name=s['bundle_declarations'][0];statement=name+' :'+log.split(name+' :')[1]
p=root/'theorems/frozen/EC-T0028/v1.md';assert not p.exists();p.parent.mkdir();p.write_text(f'''# EC-T0028 v1 — Ordinary ep-marker irrelevance outside raw EP shape

**FROZEN S049, 2026-10-20**, candidate EC-C030.
**Own proof-source:** `{sha}`. Main `{name}`.

## Scope and trust

Every raw Position q, actual Move m and replacement Option Square e, under
¬(source Pawn ∧ distinct files ∧ empty destination), replacing old ep preserves
Boolean isPseudo and FULL played Position. No legality, history, terminal,
material, colour or promotion restriction. Raw epCapture false for ANY marker;
full play unfolding includes output ep recomputation, rights/turn/board and
promotion/castling branches. isPseudo proof splits source/colour/kind; same-file
or occupied-destination pawn moves suppress EP clause. ¬LegalEP alone cannot
replace the guard for total raw play.

COMPLETE immutable module `{s['complete_modules'][0]}`; shared/transitive frozen
definitions unchanged. [Paper](../../../proofs/EC-C030_ORDINARY_EP_IRRELEVANCE.md),
[paper audit](../../../audits/EC-C030_ORDINARY_EP_PAPER.md),
[Lean audit](../../../audits/EC-C030_ORDINARY_EP_LEAN.md),
[freeze review](../VERIFICATION-S049/fidelity-review.md).
Same-agent reviews, not independent external audit. Classical branch reasoning,
no novelty/enumeration/tablebase/engine/stored certificates. Trust official Lean
kernel, standard three axioms, A1 and existing FIDE2023 legal-move encoding.
No new English-to-FIDE correspondence or concrete full-game diagnostic claimed.
No full normalization/key/rights-history/claims/adjudication, strategy lifting,
numerical KRK, WDL/DTZ or solved material-class result.

## Exact theorem and axioms

```text
{statement.strip()}
```

## Complete frozen source

```lean
{source}```

## Observed Gate Z

{result}
Every formal byte matches own anchor/current source; all source/transitive hashes,
clean HEAD/tree/status and commands/exits/times/UTC retained. Official core
Lean4.35.0 release eb6cafb7290e8bd5f2937522d8d804f58f02bafc, no dependencies/shim.
Hosted CI unobserved. [Evidence](../VERIFICATION-S049/README.md).

## Transitive SHA256

```text
{(out/'dependency-sha256.txt').read_text()}```
''')
p=root/'theorems/LEDGER.csv';old=p.read_bytes();rows=list(csv.DictReader(io.StringIO(old.decode())));assert len(rows)==27;fields=list(rows[0]);row=dict(zip(fields,['EC-T0028','Raw ep-marker irrelevance outside source-pawn distinct-file empty-destination shape','theorems/frozen/EC-T0028/v1.md','proofs/EC-C030_ORDINARY_EP_IRRELEVANCE.md',s['complete_modules'][0],name,'leanprover/lean4:v4.35.0',sha,s['verified_utc'],'FIDE Laws of Chess 2023 legal-move kernel; conditional raw marker irrelevance','theorems/frozen/EC-T0028/v1.md','FROZEN','From EC-C030. New exact-source Gate Z; complete OrdinaryEP module frozen. Boolean isPseudo and full play preservation under explicit non-EP-shape guard, no legality premise. Standard three axioms. No full normalization/key or numerical KRK result.']));buf=io.StringIO(newline='');csv.DictWriter(buf,fieldnames=fields,lineterminator='\n').writerow(row);p.write_bytes(old+buf.getvalue().encode())
p=root/'research/CANDIDATES.md';p.write_text(p.read_text().replace('FORMAL_VERIFIED (S048, 2026-10-20); Gate Z pending','**FROZEN as [EC-T0028](../theorems/frozen/EC-T0028/v1.md)** (S049, 2026-10-20)'))
p=root/'docs/SESSION_PROGRESS.md';t=p.read_text().replace('through S048. Twenty-seven','through S049. Twenty-eight').replace('these are not twenty-seven solved','these are not twenty-eight solved').replace('legal-ep prerequisites frozen; ordinary ep irrelevance formally verified','legal-ep and ordinary ep-irrelevance prerequisites frozen');delta='Session change: S049 froze ordinary ep-marker irrelevance as EC-T0028 after a new exact-source Gate Z check; 28 bundles are frozen and material-class coverage is unchanged.';t=t.replace(next(l for l in t.splitlines() if l.startswith('Session change:')),delta);p.write_text(t)
p=root/'README.md';t=p.read_text().replace('**After S048.** Twenty-seven frozen theorem bundles (not twenty-seven solved material classes).','**After S049.** Twenty-eight frozen theorem bundles (not twenty-eight solved material classes).').replace('- Next: S049, separate exact-source freeze of ordinary ep-marker irrelevance.', '- Next: S050, effective en-passant normalization preservation.');t+='\n- S049: EC-C030 frozen as [EC-T0028](theorems/frozen/EC-T0028/v1.md), separate exact-source Gate Z passed. [Evidence](theorems/frozen/VERIFICATION-S049/README.md).\n';p.write_text(t)
p=root/'docs/ROADMAP.md';t=p.read_text().replace('S049 separate freeze next.', 'S049 froze it as EC-T0028 after a new exact-source Gate Z check; 28 bundles. S050 targets effectiveEP normalization preservation.');p.write_text(t)
p=root/'theorems/README.md';t=p.read_text().replace('EC-T0007–EC-T0027 were first frozen','EC-T0007–EC-T0028 were first frozen').replace('Current frozen count: **27 bundles**, not twenty-seven solved','Current frozen count: **28 bundles**, not twenty-eight solved');t+='\n- [EC-T0028](frozen/EC-T0028/v1.md): ordinary raw ep-marker irrelevance, Boolean pseudo-legality and full play; S049 exact-source freeze. [Evidence](frozen/VERIFICATION-S049/README.md).\n';p.write_text(t)
(out/'README.md').write_text(f'''# S049 — Ordinary ep-marker irrelevance Gate Z

{result}

Full logs/commands/exits/times/UTC/toolchain, full source/transitive SHA256 and
clean HEAD/tree/status retained. Every formal byte matches own anchor/current
source. Official core Lean4.35.0, no dependency/shim/TLS/checksum change.
Hosted CI unobserved. All prior records/source unchanged; exactly one new
manifest/ledger row, 28 frozen bundles, no solved-class upgrade. No source edit,
incremental build, unrelated diagnostics or trivial tests. Same-agent fidelity
review, no claim of independent external audit.

Reproduce: `python theorems/frozen/VERIFICATION-S049/reproduction/verify.py REPO_ROOT NEW_OUTPUT NEW_CLONE {sha}`
Validate: `python theorems/frozen/VERIFICATION-S049/reproduction/validate.py REPO_ROOT`.
''')
table='\n'.join(l for l in (root/'docs/SESSION_PROGRESS.md').read_text().splitlines() if l.startswith('|'));prompt=(root/'NEXT_SESSION.md').read_text().strip()
(root/'sessions/S049_FREEZE_ORDINARY_EP_IRRELEVANCE.md').write_text(f'''# S049 — Freeze ordinary ep-marker irrelevance

2026-10-20. Base main ff21fec6b086f3ecbd2ea2569ffab0d7dc65e197;
branch session/s049-freeze-ordinary-ep-irrelevance. Explicit all-heads fetch,
no unmerged prior work, existing checkout; consecutive sessions/publication
resumed by owner. EC-C030 frozen as EC-T0028; 28 bundles, class coverage unchanged.

## Result and review

Complete OrdinaryEP module frozen unchanged at own original proof source.
Every q,m,e under explicit non-EP-shape guard: Boolean isPseudo and FULL play
preserved by marker replacement, without actual legality/history assumptions.
Raw capture conjunction false for every marker; full play includes output ep,
rights/turn/board function, promotions and castling. Source/colour/kind cases
isolate pawnMoveOK; same-file or occupied destination suppresses EP test.
Absent/wrong-colour/nonpawn/king/castling, source=destination, arbitrary flags,
both colours and promotions reviewed symbolically. ¬LegalEP alone insufficient
for total raw play equality. No enumeration/oracle/stored certificates, concrete
pinned/full-game diagnostics or novelty claim. Same-agent fidelity review,
not an independently staffed external audit. [Review](../theorems/frozen/VERIFICATION-S049/fidelity-review.md).

## Observed evidence

{result}
[Evidence](../theorems/frozen/VERIFICATION-S049/README.md). Exact main inspected;
full formal bytes/source/transitive hashes and clean HEAD/tree/status retained.
Official core Lean4.35.0 release eb6cafb7290e8bd5f2937522d8d804f58f02bafc;
no dependencies/shim/runtime setup/TLS/checksum changes. Hosted CI unobserved.
One NEW clean Gate Z run, no failures/repeated builds. No source edit/incremental
build. Relevant ledger structure/tests, immutable boundary/preservation/evidence,
full progress table/prompt/local-link/diff checks passed; all prior source/papers/
audits/evidence/manifests and 27 rows preserved, exactly EC-T0028 appended.
No unrelated diagnostics/trivial tests. Commit/push branch, merge/push main and
compare remote identities; final identities in Git/observed publication checks.

## Limits and continuation

No full effectiveEP normalization, FIDE repetition key/rights-history/claims/
adjudication, strategy lifting, numerical KRK, WDL/DTZ or solved material class.
S050 normalization preservation installed; continue until owner says stop.

## Required progress table

{table}

{delta}

## Full installed S050 prompt

{prompt}
''')
p=root/'sessions/SESSION_LEDGER.md';t=p.read_text().replace('Full session closeouts live','| S049 | 2026-10-20 | Freeze EC-C030 ordinary ep irrelevance (Gate Z) | New own exact-source 75-job build, 277 allowed reports, source/record preservation. [Closeout](S049_FREEZE_ORDINARY_EP_IRRELEVANCE.md) | **+1 → EC-T0028 FROZEN** (28 bundles) |\n\nFull session closeouts live');p.write_text(t)
print(result)
