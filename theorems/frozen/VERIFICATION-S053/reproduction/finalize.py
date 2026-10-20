"""Freeze EC-C032 only after own-source Gate Z success."""
import csv,io,json
from pathlib import Path
root=Path(__file__).resolve().parents[4];out=root/'theorems/frozen/VERIFICATION-S053';s=json.loads((out/'summary.json').read_text())
sha=s['proof_source'];assert sha=='7ada0bfa5731cae92a965a17d56695b4dbd221ef';assert s['build_exit']==s['axiom_statement_exit']==0
assert (out/'axioms-statements.log').read_bytes()==(root/'sessions/evidence/S052/axioms-statements.log').read_bytes()
result=f"Own proof-source `{sha}`; NEW GitHub clone `{s['fresh_clone']}`, no .lake before build. Full {s['build_jobs']}-job build exit 0 in {s['build_seconds']}s; COMPLETE AxiomCheck exit 0 at {s['verified_utc']}, {s['total_axiom_reports']} allowed reports. Main standard-three; entire report identical to S052 Gate F."
name=s['bundle_declarations'][0];log=(out/'axioms-statements.log').read_text();statement=name+' :'+log.split(name+' :')[1]
scope='''For every raw Position q,r under full normalized key equality and every actual
Move m, Boolean legality is equal and FULL played endpoints agree for legal q
moves. key := normalizeEP, exact normalized board/turn/castling/effective-target
record equality. Frozen normalization preservation twice, congrArg at normalized
identity, legality at r obtained before its full endpoint clause. No raw illegal
endpoint equality, board-only/hash premise, converse/FIDE identity iff, history/
material/terminal/colour/promotion restriction or adverse reply pruning.'''
sources='\n'.join(f'### {p}\n\n```lean\n{(root/p).read_text()}```\n' for p in s['complete_modules'])
p=root/'theorems/frozen/EC-T0030/v1.md';assert not p.exists();p.parent.mkdir();p.write_text(f'''# EC-T0030 v1 — Normalized-key congruence preserves legal play

**FROZEN S053, 2026-10-20**, candidate EC-C032.
**Own proof-source:** `{sha}`. Main `{name}`.

## Exact scope and trust

{scope}

BOTH complete KeyDefinitions and KeyCongruence modules below are
immutable, including shared key. All prior imported frozen sources
unchanged. Corrections require new module/version, no silent edits.
[Paper](../../../proofs/EC-C032_NORMALIZED_KEY_CONGRUENCE.md),
[paper audit](../../../audits/EC-C032_KEY_CONGRUENCE_PAPER.md),
[Lean audit](../../../audits/EC-C032_KEY_CONGRUENCE_LEAN.md),
[freeze fidelity](../VERIFICATION-S053/fidelity-review.md).
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
[Evidence](../VERIFICATION-S053/README.md).

## Transitive SHA256

```text
{(out/'dependency-sha256.txt').read_text()}```
''')
p=root/'theorems/LEDGER.csv';old=p.read_bytes();rows=list(csv.DictReader(io.StringIO(old.decode())));assert len(rows)==29;fields=list(rows[0]);row=dict(zip(fields,['EC-T0030','Equal normalized keys preserve legality and full legal played endpoints','theorems/frozen/EC-T0030/v1.md','proofs/EC-C032_NORMALIZED_KEY_CONGRUENCE.md','formal/EndgameChess/Rules/RawRepetition/KeyCongruence.lean',name,'leanprover/lean4:v4.35.0',sha,s['verified_utc'],'FIDE Laws of Chess 2023 legal-move kernel; normalized-key congruence only','theorems/frozen/EC-T0030/v1.md','FROZEN','From EC-C032. New own-source Gate Z; complete KeyDefinitions/KeyCongruence modules frozen. Equal keys imply Boolean isLegal equality and full legal endpoints for every raw q,r,m. Standard three axioms. No full FIDE key or numerical KRK claim.']));buf=io.StringIO(newline='');csv.DictWriter(buf,fieldnames=fields,lineterminator='\n').writerow(row);p.write_bytes(old+buf.getvalue().encode())
p=root/'research/CANDIDATES.md';p.write_text(p.read_text().replace('FORMAL_VERIFIED (S052, 2026-10-20); Gate Z pending','**FROZEN as [EC-T0030](../theorems/frozen/EC-T0030/v1.md)** (S053, 2026-10-20)'))
p=root/'docs/SESSION_PROGRESS.md';t=p.read_text().replace('through S052. Twenty-nine','through S053. Thirty').replace('these are not twenty-nine solved','these are not thirty solved').replace('normalization prerequisites frozen; key congruence formally verified','normalization/key-congruence prerequisites frozen');delta='Session change: S053 froze normalized-key congruence as EC-T0030 after a new exact-source Gate Z check; 30 bundles are frozen and material-class coverage is unchanged.';t=t.replace(next(l for l in t.splitlines() if l.startswith('Session change:')),delta);p.write_text(t)
p=root/'README.md';t=p.read_text().replace('**After S052.** Twenty-nine frozen theorem bundles (not twenty-nine solved material classes).','**After S053.** Thirty frozen theorem bundles (not thirty solved material classes).').replace('- Next: S053, separate exact-source freeze of normalized-key congruence.','- Next: S054, full normalized-key current occurrence append law.');t+='\n- S053: EC-C032 frozen as [EC-T0030](theorems/frozen/EC-T0030/v1.md), both key modules immutable; separate exact-source Gate Z passed. [Evidence](theorems/frozen/VERIFICATION-S053/README.md).\n';p.write_text(t)
p=root/'docs/ROADMAP.md';t=p.read_text().replace('S053 separate freeze next.','S053 froze this as EC-T0030 after new own-source Gate Z, 30 bundles; S054 targets concrete normalized-key occurrence bookkeeping.');p.write_text(t)
p=root/'theorems/README.md';t=p.read_text().replace('EC-T0007–EC-T0029 were first frozen','EC-T0007–EC-T0030 were first frozen').replace('Current frozen count: **29 bundles**, not twenty-nine solved','Current frozen count: **30 bundles**, not thirty solved');t+='\n- [EC-T0030](frozen/EC-T0030/v1.md): normalized-key legal-move/full-legal-endpoint congruence; both modules frozen S053. [Evidence](frozen/VERIFICATION-S053/README.md).\n';p.write_text(t)
(out/'README.md').write_text(f'''# S053 — Normalized-key congruence Gate Z

{result}

Both complete new key definition/proof modules immutable. Exact main
inspected, all formal bytes match own anchor/current source; full source/transitive
SHA256, clean HEAD/tree/status, full logs/commands/exits/times/UTC/toolchain retained.
Official core Lean4.35.0, no dependency/shim/TLS/checksum change; hosted CI unobserved.
All prior source/records/29 rows preserved, exactly one new manifest/row. No source
edit/incremental build, unrelated diagnostics/trivial tests. Same-agent review,
not independent external audit. First run interrupted by environment restart
after 8/79 jobs; partial logs retained in interrupted-run/. Different NEW clone
retry, no cache reused; successful retry summary above. See
[interruption record](environment-interruption.md). No full FIDE key/adjudication
or KRK distance result.

Reproduce: `python theorems/frozen/VERIFICATION-S053/reproduction/verify.py REPO_ROOT NEW_OUTPUT NEW_CLONE {sha}`
Validate: `python theorems/frozen/VERIFICATION-S053/reproduction/validate.py REPO_ROOT`.
''')
table='\n'.join(l for l in (root/'docs/SESSION_PROGRESS.md').read_text().splitlines() if l.startswith('|'));prompt=(root/'NEXT_SESSION.md').read_text().strip()
(root/'sessions/S053_FREEZE_NORMALIZED_KEY_CONGRUENCE.md').write_text(f'''# S053 — Freeze normalized-key congruence preservation

2026-10-20, base main fd6f92027ca6d887ba28eebefa81d39eba9a7c02;
branch session/s053-freeze-normalized-key-congruence. All-heads fetch,
no prior unmerged work, existing checkout. Consecutive sessions/publication
authorised by owner. EC-C032 frozen as EC-T0030, 30 bundles; no class upgrade.

## Result and fidelity

{scope}

Both complete key modules frozen unchanged, exact paper and Lean fidelity
reviewed. [Review](../theorems/frozen/VERIFICATION-S053/fidelity-review.md).
Same-agent review, not independent external audit. Both colours, arbitrary flags,
promotions, missing/wrong-colour/nonpawn/king/castling/same-file/occupied/source=
destination/pseudo-only-selfcheck cases reviewed symbolically. No concrete full-game
diagnostic, enumeration/oracle/stored certificate or novelty claim. S052 incremental and fresh checks passed first attempt. S053 infrastructure
interruption/retry documented separately; no proof change.

## Observed evidence

{result}
[Evidence](../theorems/frozen/VERIFICATION-S053/README.md). Full source/transitive
hashes, clean HEAD/tree/status, full logs/commands/exits/times/UTC/toolchain retained.
Every formal byte matches own anchor/current source. Official core Lean4.35.0
release eb6cafb7290e8bd5f2937522d8d804f58f02bafc, no dependencies/shim or setup/
TLS/checksum change. Hosted CI unobserved. First clean build was interrupted by environment restart after 8/79 jobs;
partial files retained in interrupted-run/. NEW retry clone, no reused cache,
passed full build/runner. See environment-interruption.md. No source changes. No source edit/incremental build. Relevant ledger structure/tests,
preservation/evidence/full-table/full-prompt/local-link/diff checks passed; all
prior protected source/papers/audits/evidence/manifests and 29 rows preserved,
exactly EC-T0030 appended. No unrelated diagnostics/trivial tests.
Commit/push branch, merge/push main and compare remote SHAs; final identities
retained in Git/observed publication checks. Continue S054 unless owner stops.

## Limits and continuation

No full FIDE key/rights-history/claims/adjudication/mate precedence, strategy
lifting, numerical KRK, holding/outcome, WDL/DTZ/Syzygy or initial-position value.
S054 concrete normalized-key occurrence prerequisite installed, not a solved-class claim.

## Required progress table

{table}

{delta}

## Full installed S054 prompt

{prompt}
''')
p=root/'sessions/SESSION_LEDGER.md';t=p.read_text().replace('Full session closeouts live','| S053 | 2026-10-20 | Freeze EC-C032 normalized-key congruence (Gate Z) | New own-source 79-job build, 279 allowed reports; both complete modules frozen. [Closeout](S053_FREEZE_NORMALIZED_KEY_CONGRUENCE.md) | **+1 → EC-T0030 FROZEN** (30 bundles) |\n\nFull session closeouts live');p.write_text(t)
print(result)
