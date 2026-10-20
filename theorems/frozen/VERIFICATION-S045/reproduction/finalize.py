"""Finalize S045 only from successful own exact-source Gate Z evidence."""
import csv,io,json
from pathlib import Path
root=Path(__file__).resolve().parents[4];out=root/'theorems/frozen/VERIFICATION-S045'
s=json.loads((out/'summary.json').read_text());assert s['build_exit']==s['axiom_statement_exit']==0
sha=s['proof_source'];assert sha=='28bdacfa34995ed3d778bfb2dab1654e46999f0c'
utc=s['verified_utc'];sec=s['build_seconds']
assert (out/'axioms-statements.log').read_bytes()==(root/'sessions/evidence/S044/axioms-statements.log').read_bytes()
source='\n\n'.join('```lean\n'+(root/p).read_text()+'```' for p in s['complete_modules'])
log=(out/'axioms-statements.log').read_text();statement='def EndgameChess.Rules.RawRepetition.LegalEP :'+log.split('def EndgameChess.Rules.RawRepetition.LegalEP :')[1]
manifest=root/'theorems/frozen/EC-T0026/v1.md';assert not manifest.exists();manifest.parent.mkdir()
manifest.write_text(f"""# EC-T0026 v1 — Legality-filtered en-passant availability and effective target

**Status:** FROZEN (S045, 2026-10-20), candidate EC-C028.
**OWN exact verified proof-source:** `{sha}`.
**Main:** EndgameChess.Rules.RawRepetition.effectiveEP_spec.

## Scope, sources, immutable boundary and trust

LegalEP explicitly requires actual isLegal, frozen source Pawn, q.ep=some m.dst,
distinct files, empty destination and opposing flank pawn. It is the existing
CaptureEvent EP event with actual legality, not mere pseudo-legality or an
exported epCapture predicate (play's test is local). effectiveEP is explicitly
NONCOMPUTABLE classical existence-filtered q.ep, no search/enumeration claim.
For EVERY raw q, main proves none iff no legal witness, and some dst iff an
actual legal witness targets dst. Witness flag consistency rules out none/wrong
target when available; some injectivity fixes every witness's destination.
No separate target/count/clock seed, endpoint premise, material/colour/strategy/
terminal filter or assertion that arbitrary raw flags have lawful FIDE history.

COMPLETE immutable modules:
- formal/EndgameChess/Rules/RawRepetition/Definitions.lean
- formal/EndgameChess/Rules/RawRepetition/EffectiveEP.lean

Both complete modules, including shared definitions/noncomputable construction,
are frozen byte-for-byte; transitive closure below retains unchanged prior
frozen definitions. Corrections require new module/version under protocol.
[Paper](../../../proofs/EC-C028_EFFECTIVE_EP_TARGET.md),
[paper audit](../../../audits/EC-C028_EFFECTIVE_EP_PAPER.md),
[Lean audit](../../../audits/EC-C028_EFFECTIVE_EP_LEAN.md),
[S045 fidelity](../VERIFICATION-S045/fidelity-review.md).
Same-agent reviews, not independent external audit. Classical construction,
no novelty/tablebase/engine/enumeration/stored-position certificate.
Rules: FIDE Laws effective 2023-01-01, existing Article3 kernel/raw event only;
no new English-FIDE repetition correspondence. Trust: official Lean kernel,
standard three axioms, A1/existing owner-reviewed FIDE-to-kernel encoding
(2026-10-18). No new axiom. No pinned/full compatible game claimed as run.

No full key/Article9.2.3/rights-history correctness, low-count certificate,
claims/terminal admissibility/adjudication/mate precedence, full Layer/strategy
extraction/lifting, numerical KRK, holding/outcome, DTM/DTZ/WDL/Syzygy or
initial-position result. No adverse reply pruning or solved-class upgrade.

## Exact definitions, main statement and axiom report

```text
{statement.strip()}
```

## Complete source

{source}

## Observed Gate Z

ONE NEW GitHub clone `{s['fresh_clone']}`, detached OWN FULL SHA, no .lake
before build. Full **73-job lake build exit 0, {sec}s**; COMPLETE
**AxiomCheck exit 0**, UTC **{utc}**, **275 allowed reports**.
Main **[propext, Classical.choice, Quot.sound]** only. Entire report identical
to actual S044 Gate F; full source/transitive hashes and clean HEAD/tree/status
retained with commands/exits/timings. Official unmodified core Lean4.35.0 release
 eb6cafb7290e8bd5f2937522d8d804f58f02bafc; no dependency/shim, setup/TLS/checksum
change. Existing elan/Git proxy sufficient. Hosted CI unobserved.
[Full evidence](../VERIFICATION-S045/README.md). Certifies this bundle only.
S044 initial local compile failure and corrected witness retention preserved;
this NEW Gate Z is a separate full run.

## Transitive SHA-256 inventory

```text
{(out/'dependency-sha256.txt').read_text()}```
""")
p=root/'theorems/LEDGER.csv';old=p.read_bytes();rows=list(csv.DictReader(io.StringIO(old.decode())));assert len(rows)==25 and rows[-1]['theorem_id']=='EC-T0025'
fields=list(rows[0]);row=dict(zip(fields,['EC-T0026','Legality-filtered en-passant availability and effective target specification','theorems/frozen/EC-T0026/v1.md','proofs/EC-C028_EFFECTIVE_EP_TARGET.md','formal/EndgameChess/Rules/RawRepetition/EffectiveEP.lean',s['bundle_declarations'][0],'leanprover/lean4:v4.35.0',sha,utc,'FIDE Laws of Chess 2023 legal-move kernel; raw effective-ep target only','theorems/frozen/EC-T0026/v1.md','FROZEN','From EC-C028. New exact-source Gate Z, complete RawRepetition Definitions/EffectiveEP frozen. Actual legal EP event and classical effective-target consistency; standard three axioms. No full FIDE repetition-key/claim or numerical KRK result.']))
b=io.StringIO(newline='');csv.DictWriter(b,fieldnames=fields,lineterminator='\n').writerow(row);p.write_bytes(old+b.getvalue().encode())
p=root/'research/CANDIDATES.md';t=p.read_text().replace('FORMAL_VERIFIED (S044, 2026-10-20); Gate Z pending','**FROZEN as [EC-T0026](../theorems/frozen/EC-T0026/v1.md)** (S045, 2026-10-20)');p.write_text(t)
p=root/'docs/SESSION_PROGRESS.md';t=p.read_text().replace('through S044. Twenty-five','through S045. Twenty-six').replace('these are not twenty-five solved','these are not twenty-six solved').replace('effective-ep target formally verified','effective-ep target frozen');delta='Session change: S045 froze the legality-filtered effective en-passant target as EC-T0026 after a new exact-source Gate Z check; 26 bundles are frozen and material-class coverage is unchanged.';t=t.replace(next(l for l in t.splitlines() if l.startswith('Session change:')),delta);p.write_text(t)
p=root/'README.md';t=p.read_text().replace('**After S044.** Twenty-five frozen theorem bundles (not twenty-five solved material classes).','**After S045.** Twenty-six frozen theorem bundles (not twenty-six solved material classes).').replace('- Next: S045, separate exact-source Gate Z review of EC-C028.', '- S045: EC-C028 frozen as [EC-T0026](theorems/frozen/EC-T0026/v1.md) after new exact-source Gate Z (73 jobs, 275 allowed reports), with all prior source/records preserved.\n- Next: S046, kernel characterization of the legal en-passant event.');p.write_text(t)
p=root/'docs/ROADMAP.md';t=p.read_text().replace('S045 Gate Z pending before further kernel fidelity/key composition.', 'S045 freezes this as EC-T0026 after new exact-source Gate Z (73 jobs, 275 allowed reports). Twenty-six bundles; S046 targets kernel event characterization before normalization/key composition.');p.write_text(t)
p=root/'theorems/README.md';t=p.read_text().replace('EC-T0007–EC-T0025 were first frozen','EC-T0007–EC-T0026 were first frozen').replace('Current frozen count: **25 bundles**, not twenty-five solved','Current frozen count: **26 bundles**, not twenty-six solved');t+='\n- [EC-T0026](frozen/EC-T0026/v1.md): actual legal-ep availability/effective-target specification. Frozen S045 from EC-C028. [Evidence](frozen/VERIFICATION-S045/README.md). No full FIDE repetition-key/claim result.\n';p.write_text(t)
(out/'README.md').write_text(f"""# S045 — EC-C028 effective ep target Gate Z evidence

Own SHA `{sha}`, ONE NEW GitHub clone, no .lake before build.
Full **73-job lake build exit 0, {sec}s**, COMPLETE **AxiomCheck exit 0**,
**275 allowed reports**, UTC **{utc}**, main standard-three only.
Exact definitions/main inspected, full output identical to actual S044 Gate F.
All source/transitive bytes match own anchor/current main; source/import hashes,
clean HEAD/tree/status and full logs/commands/exits/timings/runtime/toolchain/
lake/UTC summary retained. Official core Lean4.35.0 release
 eb6cafb7290e8bd5f2937522d8d804f58f02bafc; no dependency/shim/TLS/checksum change.
Hosted CI unobserved. Prior initial local S044 compile failure preserved;
this new full Gate Z ran separately, no incremental source check needed.

EC-C028 frozen as EC-T0026, both complete RawRepetition definition/proof modules,
one immutable manifest/new ledger row. Prior formal source/papers/audits/evidence/
manifests and 25 rows preserved; ledger/test/preservation/document checks separate.
No unrelated diagnostics/trivial tests or full compatible/pinned game run.
Legality-filtered target only, no full FIDE key/claims or solved-class gain.

```sh
python theorems/frozen/VERIFICATION-S045/reproduction/verify.py REPO_ROOT NEW_OUTPUT NEW_CLONE {sha}
python theorems/frozen/VERIFICATION-S045/reproduction/validate.py REPO_ROOT
```
""")
table='\n'.join(l for l in (root/'docs/SESSION_PROGRESS.md').read_text().splitlines() if l.startswith('|'));prompt=(root/'NEXT_SESSION.md').read_text().strip()
(root/'sessions/S045_FREEZE_EFFECTIVE_EP_TARGET.md').write_text(f"""# S045 — Freeze legality-filtered effective en-passant target

2026-10-20, base main 70f4230beb8bd328b5aa67135fce5a754d5bafb3,
branch session/s045-freeze-effective-ep-target. Explicit all-heads fetch, no
prior unmerged sessions, existing checkout, publication/consecutive run authorised.

## Result and checks

**EC-C028 frozen as EC-T0026**, twenty-six bundles, no class coverage upgrade.
No Lean source edits. Reviewed actual paper/audits, complete definitions/proof,
Gate F statement/axiom/hash/identity evidence and existing kernel event sources.
LegalEP uses actual legality plus source pawn/raw flag/distinct files/empty dst/
opposing flank pawn, not pseudo-legality. Noncomputable effective target uses
classical existence, not search. Main none/no-witness and some/exact-witness
specification proves target consistency using actual flag and some injectivity.
No seed/endpoint hypothesis or material/colour/strategy/terminal filter; arbitrary
raw flags not certified as lawful histories. Same-agent review, not independent
external audit. Symbolic no-flag/no-pawn/pseudo-only/self-check/multiple-source/
occupied/wrong-kind-colour-flank/ordinary controls; no concrete pinned/full
promotion/ep/castling/threshold history run. Classical, no novelty/tablebase/engine.

OWN source **{sha}**, ONE NEW GitHub clone
**{s['fresh_clone']}**, detached FULL exact SHA, no .lake before build.
Full **73-job lake build exit 0, {sec}s**, COMPLETE **AxiomCheck exit 0**,
UTC **{utc}**, **275 allowed reports**, main standard-three only.
Exact definitions/main inspected; entire output identical to S044 Gate F.
Every source/transitive hash and clean HEAD/tree/status retained with commands/
exits/timings. Official unmodified core Lean4.35.0 release
 eb6cafb7290e8bd5f2937522d8d804f58f02bafc, no dependency/shim/setup/TLS/checksum
change; existing elan/Git proxy sufficient. Hosted CI unobserved.
[Evidence](../theorems/frozen/VERIFICATION-S045/README.md). Historical S044 local
compile failure/correction preserved; no source change or incremental check here.

One immutable manifest/new row; all prior formal source/papers/audits/session/
evidence/manifests and 25 rows unchanged. Relevant ledger structure/tests,
preservation/evidence/full table/prompt/local-link/diff checks passed. No unrelated
diagnostics/trivial tests. Commit/push branch, merge/push main, compare remote
SHAs; final identity in Git history/observed publication checks. Continue S046.

## Limits and next prerequisite

No full repetition key/Article9.2.3/rights-history correspondence, low-count
certificate, claims/admissibility/adjudication/mate precedence, full Layer/
strategy extraction/lifting, numerical KRK, holding/outcome, DTM/DTZ/WDL/Syzygy
or initial-position result. S046 selects exact kernel characterization of
LegalEP: actual legal source pawn + distinct files + empty dst should force raw
ep flag and opposing flank pawn via pawnMoveOK's remaining branch. Its paper/
audit must precede Lean, preserving actual legality and finite-file arithmetic.
This precedes any normalization/key composition; no such result assumed here.

## Required progress table

{table}

{delta}

## Full installed S046 prompt

{prompt}
""")
p=root/'sessions/SESSION_LEDGER.md';t=p.read_text().replace('Full session closeouts live',f'| S045 | 2026-10-20 | Freeze effective legal-ep target (Gate Z) | New own exact-source 73-job build, 275 allowed reports; Gate F output identical; prior sources/records preserved. S046 kernel LegalEP characterization installed. [Closeout](S045_FREEZE_EFFECTIVE_EP_TARGET.md) | **+1 → EC-T0026 FROZEN** (26 bundles) |\n\nFull session closeouts live');p.write_text(t)
print('Created EC-T0026 and complete S045 records from successful Gate Z evidence.')
