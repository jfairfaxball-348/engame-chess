"""Finalize S043 only from successful new exact-source Gate Z evidence."""
import csv,io,json
from pathlib import Path
root=Path(__file__).resolve().parents[4];out=root/'theorems/frozen/VERIFICATION-S043'
s=json.loads((out/'summary.json').read_text());assert s['build_exit']==s['axiom_statement_exit']==0
sha=s['proof_source'];assert sha=='04bd8d03bf09056eff74c5fae1c399a841b170cb'
utc=s['verified_utc'];sec=s['build_seconds']
assert (out/'axioms-statements.log').read_bytes()==(root/'sessions/evidence/S042/axioms-statements.log').read_bytes()
source='\n\n'.join('```lean\n'+(root/p).read_text()+'```' for p in s['complete_modules'])
report=(out/'axioms-statements.log').read_text();statement='def EndgameChess.Rules.RawOccurrences.occurrences.'+report.split('def EndgameChess.Rules.RawOccurrences.occurrences.')[1]
manifest=root/'theorems/frozen/EC-T0025/v1.md';assert not manifest.exists();manifest.parent.mkdir()
manifest.write_text(f"""# EC-T0025 v1 — Generic full raw-history key occurrence counting

**Status:** FROZEN (S043, 2026-10-20), candidate EC-C027.
**OWN exact verified proof-source:** `{sha}`.
**Main:** EndgameChess.Rules.RawOccurrences.append_occurrences.

## Scope, sources and complete immutable boundary

Fix ANY K:Type u with explicit DecidableEq K and FIXED key:Position→K.
occurrences(key,t,a) counts ALL frozen t.positions entries matching a by correct
equality decision, including initial root/current and every prior endpoint.
For EVERY raw s, actual legal m and queried a, append adds exactly one iff
key(new played endpoint)=a. Proof uses frozen append_spec's full position-list
retention and filter/length append/singleton laws. Same map/query on both sides;
new-current count queries NEW key in OLD history, not old-current count+1.
No independent vector, seed, clock reset truncation, erased-history substitution,
or terminal/material/side/strategy filter. All raw replies, resets and adverse
draw-ending children remain. No fabricated compatible full game or finite lookup.

COMPLETE immutable modules:
- formal/EndgameChess/Rules/RawOccurrences/Definitions.lean
- formal/EndgameChess/Rules/RawOccurrences/Append.lean

Both complete definitions/proof modules and their meaning are frozen byte-for-
byte. Transitive closure below includes unchanged EC-T0021 sources. Corrections
require new module/version under the protocol; no silent frozen edits.

[Paper](../../../proofs/EC-C027_RAW_KEY_OCCURRENCES.md),
[paper audit](../../../audits/EC-C027_RAW_KEY_OCCURRENCES_PAPER.md),
[Lean audit](../../../audits/EC-C027_RAW_KEY_OCCURRENCES_LEAN.md),
[S043 fidelity](../VERIFICATION-S043/fidelity-review.md).
Same-agent reviews, not independent external audit. Classical list counting,
no novelty/tablebase/engine/enumeration/stored-position certificate.
Rule edition FIDE Laws effective 2023-01-01, existing Article 3 kernel; raw
generic history bookkeeping, no new English-FIDE encoding claim. Trust remains
official Lean kernel/standard three axioms, A1 and existing owner-reviewed
FIDE-to-kernel encoding (2026-10-18). No new axiom.

Generic key may be constant: NOT a FIDE repetition key, effective-ep/Article
9.2.3/rights-history theorem or low-repetition certificate. No current/intended
claims, no-earlier-terminal admissibility, automatic draws/mate precedence,
full Layer/strategy extraction/lifting, numerical KRK bound, holding/outcome,
DTM/DTZ/WDL/Syzygy or initial-position value. No all-KRK low-count/clock budget
claim or material-class coverage upgrade.

## Exact definition, theorem and axiom report

```text
{statement.strip()}
```

## Complete proof-source modules

{source}

## Observed Gate Z evidence

ONE NEW GitHub clone `{s['fresh_clone']}`, detached OWN full SHA, no .lake
before build. Full **71-job lake build exit 0, {sec}s**, COMPLETE
**AxiomCheck exit 0**, UTC **{utc}**, **274 allowed reports**.
Main **[propext, Classical.choice, Quot.sound]** only. Entire report identical
to actual S042 Gate F. Full source/transitive hashes and clean HEAD/tree/status,
commands/exits/timings retained. Official unmodified core Lean4.35.0 release
 eb6cafb7290e8bd5f2937522d8d804f58f02bafc; no dependencies/shim. Existing elan/
Git proxy used, TLS/checksums unchanged; hosted CI unobserved.
[Full evidence](../VERIFICATION-S043/README.md). Certifies this bundle only.

## Transitive SHA-256 inventory

```text
{(out/'dependency-sha256.txt').read_text()}```
""")
p=root/'theorems/LEDGER.csv';old=p.read_bytes();rows=list(csv.DictReader(io.StringIO(old.decode())));assert len(rows)==24 and rows[-1]['theorem_id']=='EC-T0024'
fields=list(rows[0]);row=dict(zip(fields,['EC-T0025','Generic full raw-history key occurrence counting and exact append law','theorems/frozen/EC-T0025/v1.md','proofs/EC-C027_RAW_KEY_OCCURRENCES.md','formal/EndgameChess/Rules/RawOccurrences/Append.lean',s['bundle_declarations'][0],'leanprover/lean4:v4.35.0',sha,utc,'FIDE Laws of Chess 2023 legal-move kernel; generic raw key counting only','theorems/frozen/EC-T0025/v1.md','FROZEN','From EC-C027. New exact-source Gate Z, both complete RawOccurrences modules frozen. Fixed arbitrary key with DecidableEq; full root/prior/current history retained. Standard three axioms. Not FIDE key correctness or repetition threshold certificate.']))
b=io.StringIO(newline='');csv.DictWriter(b,fieldnames=fields,lineterminator='\n').writerow(row);p.write_bytes(old+b.getvalue().encode())
p=root/'research/CANDIDATES.md';t=p.read_text().replace('FORMAL_VERIFIED (S042, 2026-10-20); Gate Z pending','**FROZEN as [EC-T0025](../theorems/frozen/EC-T0025/v1.md)** (S043, 2026-10-20)');p.write_text(t)
p=root/'docs/SESSION_PROGRESS.md';t=p.read_text().replace('through S042. Twenty-four','through S043. Twenty-five').replace('these are not twenty-four solved','these are not twenty-five solved');lines=t.splitlines();lines=[('| K+R vs K | Dead/live and clock-free forcing frozen; projection, raw trace/clock and generic key counting frozen | FIDE history/adjudication and distance |' if l.startswith('| K+R vs K |') else l) for l in lines];t='\n'.join(lines)+'\n';delta='Session change: S043 froze generic raw key occurrence counting as EC-T0025 after a new exact-source Gate Z check; 25 bundles are frozen and material-class coverage is unchanged.';t=t.replace(next(l for l in t.splitlines() if l.startswith('Session change:')),delta);p.write_text(t)
p=root/'README.md';t=p.read_text().replace('**After S042.** Twenty-four frozen theorem bundles (not twenty-four solved material classes).','**After S043.** Twenty-five frozen theorem bundles (not twenty-five solved material classes).').replace('- Next: S043, separate exact-source Gate Z review of EC-C027.', '- S043: EC-C027 frozen as [EC-T0025](theorems/frozen/EC-T0025/v1.md) after new exact-source Gate Z, 71 jobs and 274 allowed reports. Full prior source/records preserved.\n- Next: S044, legality-filtered en-passant availability/effective target specification.');p.write_text(t)
p=root/'docs/ROADMAP.md';t=p.read_text().replace('S043 Gate Z pending. No FIDE repetition key is claimed;', 'S043 freezes this as EC-T0025 after new exact-source Gate Z (71 jobs, 274 allowed reports). Twenty-five bundles; S044 targets legality-filtered en-passant availability/effective target before key composition. No FIDE repetition key is claimed;');p.write_text(t)
p=root/'theorems/README.md';t=p.read_text().replace('EC-T0007–EC-T0024 were first frozen','EC-T0007–EC-T0025 were first frozen').replace('Current frozen count: **24 bundles**, not twenty-four solved','Current frozen count: **25 bundles**, not twenty-five solved');t+='\n- [EC-T0025](frozen/EC-T0025/v1.md): generic fixed-key full raw-history occurrences and exact append count law. Frozen S043 from EC-C027. [Evidence](frozen/VERIFICATION-S043/README.md). Not a FIDE repetition-key/threshold result.\n';p.write_text(t)
(out/'README.md').write_text(f"""# S043 — EC-C027 Gate Z evidence

Own published SHA `{sha}`, ONE NEW GitHub clone, no formal/.lake
before build. Full **71-job lake build exit 0, {sec}s**; COMPLETE
**AxiomCheck exit 0**, **274 allowed reports**, UTC **{utc}**.
Definition/main inspected, main standard-three only. Entire report identical
to actual S042 Gate F. All source/transitive bytes match own anchor/current main.
Full clone/checkout/prebuild/build/axiom/toolchain/lake logs, commands/exits/
timings, source/import hashes, clean HEAD/tree/status, runtime identity and UTC
summary retained. Official core Lean4.35.0 release eb6cafb7290e8bd5f2937522d8d804f58f02bafc;
no dependencies/shim, TLS/checksums unchanged. Hosted CI unobserved.

EC-C027 frozen as EC-T0025, both complete RawOccurrences modules, one manifest/
ledger row. All prior formal source/papers/audits/evidence/manifests and 24 rows
preserved; validation/ledger/preservation logs separate. No unrelated diagnostic
suite or trivial tests, no failed/repeated clean run or full compatible game.
Generic key counting only, no FIDE key/repetition certificate or class gain.

```sh
python theorems/frozen/VERIFICATION-S043/reproduction/verify.py REPO_ROOT NEW_OUTPUT NEW_CLONE {sha}
python theorems/frozen/VERIFICATION-S043/reproduction/validate.py REPO_ROOT
```
""")
table='\n'.join(l for l in (root/'docs/SESSION_PROGRESS.md').read_text().splitlines() if l.startswith('|'));prompt=(root/'NEXT_SESSION.md').read_text().strip()
(root/'sessions/S043_FREEZE_RAW_KEY_OCCURRENCES.md').write_text(f"""# S043 — Freeze generic full raw-history key occurrence counting

2026-10-20, base main 28c3cc300f34638387fffc45fb899192923fc642,
branch session/s043-freeze-raw-key-occurrences. Explicit all-heads fetch, no
prior unmerged session, existing checkout, publication/consecutive run authorised.

## Result and checks

**EC-C027 frozen as EC-T0025**, twenty-five bundles, no class coverage upgrade.
No Lean source edits. Paper/source review confirms fixed arbitrary key map and
explicit DecidableEq, full root/prior/current position counting, frozen append
retention and exact new-key singleton contribution. New-current count queries
NEW key in OLD history; no reset truncation, vector/seed, erased-history shortcut
or material/side/strategy/terminal filter. Every raw legal append retained.
Same-agent review, not independent external audit; symbolic empty-root/absent/
equal/new/nonconsecutive/constant-key/equal-erasure/reset/earlier-draw controls
found no gap. [A,B,A]→B illustrates the old-current-count mistake, not a full
compatible game. No promotion/ep/castling/threshold prefix run or required.
Classical list counting, no novelty/tablebase/engine/enumeration/certificates.

OWN source **{sha}**, ONE NEW GitHub clone
**{s['fresh_clone']}**, detached FULL exact SHA, no .lake before build.
Full **71-job lake build exit 0, {sec}s**, COMPLETE **AxiomCheck exit 0**,
UTC **{utc}**, **274 allowed reports**, main standard-three only.
Exact definition/main inspected. Whole output identical to actual S042 Gate F;
all source/transitive hashes, clean HEAD/tree/status and commands/exits/timings
retained. Official unmodified core Lean4.35.0 release
 eb6cafb7290e8bd5f2937522d8d804f58f02bafc; no dependency/shim, setup change or
TLS/checksum bypass. Existing elan/Git proxy sufficient. Hosted CI unobserved.
[Evidence](../theorems/frozen/VERIFICATION-S043/README.md).

One immutable manifest/new ledger row, all prior formal source/papers/audits/
session/evidence/manifests and 24 rows preserved. Relevant ledger structure/tests,
preservation/evidence and full table/prompt/local-link/diff checks passed.
No incremental build required without source edits, no unrelated diagnostics
or trivial tests. Commit/push session branch, merge/push main and compare remote
SHAs; final identity in Git history and observed publication checks. Continue S044.

## Limits and next prerequisite

Generic key may be constant: no FIDE repetition key/effective-ep/rights-history/
Article 9.2.3 correspondence or low-repetition certificate. No claims/terminal
admissibility/adjudication/mate precedence, full Layer/strategy extraction/lifting,
numerical KRK bound, holding/outcome, DTM/DTZ/WDL/Syzygy or initial-position value.
S044 chooses precise legality-filtered ep event and effective-target spec before
key composition. play's epCapture is local, not exported; isLegal required,
not just pseudo-legality. No full repetition semantics are inferred.

## Required progress table

{table}

{delta}

## Full installed S044 prompt

{prompt}
""")
p=root/'sessions/SESSION_LEDGER.md';t=p.read_text().replace('Full session closeouts live',f'| S043 | 2026-10-20 | Freeze generic raw key occurrence counting (Gate Z) | New own exact-source 71-job build, 274 allowed reports; Gate F output identical, prior sources/records preserved. S044 effective legal-ep target installed. [Closeout](S043_FREEZE_RAW_KEY_OCCURRENCES.md) | **+1 → EC-T0025 FROZEN** (25 bundles) |\n\nFull session closeouts live');p.write_text(t)
print('Created EC-T0025 and complete S043 closeout from observed Gate Z evidence.')
