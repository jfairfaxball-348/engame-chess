"""Finalize S041 from successful exact-source Gate Z evidence only."""
import csv,io,json
from pathlib import Path
root=Path(__file__).resolve().parents[4];out=root/'theorems/frozen/VERIFICATION-S041'
s=json.loads((out/'summary.json').read_text());assert s['build_exit']==s['axiom_statement_exit']==0
sha=s['proof_source'];assert sha=='dd24ef3b4bd68d429c9c381908a7f3d5bfa9f85f'
utc=s['verified_utc'];sec=s['build_seconds']
assert (out/'axioms-statements.log').read_bytes()==(root/'sessions/evidence/S040/axioms-statements.log').read_bytes()
source=(root/'formal/EndgameChess/Rules/RawClock/BudgetCertificate.lean').read_text()
report=(out/'axioms-statements.log').read_text();statement='@EndgameChess.Rules.RawClock.clock_budget_certificate :'+report.split('@EndgameChess.Rules.RawClock.clock_budget_certificate :')[1]
manifest=root/'theorems/frozen/EC-T0024/v1.md';assert not manifest.exists();manifest.parent.mkdir()
manifest.write_text(f"""# EC-T0024 v1 — Conditional raw prefix and prospective-ply clock certificate

**Status:** FROZEN (S041, 2026-10-20), candidate EC-C026.
**OWN exact verified proof-source:** `{sha}`.
**Main:** EndgameChess.Rules.RawClock.clock_budget_certificate.

## Scope and immutable boundary

For every raw state s,n under the explicit HYPOTHESIS clock(s.trace)+n<100,
every actual Extends k s u with k≤n has clock(u.trace)<100, and if k<n EVERY
prospective RawBoardStep u v has clock(v.trace)<100. The prospective child is
not asserted played as a claim action. k=n only bounds the current prefix;
n=0 grants no extra ply. Counters/index measure BOARD PLIES. Budget is not a
numerical KRK mate bound. Full initial-rooted traces, actual Move/legal witnesses,
resets and all replies (including adverse draw-ending children) retained.
No erased-board history substitution, arbitrary seed, endpoint clock premise,
terminal/material/side/strategy filter or fabricated compatible game history.
Proof applies frozen growth at k and actual snoc at k+1, k+1≤n and monotonicity.

COMPLETE immutable module:
`formal/EndgameChess/Rules/RawClock/BudgetCertificate.lean`.
No other new source module belongs to this bundle. Complete transitive closure
below includes unchanged EC-T0021–0023 data/proofs. Frozen source must not be
edited; corrections require a new module/version under the protocol.

[Paper](../../../proofs/EC-C026_RAW_CLOCK_BUDGET_CERTIFICATE.md),
[paper audit](../../../audits/EC-C026_RAW_CLOCK_BUDGET_PAPER.md),
[Lean audit](../../../audits/EC-C026_RAW_CLOCK_BUDGET_LEAN.md),
[S041 fidelity review](../VERIFICATION-S041/fidelity-review.md).
Same-agent reviews, not independent external audit. Classical arithmetic, no
novelty, tablebase, engine, enumeration or stored-position certificate.
Rules: FIDE Laws effective 2023-01-01, existing Article 3 legal-move kernel;
raw history/counter bookkeeping only, no new FIDE claim/adjudication encoding.
Trust: official Lean kernel, standard three axioms, A1 and existing owner-reviewed
FIDE-to-kernel encoding (2026-10-18). No new axiom.

No theorem that FIDE CanClaim is false, repetition certificate/key correctness,
no-earlier-terminal admissibility, current/intended claim semantics, automatic
fivefold/75-move adjudication, mate precedence, full Layer instance, strategy
extraction or rule-aware lifting, numerical KRK bound, holding/outcomes,
DTM/DTZ/WDL/Syzygy parity or initial-position result. No class coverage upgrade.

## Exact statement, axioms and complete proof source

```text
{statement.strip()}
```

```lean
{source}```

## Observed Gate Z verification

ONE NEW GitHub clone `{s['fresh_clone']}`, detached at this own FULL exact SHA,
formal/.lake absent BEFORE build. Full **69-job lake build, exit 0, {sec}s**;
COMPLETE **AxiomCheck exit 0**, UTC **{utc}**, **273 allowed reports**.
Main **[propext, Classical.choice, Quot.sound]** only. Entire report identical
to actual S040 Gate F. Exact source/transitive hashes and clean HEAD/tree/status
retained. Official unmodified core Lean4.35.0 release
 eb6cafb7290e8bd5f2937522d8d804f58f02bafc; no dependencies/host shim.
Existing elan/Git proxy used; TLS/checksums unchanged. Hosted CI unobserved.
[Full evidence](../VERIFICATION-S041/README.md). This certifies this bundle only.

## Transitive SHA-256 inventory

```text
{(out/'dependency-sha256.txt').read_text()}```
""")
p=root/'theorems/LEDGER.csv';old=p.read_bytes();rows=list(csv.DictReader(io.StringIO(old.decode())));assert len(rows)==23 and rows[-1]['theorem_id']=='EC-T0023'
fields=list(rows[0]);row=dict(zip(fields,['EC-T0024','Conditional raw prefix and prospective-ply clock certificate','theorems/frozen/EC-T0024/v1.md','proofs/EC-C026_RAW_CLOCK_BUDGET_CERTIFICATE.md','formal/EndgameChess/Rules/RawClock/BudgetCertificate.lean',s['bundle_declarations'][0],'leanprover/lean4:v4.35.0',sha,utc,'FIDE Laws of Chess 2023 legal-move kernel; raw history component only','theorems/frozen/EC-T0024/v1.md','FROZEN','From EC-C026. New exact-source Gate Z; complete BudgetCertificate module frozen. Explicit root budget; all actual prefixes and every interior prospective ply. Standard three axioms. No repetition/FIDE claim semantics or numerical KRK bound.']))
b=io.StringIO(newline='');csv.DictWriter(b,fieldnames=fields,lineterminator='\n').writerow(row);p.write_bytes(old+b.getvalue().encode())
p=root/'research/CANDIDATES.md';t=p.read_text().replace('FORMAL_VERIFIED (S040, 2026-10-20); Gate Z pending','**FROZEN as [EC-T0024](../theorems/frozen/EC-T0024/v1.md)** (S041, 2026-10-20)');p.write_text(t)
p=root/'docs/SESSION_PROGRESS.md';t=p.read_text().replace('through S040. Twenty-three','through S041. Twenty-four').replace('these are not twenty-three solved','these are not twenty-four solved').replace('raw traces, counter and multi-step clock bound frozen; conditional clock certificate formally verified','raw traces, counter, multi-step bound and conditional clock certificate frozen');delta='Session change: S041 froze the conditional raw clock certificate as EC-T0024 after a new exact-source Gate Z check; 24 bundles are frozen and material-class coverage is unchanged.';t=t.replace(next(l for l in t.splitlines() if l.startswith('Session change:')),delta);p.write_text(t)
p=root/'README.md';t=p.read_text().replace('**After S040.** Twenty-three frozen theorem bundles (not twenty-three solved material classes).','**After S041.** Twenty-four frozen theorem bundles (not twenty-four solved material classes).').replace('- Next: S041, exact-source Gate Z review of EC-C026.','- S041: EC-C026 frozen as [EC-T0024](theorems/frozen/EC-T0024/v1.md) after new exact-source Gate Z, 69 jobs and 273 allowed reports. Prior sources/records unchanged.\n- Next: S042, generic full raw-history key occurrence counting and exact append law.');p.write_text(t)
p=root/'docs/ROADMAP.md';t=p.read_text().replace('S041 Gate Z pending;', 'S041 freezes it as EC-T0024 after new exact-source Gate Z (69 jobs, 273 allowed reports). Twenty-four bundles; S042 targets generic full-history key occurrence counting, without claiming a FIDE repetition key;');p.write_text(t)
p=root/'theorems/README.md';t=p.read_text().replace('EC-T0007–EC-T0023 were first frozen','EC-T0007–EC-T0024 were first frozen').replace('Current frozen count: **23 bundles**, not twenty-three solved','Current frozen count: **24 bundles**, not twenty-four solved');t+='\n- [EC-T0024](frozen/EC-T0024/v1.md): conditional raw prefix and every interior prospective-ply clock certificate. Frozen S041 from EC-C026. [Evidence](frozen/VERIFICATION-S041/README.md). No repetition/FIDE claim or numerical KRK conclusion.\n';p.write_text(t)
(out/'README.md').write_text(f"""# S041 — EC-C026 Gate Z evidence

Own exact published source `{sha}`, ONE NEW GitHub clone,
formal/.lake absent before build. Full **69-job build, exit 0, {sec}s**;
COMPLETE **AxiomCheck exit 0**, **273 allowed reports**, UTC **{utc}**.
Main standard-three only, entire report identical to actual S040 Gate F.
All formal/source/transitive bytes match exact anchor/current main; clean
HEAD/tree/status, full logs/commands/exits/timings, source/import hashes,
toolchain/lake/runtime identity and UTC summary retained. Official core
Lean4.35.0 release eb6cafb7290e8bd5f2937522d8d804f58f02bafc, no dependency/shim.
S040's prebuild short-SHA interruption is historical evidence, unchanged;
this separate NEW Gate Z used full SHA and ONE uninterrupted build/runner.
Hosted CI unobserved. Fidelity review symbolic; no compatible full game run.

EC-C026 frozen as EC-T0024, one new ledger row/manifest; all prior formal source,
papers/audits/evidence/manifests and 23 ledger rows preserved. Evidence,
preservation, ledger and document checks retained separately. No unrelated
diagnostics or trivial tests. Raw conditional clock scope, no solved-class gain.

```sh
python theorems/frozen/VERIFICATION-S041/reproduction/verify.py REPO_ROOT NEW_OUTPUT NEW_CLONE {sha}
python theorems/frozen/VERIFICATION-S041/reproduction/validate.py REPO_ROOT
```
""")
table='\n'.join(l for l in (root/'docs/SESSION_PROGRESS.md').read_text().splitlines() if l.startswith('|'));prompt=(root/'NEXT_SESSION.md').read_text().strip()
(root/'sessions/S041_FREEZE_RAW_CLOCK_BUDGET.md').write_text(f"""# S041 — Freeze the conditional raw clock certificate

2026-10-20, base main 29cf1b004c2671457b0b2b3e52a250b18eb87d09,
branch session/s041-freeze-clock-budget. Explicit all-heads fetch, no earlier
unmerged session, existing checkout. Publication/consecutive sessions authorised.

## Result and verification

**EC-C026 frozen as EC-T0024**, twenty-four bundles, no new solved class.
No Lean source changed. Reviewed paper/audits, actual Gate F/source/identity
logs, frozen EC-T0021–0023 boundaries and exact conditional statement.
Root clock+n<100 is a HYPOTHESIS. Every actual k≤n prefix is below 100;
EVERY prospective raw step at k<n is bounded via actual Extends.snoc and growth.
k=n bounds only current state; n=0 grants no extra ply. Full histories and
all legal Move witnesses/replies remain, including reset/draw-ending children.
No erased-board history shortcut, seed, endpoint-clock premise or terminal filter.
Same-agent fidelity review, not independent external audit; symbolic n=0/k=0/
k=n,99/100,quiet/reset/mixed/equal-erasure/earlier-draw controls. No fixed full
promotion/ep/castling/threshold game run. Classical arithmetic, no novelty,
tablebase/engine/enumeration or per-position certificates.

OWN proof-source **{sha}**. ONE NEW GitHub clone
**{s['fresh_clone']}**, detached FULL exact SHA, no .lake before build.
Full **69-job lake build exit 0, {sec}s**, COMPLETE **AxiomCheck exit 0**,
UTC **{utc}**, **273 allowed reports**, main standard-three only.
Entire report identical to actual S040 Gate F; all source/transitive hashes,
clean HEAD/tree/status, command exits/timings retained. Official unmodified
core Lean4.35.0 release eb6cafb7290e8bd5f2937522d8d804f58f02bafc; no dependency/
shim. Existing elan/Git proxy sufficient, TLS/checksums unchanged. Hosted CI
unobserved. [Evidence](../theorems/frozen/VERIFICATION-S041/README.md).
S040's short-SHA prebuild failure retained unchanged; this NEW Gate Z had no
such interruption. No incremental build needed without source changes.

One new immutable manifest/ledger row; all prior formal source, papers/audits,
session/evidence/manifests and 23 ledger rows preserved. Relevant ledger tests/
structure, preservation, evidence and full table/prompt/local-link/diff checks
passed. No unrelated diagnostics or trivial tests. Commit/push branch,
merge/push main and compare remote SHAs; final identity in Git history and
observed publication checks. Consecutive execution continues to installed S042.

## Limits and next prerequisite

No FIDE CanClaim theorem, repetition bound/key correctness, no-earlier-terminal
admissibility, current/intended claims, automatic adjudication/mate precedence,
full Layer/strategy extraction/lifting, numerical KRK bound, holding/outcomes,
DTM/DTZ/WDL/Syzygy or initial-position value. S042 chooses generic full-history
occurrence counting and exact append law under an explicit fixed key map with
decidable equality. It will NOT claim that key is the FIDE repetition key or
that any history has a low-repetition certificate. All root/reset history stays.

## Required progress table

{table}

{delta}

## Full installed S042 prompt

{prompt}
""")
p=root/'sessions/SESSION_LEDGER.md';t=p.read_text().replace('Full session closeouts live',f'| S041 | 2026-10-20 | Freeze conditional raw clock certificate (Gate Z) | New own exact-source 69-job build, 273 allowed reports; Gate F report identical, all source/records preserved. S042 generic raw key occurrence counting installed. [Closeout](S041_FREEZE_RAW_CLOCK_BUDGET.md) | **+1 → EC-T0024 FROZEN** (24 bundles) |\n\nFull session closeouts live');p.write_text(t)
print('Created EC-T0024 and complete S041 records from successful Gate Z.')
