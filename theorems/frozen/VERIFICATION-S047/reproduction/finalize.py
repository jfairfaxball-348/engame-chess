"""Finalize S047 from successful own Gate Z, then stop as owner instructed."""
import csv,io,json
from pathlib import Path
root=Path(__file__).resolve().parents[4];out=root/'theorems/frozen/VERIFICATION-S047'
s=json.loads((out/'summary.json').read_text());assert s['build_exit']==s['axiom_statement_exit']==0
sha=s['proof_source'];assert sha=='421608f5b20fee055bc3cb9d0c5904b0d192527b'
utc=s['verified_utc'];sec=s['build_seconds']
assert (out/'axioms-statements.log').read_bytes()==(root/'sessions/evidence/S046/axioms-statements.log').read_bytes()
source=(root/'formal/EndgameChess/Rules/RawRepetition/EPCharacterization.lean').read_text()
log=(out/'axioms-statements.log').read_text();statement='EndgameChess.Rules.RawRepetition.legalEP_iff_shape :'+log.split('EndgameChess.Rules.RawRepetition.legalEP_iff_shape :')[1]
manifest=root/'theorems/frozen/EC-T0027/v1.md';assert not manifest.exists();manifest.parent.mkdir()
manifest.write_text(f"""# EC-T0027 v1 — Kernel characterization of the actual legal en-passant event

**Status:** FROZEN (S047, 2026-10-20), candidate EC-C029.
**OWN exact verified proof-source:** `{sha}`.
**Main:** EndgameChess.Rules.RawRepetition.legalEP_iff_shape.

## Scope, immutable module, sources and trust

For EVERY raw q,m, LegalEP iff actual isLegal, source RawClock.Pawn, distinct
files and empty destination. Raw ep marker/opposing flank pawn RECOVERED from
kernel legality, not RHS premises. Actual self-check/promotion legality retained.
Forward projects frozen clauses. Backward proves dx≠0 by finite-file equality/
Fin.ext/integer omega, specializes isPseudo to source pawn, extracts pawnMoveOK,
eliminates single/double and ordinary capture, recovers EP flag/flank. No
coordinate/class enumeration, extra definitions/corollaries, seed, erased-history
surrogate or terminal/material/colour/strategy filter. Both colours/all raw flags.

COMPLETE immutable module:
`formal/EndgameChess/Rules/RawRepetition/EPCharacterization.lean`.
Entire module is frozen byte-for-byte. Transitive closure below retains unchanged
prior frozen definitions; corrections require new module/version under protocol.
[Paper](../../../proofs/EC-C029_LEGAL_EP_CHARACTERIZATION.md),
[paper audit](../../../audits/EC-C029_LEGAL_EP_PAPER.md),
[Lean audit](../../../audits/EC-C029_LEGAL_EP_LEAN.md),
[S047 fidelity](../VERIFICATION-S047/fidelity-review.md).
Same-agent reviews, not independent external audit. Classical kernel branch
reasoning, no novelty/tablebase/engine/enumeration/stored-position certificate.
Rule edition FIDE Laws effective 2023-01-01, existing Article3 legal-move kernel;
raw event characterization only, no new English-FIDE correspondence claim.
Trust: official Lean kernel/standard three axioms, A1 and existing owner-reviewed
FIDE-to-kernel encoding (2026-10-18). No new axiom or concrete pinned/full game run.

No ep-normalization preservation, full key/Article9.2.3/rights-history correspondence,
low-count certificate, claims/terminal admissibility/adjudication/mate precedence,
full Layer/strategy extraction/lifting, numerical KRK, holding/outcome,
DTM/DTZ/WDL/Syzygy or initial-position value. Raw flags not certified lawful.
No adverse reply pruning or solved-material-class upgrade.

## Exact theorem and axiom report

```text
{statement.strip()}
```

## Complete proof source

```lean
{source}```

## Observed Gate Z

ONE NEW GitHub clone `{s['fresh_clone']}`, detached OWN full SHA, no .lake
before build. Full **74-job lake build exit 0, {sec}s**, COMPLETE
**AxiomCheck exit 0**, UTC **{utc}**, **276 allowed reports**.
Main **[propext, Classical.choice, Quot.sound]** only. Entire report identical
to actual S046 Gate F; every formal byte matches own anchor/current main, full
source/transitive hashes and clean HEAD/tree/status retained with commands/exits/
timings. Official unmodified core Lean4.35.0 release
 eb6cafb7290e8bd5f2937522d8d804f58f02bafc; no dependency/shim/TLS/checksum change.
Existing elan/Git proxy sufficient; hosted CI unobserved. Certifies this bundle only.
[Full evidence](../VERIFICATION-S047/README.md).

## Transitive SHA-256 inventory

```text
{(out/'dependency-sha256.txt').read_text()}```
""")
p=root/'theorems/LEDGER.csv';old=p.read_bytes();rows=list(csv.DictReader(io.StringIO(old.decode())));assert len(rows)==26 and rows[-1]['theorem_id']=='EC-T0026'
fields=list(rows[0]);row=dict(zip(fields,['EC-T0027','Kernel characterization of actual legal en-passant by source pawn and empty destination','theorems/frozen/EC-T0027/v1.md','proofs/EC-C029_LEGAL_EP_CHARACTERIZATION.md','formal/EndgameChess/Rules/RawRepetition/EPCharacterization.lean',s['bundle_declarations'][0],'leanprover/lean4:v4.35.0',sha,utc,'FIDE Laws of Chess 2023 legal-move kernel; raw EP event characterization only','theorems/frozen/EC-T0027/v1.md','FROZEN','From EC-C029. New exact-source Gate Z; complete EPCharacterization module frozen. Actual legality/source pawn/distinct files/empty dst recover marker/flank. Standard three axioms. No normalization/full FIDE key or numerical KRK result.']))
b=io.StringIO(newline='');csv.DictWriter(b,fieldnames=fields,lineterminator='\n').writerow(row);p.write_bytes(old+b.getvalue().encode())
p=root/'research/CANDIDATES.md';t=p.read_text().replace('FORMAL_VERIFIED (S046, 2026-10-20); Gate Z pending','**FROZEN as [EC-T0027](../theorems/frozen/EC-T0027/v1.md)** (S047, 2026-10-20)');p.write_text(t)
p=root/'docs/SESSION_PROGRESS.md';t=p.read_text().replace('through S046. Twenty-six','through S047. Twenty-seven').replace('these are not twenty-six solved','these are not twenty-seven solved');lines=t.splitlines();lines=[('| K+R vs K | Dead/live and clock-free forcing frozen; projection, raw history/clock/key-count and legal-ep prerequisites frozen | FIDE history/adjudication and distance |' if l.startswith('| K+R vs K |') else l) for l in lines];t='\n'.join(lines)+'\n';delta='Session change: S047 froze the kernel legal-en-passant characterization as EC-T0027 after a new exact-source Gate Z check; 27 bundles are frozen and material-class coverage is unchanged.';t=t.replace(next(l for l in t.splitlines() if l.startswith('Session change:')),delta);p.write_text(t)
p=root/'README.md';t=p.read_text().replace('**After S046.** Twenty-six frozen theorem bundles (not twenty-six solved material classes).','**After S047.** Twenty-seven frozen theorem bundles (not twenty-seven solved material classes).').replace('- Next: S047, separate exact-source Gate Z review of EC-C029.', '- S047: EC-C029 frozen as [EC-T0027](theorems/frozen/EC-T0027/v1.md) after new exact-source Gate Z (74 jobs, 276 allowed reports), all prior source/records preserved. Owner requested stopping at this closeout.\n- Next: S048, raw ep-marker irrelevance outside en-passant shape; prepared handover only, **not started**.');p.write_text(t)
p=root/'docs/ROADMAP.md';t=p.read_text().replace('S047 Gate Z pending before normalization/key composition.', 'S047 freezes this as EC-T0027 after new exact-source Gate Z (74 jobs, 276 allowed reports). Twenty-seven bundles. S048 ordinary ep-marker irrelevance is prepared as a prerequisite for normalization; owner requested stop at S047, so it is not started.');p.write_text(t)
p=root/'theorems/README.md';t=p.read_text().replace('EC-T0007–EC-T0026 were first frozen','EC-T0007–EC-T0027 were first frozen').replace('Current frozen count: **26 bundles**, not twenty-six solved','Current frozen count: **27 bundles**, not twenty-seven solved');t+='\n- [EC-T0027](frozen/EC-T0027/v1.md): exact kernel LegalEP characterization from actual legality, source pawn, distinct files and empty destination. Frozen S047 from EC-C029. [Evidence](frozen/VERIFICATION-S047/README.md). No normalization/full FIDE key result.\n';p.write_text(t)
(out/'README.md').write_text(f"""# S047 — EC-C029 kernel LegalEP characterization Gate Z evidence

Own published SHA `{sha}`, ONE NEW GitHub clone, no .lake before
build. Full **74-job lake build exit 0, {sec}s**, COMPLETE **AxiomCheck exit 0**,
**276 allowed reports**, UTC **{utc}**, main standard-three only. Exact main
inspected; whole report identical to actual S046 Gate F. Every formal byte matches
own anchor/current main; full source/transitive hashes and clean HEAD/tree/status,
logs/commands/exits/timings/toolchain/lake/runtime identity/UTC summary retained.
Official core Lean4.35.0 release eb6cafb7290e8bd5f2937522d8d804f58f02bafc;
no dependency/shim/TLS/checksum change. Hosted CI unobserved.

EC-C029 frozen as EC-T0027, one complete module, one manifest/new row. All prior
formal source/papers/audits/evidence/manifests and 26 rows preserved. Separate
ledger/test/preservation/document validation retained. No source edit/incremental
build, unrelated diagnostics/trivial tests or concrete pinned/full game run.
Owner requested stopping at S047 closeout. S048 prompt prepared ONLY, not executed.

```sh
python theorems/frozen/VERIFICATION-S047/reproduction/verify.py REPO_ROOT NEW_OUTPUT NEW_CLONE {sha}
python theorems/frozen/VERIFICATION-S047/reproduction/validate.py REPO_ROOT
```
""")
table='\n'.join(l for l in (root/'docs/SESSION_PROGRESS.md').read_text().splitlines() if l.startswith('|'));prompt=(root/'NEXT_SESSION.md').read_text().strip()
(root/'sessions/S047_FREEZE_LEGAL_EP_CHARACTERIZATION.md').write_text(f"""# S047 — Freeze kernel LegalEP characterization; owner stop at closeout

2026-10-20, base main f9ed06af02eaa78ab9fd96c77c764b023153aceb,
branch session/s047-freeze-legal-ep-characterization. Explicit all-heads fetch,
no prior unmerged session, existing checkout. Publication authorised. Owner
changed standing instructions: FINISH THIS CLOSEOUT AND STOP; S048 not started.

## Result and verification

**EC-C029 frozen as EC-T0027**, twenty-seven bundles, no class coverage upgrade.
No Lean source edit. Reviewed actual paper/audits, complete source, Gate F
main/axiom/hash/identity evidence and frozen kernel definitions. Main LegalEP iff
actual legal source pawn changes file into empty dst; marker/opposing flank
recovered from pawnMoveOK, not RHS assumptions. Fin.ext/integer omega proves
dx≠0, actual isLegal retained through self-check/promotion fields. No coordinate/
class enumeration, seed, history shortcut or terminal/material/side restriction.
Same-agent review, not independent external audit. Symbolic single/double/capture/
nonpawn/wrong-marker-flank/both-colour/promotion/pseudo-only-self-check controls;
no concrete pinned/full compatible promotion/ep/castling/threshold game run.
Classical reasoning, no novelty/tablebase/engine/stored-position certificates.

OWN source **{sha}**, ONE NEW GitHub clone
**{s['fresh_clone']}**, detached FULL exact SHA; no .lake before build.
Full **74-job lake build exit 0, {sec}s**, COMPLETE **AxiomCheck exit 0**,
UTC **{utc}**, **276 allowed reports**, main standard-three only.
Exact main inspected; whole output identical to actual S046 Gate F. Every formal
byte matches own anchor/current main; full source/transitive hashes, clean
HEAD/tree/status and commands/exits/timings retained. Official unmodified core
Lean4.35.0 release eb6cafb7290e8bd5f2937522d8d804f58f02bafc; no dependency/shim,
setup/TLS/checksum change; existing elan/Git proxy sufficient. Hosted CI unobserved.
[Evidence](../theorems/frozen/VERIFICATION-S047/README.md).

One immutable manifest/new row; prior formal source/papers/audits/session/
evidence/manifests and 26 rows preserved. Relevant ledger structure/tests,
preservation/evidence/full table/prompt/local-link/diff checks passed. No source
edit/incremental build, unrelated diagnostics/trivial tests. Commit/push branch,
merge/push main and compare remote SHAs; final identity in Git history/observed
publication checks. STOP after publication; no S048 proof/candidate/branch begun.

## Limits and prepared next prompt

No ep-normalization legal-move/endpoint preservation, full repetition key/
Article9.2.3/rights-history theorem, low-count certificate, claims/admissibility/
adjudication/mate precedence, full Layer/strategy extraction/lifting, numerical
KRK, holding/outcome, DTM/DTZ/WDL/Syzygy or initial-position value.

Prepared S048 chooses the smallest ordinary-move prerequisite for normalization:
raw ep-marker replacement preserves pseudo-legality and FULL play outside the
source-pawn/distinct-file/empty-dst shape. It must not assume ¬LegalEP alone
suffices, since total raw play may remove a flank piece on an illegal EP-shaped
move. This is a future exact conditional statement requiring its own paper/audit
and Lean; it is NOT proved here or an assertion of a counterexample to the
separate legal-only normalization target. Owner resumption required to execute.

## Required progress table

{table}

{delta}

## Full installed S048 prompt — prepared, NOT executed

{prompt}
""")
p=root/'sessions/SESSION_LEDGER.md';t=p.read_text().replace('Full session closeouts live',f'| S047 | 2026-10-20 | Freeze kernel LegalEP characterization (Gate Z); owner stop | New own exact-source 74-job build, 276 allowed reports; Gate F output identical, prior sources/records preserved. S048 handover prepared ONLY; owner requested stop at this closeout. [Closeout](S047_FREEZE_LEGAL_EP_CHARACTERIZATION.md) | **+1 → EC-T0027 FROZEN** (27 bundles) |\n\nFull session closeouts live');p.write_text(t)
print('Created EC-T0027 and complete S047 closeout; S048 prepared only, execution stops after publication.')
