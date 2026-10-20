"""Finalize S042 only from observed exact-source Gate F evidence."""
import json
from pathlib import Path
root=Path(__file__).resolve().parents[3];out=root/'sessions/evidence/S042'
s=json.loads((out/'summary.json').read_text());assert s['build_exit']==s['axiom_statement_exit']==0
sha=s['proof_source'];assert sha=='04bd8d03bf09056eff74c5fae1c399a841b170cb'
utc=s['verified_utc'];sec=s['build_seconds']
p=root/'research/CANDIDATES.md';t=p.read_text().replace('LOCAL_VERIFIED (S042, 2026-10-20); Gate F pending','FORMAL_VERIFIED (S042, 2026-10-20); Gate Z pending').replace('Generic bookkeeping, no FIDE repetition-key correctness or threshold certificate.', f'Own source `{sha}`; fresh 71-job build, 274 allowed reports. [Evidence](../sessions/evidence/S042/README.md). Generic bookkeeping, no FIDE repetition-key correctness or threshold certificate.');p.write_text(t)
p=root/'audits/EC-C027_RAW_KEY_OCCURRENCES_LEAN.md';p.write_text(p.read_text()+f"""
## Completed Gate F

Own published exact source `{sha}`, ONE NEW GitHub clone, no .lake
before build. Full 71-job lake build exit 0, {sec}s; COMPLETE AxiomCheck
exit 0 at {utc}. 274 allowed reports, main standard-three only.
Exact definition/main inspected. Working/clean reports identical, all formal
source bytes match own exact source, full source/transitive hashes and clean
HEAD/tree/status retained. Two new modules forbidden scan zero. Official core
Lean4.35.0 release eb6cafb7290e8bd5f2937522d8d804f58f02bafc, no dependency/shim.
No authoring/prebuild/build failure; original and clean checks each passed.
Gate F complete, Gate Z pending; hosted CI unobserved. Evidence: sessions/evidence/S042/.
""")
p=root/'docs/SESSION_PROGRESS.md';t=p.read_text().replace('through S041.', 'through S042.').replace('conditional clock certificate frozen |','conditional clock certificate frozen; generic key-count append law formally verified |');delta='Session change: S042 formally verified generic full-history key occurrence counting and its exact append law; 24 bundles remain frozen and material-class coverage is unchanged.';t=t.replace(next(l for l in t.splitlines() if l.startswith('Session change:')),delta);p.write_text(t)
p=root/'README.md';t=p.read_text().replace('**After S041.**','**After S042.**').replace('- Next: S042, generic full raw-history key occurrence counting and exact append law.', '- S042: **EC-C027 FORMAL_VERIFIED**: occurrence counting for a fixed arbitrary key map with decidable equality and exact append law; root/full history retained even on reset. [Paper](proofs/EC-C027_RAW_KEY_OCCURRENCES.md), [evidence](sessions/evidence/S042/README.md). Gate Z pending; this is not a FIDE repetition-key theorem.\n- Next: S043, separate exact-source Gate Z review of EC-C027.');p.write_text(t)
p=root/'docs/ROADMAP.md';t=p.read_text().replace('S042 targets generic full-history key occurrence counting, without claiming a FIDE repetition key;', 'S042 formally verifies **EC-C027**, generic full-history key occurrence counting and exact append law ([paper](../proofs/EC-C027_RAW_KEY_OCCURRENCES.md), [evidence](../sessions/evidence/S042/README.md)); S043 Gate Z pending. No FIDE repetition key is claimed;');p.write_text(t)
(out/'README.md').write_text(f"""# S042 — EC-C027 Gate F evidence

Own published proof-source `{sha}`, ONE NEW GitHub clone
`{s['fresh_clone']}`, no formal/.lake before build. Full **71-job build,
exit 0, {sec}s**, COMPLETE **AxiomCheck exit 0**, **274 allowed reports**,
UTC **{utc}**, main standard-three only. Definition/main inspected;
full working/clean output identical. Every formal source matches exact anchor;
all source/transitive hashes and clean HEAD/tree/status retained. Official core
Lean4.35.0 release eb6cafb7290e8bd5f2937522d8d804f58f02bafc; no dependencies/shim.

Full clone/checkout/prebuild/build/axiom/toolchain/lake logs, commands/exits/
timings, runtime identity, hashes, summary and declaration list retained.
Forbidden-token, preservation, ledger and document checks separate. No failures,
extra clean builds, unrelated diagnostics or trivial tests. No compatible full
promotion/ep/castling/threshold game run. All prior source/papers/audits/evidence/
manifests and 24 ledger rows unchanged; aggregate Lean files additive only.
Hosted CI unobserved. Generic fixed-map counting, not FIDE key correctness or
a low-repetition certificate; no solved material class gain.

```sh
python sessions/evidence/S042/verify.py REPO_ROOT NEW_OUTPUT NEW_CLONE {sha}
python sessions/evidence/S042/validate.py
```
""")
table='\n'.join(l for l in (root/'docs/SESSION_PROGRESS.md').read_text().splitlines() if l.startswith('|'));prompt=(root/'NEXT_SESSION.md').read_text().strip()
(root/'sessions/S042_RAW_KEY_OCCURRENCES.md').write_text(f"""# S042 — Generic full raw-history key occurrences

2026-10-20, base main 62052f4d87c0fac3e224cb964408dd315ea60fea;
branch session/s042-raw-key-occurrences. Explicit all-heads fetch, no earlier
unmerged sessions, existing checkout. Publication/consecutive sessions authorised.

## Result and scope

**EC-C027 FORMAL_VERIFIED, Gate Z pending.** Shared RawOccurrences/Definitions
and one main in RawOccurrences/Append; aggregate imports/runner additive only.
Fixed arbitrary key:Position→K with explicit DecidableEq K. Count is length of
all t.positions entries satisfying decide(key(p)=a), retaining initial/root,
current and every earlier endpoint. Every legal actual append obeys exactly
occ(child,a)=occ(parent,a)+(if key(new endpoint)=a then 1 else 0).
Proof uses frozen append_spec position-list equality, filter append and singleton
length. Same key/query on both sides; new-current count queries NEW key in OLD
history, not prior-current count+1. No clock reset truncation, independent vector,
arbitrary Boolean equality, erased-history surrogate or terminal/material/side/
strategy filter. All reset/adverse draw-ending legal children remain covered.

[Paper](../proofs/EC-C027_RAW_KEY_OCCURRENCES.md) and
[paper audit](../audits/EC-C027_RAW_KEY_OCCURRENCES_PAPER.md) saved BEFORE Lean;
[Lean fidelity](../audits/EC-C027_RAW_KEY_OCCURRENCES_LEAN.md). Same-agent reviews,
not independent external audit. Symbolic root/absent/equal/new/nonconsecutive/
constant-key/equal-erasure/reset/earlier-draw controls; [A,B,A] followed by B
illustrates why old-current count+1 is wrong. No such list claimed as a full
compatible chess game; no promotion/ep/castling/threshold prefix constructed/run.
Classical list counting, no novelty, engine/tablebase/enumeration/certificates.

## Observed verification

Own source **{sha}** published BEFORE ONE NEW GitHub clone
**{s['fresh_clone']}**, detached FULL exact SHA, formal/.lake absent before build.
Full **71-job lake build exit 0, {sec}s**; COMPLETE **AxiomCheck exit 0**,
UTC **{utc}**, **274 allowed reports** (242 standard-three,
18 propext/Quot.sound, 9 propext, 5 axiom-free). Main standard-three only.
Definition/main exact output inspected. Full working/clean reports identical;
all source/transitive bytes match exact anchor, clean HEAD/tree/status retained.
Two new modules forbidden scan zero. Original incremental build/complete runner
passed FIRST attempt; no failed command/prebuild or repeated clean build.

Official unmodified core Lean4.35.0 release eb6cafb7290e8bd5f2937522d8d804f58f02bafc,
no dependency/shim. Existing elan/Git proxy/network policy sufficient, no setup
change, TLS/checksums unchanged. Hosted CI unobserved. [Evidence](evidence/S042/README.md).
Relevant source/record preservation, ledger structure, evidence/table/full-prompt/
local-link/diff checks passed; no unrelated diagnostics or trivial tests.
Twenty-four frozen bundles unchanged, no ledger row/manifest added or prior
formal/candidate source, paper/audit/session/evidence modified. Aggregates additive.

## Limits and next session

Generic map may be constant, so this is NOT a FIDE repetition-key theorem.
No effective-legal-ep/Article 9.2.3/rights-history correctness, low-repetition
certificate, current/intended claim classifier, lawful-terminal admissibility,
automatic fivefold/75-move adjudication/mate precedence, full Layer/strategy
extraction/lifting, numerical KRK mate bound, holding/outcome, DTM/DTZ/WDL/
Syzygy parity or initial-position value. No all-KRK low-count/clock budget claim.
S043 installs separate exact-source freeze of this bundle. A later narrowly
specified legal-ep availability/effective-target prerequisite may precede any
actual repetition-key choice; kernel play's epCapture is local, not exported.
Commit/push branch, merge/push main and compare remote SHAs; final identity is
in Git history and observed publication checks. Continue installed S043.

## Required progress table

{table}

{delta}

## Full installed S043 prompt

{prompt}
""")
p=root/'sessions/SESSION_LEDGER.md';t=p.read_text().replace('Full session closeouts live',f'| S042 | 2026-10-20 | EC-C027 generic raw key occurrences (Gate L/F) | Fixed map/DecidableEq, root/full-history counting and exact append law; new-current queries NEW key in old history. Source `{sha}`; fresh 71-job build, 274 allowed reports. S043 freeze installed. [Closeout](S042_RAW_KEY_OCCURRENCES.md) | None — 24 frozen bundles |\n\nFull session closeouts live');p.write_text(t)
print('Created S042 complete evidence-backed closeout and statuses.')
