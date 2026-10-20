"""Finalize S046 only after observed own exact-source Gate F success."""
import json
from pathlib import Path
root=Path(__file__).resolve().parents[3];out=root/'sessions/evidence/S046'
s=json.loads((out/'summary.json').read_text());assert s['build_exit']==s['axiom_statement_exit']==0
sha=s['proof_source'];assert sha=='421608f5b20fee055bc3cb9d0c5904b0d192527b'
utc=s['verified_utc'];sec=s['build_seconds']
p=root/'research/CANDIDATES.md';t=p.read_text().replace('LOCAL_VERIFIED (S046, 2026-10-20); Gate F pending','FORMAL_VERIFIED (S046, 2026-10-20); Gate Z pending').replace('No ep-normalization, full key/FIDE claims or numerical KRK result.',f'Own source `{sha}`; fresh 74-job build, 276 allowed reports. [Evidence](../sessions/evidence/S046/README.md). No ep-normalization, full key/FIDE claims or numerical KRK result.');p.write_text(t)
p=root/'audits/EC-C029_LEGAL_EP_LEAN.md';p.write_text(p.read_text()+f"""
## Completed Gate F

Own published SHA `{sha}`; ONE NEW GitHub clone, no .lake before
build. Full 74-job lake build exit 0, {sec}s; COMPLETE AxiomCheck exit 0 at
{utc}, 276 allowed reports, main standard-three only. Exact main inspected,
whole working/clean output identical, every formal byte matches own anchor.
Full source/transitive hashes and clean HEAD/tree/status retained; one-module
forbidden scan zero. Official core Lean4.35.0 release
 eb6cafb7290e8bd5f2937522d8d804f58f02bafc, no dependency/shim. All authoring/fresh
commands passed, no failures or repeated clean build. Gate F complete, Gate Z
pending; hosted CI unobserved. Evidence: sessions/evidence/S046/.
""")
p=root/'docs/SESSION_PROGRESS.md';t=p.read_text().replace('through S045.', 'through S046.').replace('effective-ep target frozen |','effective-ep target frozen; EP event characterization formally verified |');delta='Session change: S046 formally verified the kernel legal-en-passant event characterization; 26 bundles remain frozen and material-class coverage is unchanged.';t=t.replace(next(l for l in t.splitlines() if l.startswith('Session change:')),delta);p.write_text(t)
p=root/'README.md';t=p.read_text().replace('**After S045.**','**After S046.**').replace('- Next: S046, kernel characterization of the legal en-passant event.', '- S046: **EC-C029 FORMAL_VERIFIED**: an actual legal source pawn changing file into an empty destination is exactly the defined LegalEP event; raw marker/flank recovered from kernel legality. [Paper](proofs/EC-C029_LEGAL_EP_CHARACTERIZATION.md), [evidence](sessions/evidence/S046/README.md). Gate Z pending; no ep-normalization or full FIDE key theorem.\n- Next: S047, separate exact-source Gate Z review of EC-C029.');p.write_text(t)
p=root/'docs/ROADMAP.md';t=p.read_text().replace('S046 targets kernel event characterization before normalization/key composition.', 'S046 formally verifies **EC-C029**, exact kernel LegalEP characterization ([paper](../proofs/EC-C029_LEGAL_EP_CHARACTERIZATION.md), [evidence](../sessions/evidence/S046/README.md)); S047 Gate Z pending before normalization/key composition.');p.write_text(t)
(out/'README.md').write_text(f"""# S046 — EC-C029 kernel LegalEP characterization Gate F evidence

Own published SHA `{sha}`, ONE NEW GitHub clone
`{s['fresh_clone']}`, no .lake before build. Full **74-job lake build exit 0,
{sec}s**, COMPLETE **AxiomCheck exit 0**, **276 allowed reports**, UTC **{utc}**.
Exact main inspected, standard-three only; entire working/clean output identical.
Every formal source matches own anchor, full source/transitive hashes and clean
HEAD/tree/status retained. Official core Lean4.35.0 release
 eb6cafb7290e8bd5f2937522d8d804f58f02bafc; no dependency/shim. All authoring and
fresh commands passed first attempt, no failures/repeated clean build.

Full clone/checkout/prebuild/build/axiom/toolchain/lake logs, commands/exits/
timings/runtime identity/hashes/summary retained. Forbidden-token/preservation/
ledger/document checks separate. Prior formal source/papers/audits/evidence/
manifests and 26 rows unchanged, aggregates additive only. No unrelated
diagnostics/trivial tests, concrete pinned or compatible full game run.
Hosted CI unobserved. Kernel event characterization only, not normalization,
full FIDE key/claims, numerical KRK or solved-class coverage.

```sh
python sessions/evidence/S046/verify.py REPO_ROOT NEW_OUTPUT NEW_CLONE {sha}
python sessions/evidence/S046/validate.py
```
""")
table='\n'.join(l for l in (root/'docs/SESSION_PROGRESS.md').read_text().splitlines() if l.startswith('|'));prompt=(root/'NEXT_SESSION.md').read_text().strip()
(root/'sessions/S046_LEGAL_EP_CHARACTERIZATION.md').write_text(f"""# S046 — Kernel characterization of actual legal en-passant

2026-10-20, base main 3e5f693b90d2f3420effc630aba09677bc971d72;
branch session/s046-legal-ep-characterization. Explicit all-heads fetch, no
prior unmerged session, existing checkout, publication/consecutive run authorised.

## Result and proof fidelity

**EC-C029 FORMAL_VERIFIED, Gate Z pending.** One new EPCharacterization module
imports frozen RawRepetition.Definitions unchanged. Main legalEP_iff_shape:
for EVERY raw q,m, LegalEP iff actual isLegal + source Pawn + distinct files +
empty destination. Marker/flank equations RECOVERED, not assumed on RHS.
Forward projects clauses. Backward preserves original legality, proves dx≠0
by finite-file equality/Fin.ext/integer omega, extracts isPseudo then pawnMoveOK
using exact source pawn, eliminates dx=0 single/double and occupied-dst capture,
and obtains raw ep/opposing flank from remaining EP branch. Both colours, raw
flags and every actual Move/promotion field retained. No enumeration, extra
shared definitions/corollaries, seeds, erased-history or terminal/strategy filter.

[Paper](../proofs/EC-C029_LEGAL_EP_CHARACTERIZATION.md) and
[adversarial audit](../audits/EC-C029_LEGAL_EP_PAPER.md) saved BEFORE Lean;
[Lean fidelity](../audits/EC-C029_LEGAL_EP_LEAN.md). Same-agent reviews, not
independent external audit. Symbolic straight/ordinary-capture/nonpawn/missing-
wrong-flag-flank/both-colour/pseudo-only-self-check controls found no gap.
No concrete pinned or compatible full promotion/ep/castling/threshold game run.
Classical kernel branch reasoning, no novelty/tablebase/engine/certificates.

## Observed verification

OWN source **{sha}** published BEFORE ONE NEW GitHub clone
**{s['fresh_clone']}**, detached FULL exact SHA; no .lake before build.
Full **74-job lake build exit 0, {sec}s**, COMPLETE **AxiomCheck exit 0**,
UTC **{utc}**, **276 allowed reports** (244 standard-three,
18 propext/Quot.sound, 9 propext, 5 axiom-free), main standard-three only.
Exact main inspected; entire working/clean report identical. Every formal byte
matches own anchor; full source/transitive hashes and clean HEAD/tree/status
retained. One new module forbidden scan zero. Incremental build/full authoring
runner passed FIRST attempt, no warnings/failures or repeated clean build.
Official unmodified core Lean4.35.0 release eb6cafb7290e8bd5f2937522d8d804f58f02bafc,
no dependency/shim. Existing elan/Git proxy/network policy sufficient, no setup
or TLS/checksum change. Hosted CI unobserved. [Evidence](evidence/S046/README.md).
Relevant ledger structure, source/record preservation, evidence/full table/prompt/
local-link/diff checks passed. Prior formal/candidate source/papers/audits/session/
evidence/manifests and 26 ledger rows unchanged; aggregate import/runner additive.
No unrelated diagnostics/trivial tests.

## Limits and next session

No theorem that effective-ep normalization preserves legal moves/played endpoints,
full repetition key/Article9.2.3/rights-history correspondence, low-count
certificate, claims/terminal admissibility/adjudication/mate precedence, full Layer/
strategy extraction/lifting, numerical KRK, holding/outcome, DTM/DTZ/WDL/Syzygy
or initial-position result. Raw flags not certified lawful. S047 installs separate
OWN exact-source freeze. A later normalization candidate needs its own complete
paper/audit of every raw ep use, ordinary/pawn/castling/self-check cases and exact
played endpoint/updated flags; no such result assumed here. Commit/push branch,
merge/push main and compare remote SHAs; final identity in Git history/observed
publication checks. Continue installed S047 under standing authorisation.

## Required progress table

{table}

{delta}

## Full installed S047 prompt

{prompt}
""")
p=root/'sessions/SESSION_LEDGER.md';t=p.read_text().replace('Full session closeouts live',f'| S046 | 2026-10-20 | EC-C029 kernel LegalEP characterization (Gate L/F) | Actual legal source pawn changes file into empty dst iff LegalEP; marker/flank recovered via pawnMoveOK and Fin-file dx. Source `{sha}`; fresh 74-job build, 276 allowed reports. S047 freeze installed. [Closeout](S046_LEGAL_EP_CHARACTERIZATION.md) | None — 26 frozen bundles |\n\nFull session closeouts live');p.write_text(t)
print('Created S046 complete evidence-backed records and S047 handover.')
