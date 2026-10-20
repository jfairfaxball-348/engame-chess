"""Write S048 final records only after observed clean Gate F success."""
import json
from pathlib import Path
root=Path(__file__).resolve().parents[3]; out=root/'sessions/evidence/S048'
s=json.loads((out/'summary.json').read_text());assert s['build_exit']==s['axiom_statement_exit']==0
sha=s['proof_source'];assert sha=='c4c900036dcffd209d6c08f27e2323637852c940'
result=f"Own source `{sha}`; new exact GitHub clone, no .lake before build; {s['build_jobs']}-job build exit 0 in {s['build_seconds']}s; complete AxiomCheck exit 0 at {s['verified_utc']}, {s['total_axiom_reports']} allowed reports. Main standard-three; entire working/clean output byte-identical."
p=root/'research/CANDIDATES.md';p.write_text(p.read_text().replace('LOCAL_VERIFIED (S048, 2026-10-20); Gate F pending','FORMAL_VERIFIED (S048, 2026-10-20); Gate Z pending').replace('Conditional kernel prerequisite only; no full normalization/FIDE key or KRK distance claim.',f'{result} [Evidence](../sessions/evidence/S048/README.md). Conditional kernel prerequisite only; no full normalization/FIDE key or KRK distance claim.'))
p=root/'audits/EC-C030_ORDINARY_EP_LEAN.md';p.write_text(p.read_text()+f'\n## Observed Gate F\n\n{result}\nAll formal source bytes match own anchor, source/transitive hashes and clean\nHEAD/tree/status retained. Official core Lean4.35.0; no dependencies/shim.\nRoot-cwd elan identity lookup failed before clean verification; repeated in\nformal/ successfully. No Lean failure in fresh clone. Hosted CI unobserved.\n')
p=root/'docs/SESSION_PROGRESS.md';t=p.read_text().replace('through S047.', 'through S048.').replace('legal-ep prerequisites frozen |','legal-ep prerequisites frozen; ordinary ep irrelevance formally verified |');delta='Session change: S048 formally verified ordinary ep-marker irrelevance outside the raw EP shape; 27 bundles remain frozen and material-class coverage is unchanged.';t=t.replace(next(l for l in t.splitlines() if l.startswith('Session change:')),delta);p.write_text(t)
p=root/'README.md';t=p.read_text().replace('**After S047.**','**After S048.**');t=t.replace('- Next: S048, raw ep-marker irrelevance outside en-passant shape; prepared handover only, **not started**.', '- Next: S049, separate exact-source freeze of ordinary ep-marker irrelevance.');t += '\n- S048: EC-C030 **FORMAL_VERIFIED**, raw ep-marker irrelevance outside EP shape, including full played Position equality. [Paper](proofs/EC-C030_ORDINARY_EP_IRRELEVANCE.md), [evidence](sessions/evidence/S048/README.md). S049 separate freeze next; consecutive sessions resumed by owner.\n';p.write_text(t)
p=root/'docs/ROADMAP.md';t=p.read_text().replace('S048 ordinary ep-marker irrelevance is prepared as a prerequisite for normalization; owner requested stop at S047, so it is not started.', 'S048 formally verified EC-C030, ordinary ep-marker irrelevance outside raw EP shape, including full played Position equality ([paper](../proofs/EC-C030_ORDINARY_EP_IRRELEVANCE.md), [evidence](../sessions/evidence/S048/README.md)); owner resumed consecutive sessions, S049 separate freeze next.');p.write_text(t)
(out/'README.md').write_text(f'''# S048 — Ordinary ep-marker irrelevance Gate F

{result}

Official core Lean4.35.0 release eb6cafb7290e8bd5f2937522d8d804f58f02bafc;
no dependencies/shim. Full clone/checkout/prebuild/build/axiom/toolchain logs,
commands/exits/timings, source/transitive hashes and clean identity retained.
New main only standard three axioms. Forbidden-token scan zero. Hosted CI unobserved.
Prior sources/records/ledger unchanged; aggregate imports/runner additive only.
Initial shell cwd error wrote no source; initial incremental Boolean simplification
failure retained, fixed without statement changes. Root-cwd elan identity lookup
failed, successful formal/ lookup retained. No failed/repeated clean build.
Gate F complete; Gate Z pending. No full normalization, FIDE key or KRK outcome.

Reproduce in NEW directories:
`python sessions/evidence/S048/verify.py REPO_ROOT NEW_OUTPUT NEW_CLONE {sha}`
Validate: `python sessions/evidence/S048/validate.py`.
''')
table='\n'.join(l for l in (root/'docs/SESSION_PROGRESS.md').read_text().splitlines() if l.startswith('|'));prompt=(root/'NEXT_SESSION.md').read_text().strip()
(root/'sessions/S048_ORDINARY_EP_IRRELEVANCE.md').write_text(f'''# S048 — Ordinary ep-marker irrelevance

2026-10-20, base main 66e7638f8c9da89dd326d74165342343afacf62c;
branch session/s048-ordinary-ep-irrelevance. Explicit all-heads fetch, no unmerged
prior work, existing checkout; owner resumed consecutive sessions and publication.

## Result

EC-C030 FORMAL_VERIFIED; Gate Z pending. Every raw q,m,e, outside source-Pawn,
distinct-file, empty-destination shape: marker replacement preserves isPseudo
and FULL play. No legality/reachability/history premise. Paper and separate
same-agent adversarial review saved before Lean; not independent external audit.
[Paper](../proofs/EC-C030_ORDINARY_EP_IRRELEVANCE.md),
[paper audit](../audits/EC-C030_ORDINARY_EP_PAPER.md),
[Lean review](../audits/EC-C030_ORDINARY_EP_LEAN.md).

Raw epCapture false for both markers by guard; unfolding play preserves board
function, turn, castling and freshly recomputed ep. Source/colour/kind analysis
isolates pawnMoveOK; equal files make capture geometry false, occupied destination
makes EP test false. Absent/wrong-colour/nonpawn/king/castling, promotion,
source=destination, both colours and arbitrary markers handled symbolically.
No concrete pinned/full promotion/castling/threshold game run; no enumeration,
engine/tablebase, stored certificates or novelty claim.

## Observed checks and publication

{result}
[Evidence](evidence/S048/README.md). Exact main inspected; official core
Lean4.35.0, no dependency/shim. Full command/exits/timings/UTC/toolchain, formal
source/transitive hashes and clean HEAD/tree/status retained. New module forbidden
scan zero. Final incremental changed module/importer build and full working
runner passed. One first incremental failure retained, fixed wrong-colour Boolean
simplification without changing statement. Initial shell cwd error wrote no source;
empty stray directories removed. Root-cwd elan identity lookup failed, succeeded
in formal/. Clean build/runner succeeded once, no repeated clean build. Runtime
current/connected/unrestricted; inherited proxy/CA/toolchain unchanged.
Relevant ledger/evidence/preservation/full-table/full-prompt/local-link/diff checks
passed. All prior protected sources/papers/audits/evidence/manifests and 27 ledger
rows unchanged; aggregate imports/runner additive. No unrelated diagnostics/tests.
Hosted CI unobserved. Proof source published before fresh clone. Closeout commit,
branch push, main merge/push and remote identity recorded in Git/publication checks.

## Limits and continuation

Conditional raw-kernel lemma only. ¬LegalEP alone does not justify equality of
raw play for illegal EP-shaped moves. No normalization/FIDE key/rights-history,
claim/adjudication/mate precedence, strategy lifting, numerical KRK, WDL/DTZ or
solved material-class upgrade. S049 separate exact-source freeze installed;
continue under standing owner authorisation until told to stop.

## Required progress table

{table}

{delta}

## Full installed S049 prompt

{prompt}
''')
p=root/'sessions/SESSION_LEDGER.md';t=p.read_text().replace('Full session closeouts live',f'| S048 | 2026-10-20 | EC-C030 ordinary ep irrelevance (Gate L/F) | Full pseudo/play preservation outside EP shape; {s["build_jobs"]}-job clean build, {s["total_axiom_reports"]} allowed reports. [Closeout](S048_ORDINARY_EP_IRRELEVANCE.md) | None — 27 frozen bundles |\n\nFull session closeouts live');p.write_text(t)
print(result)
