"""Write S040 records only after successful exact-source Gate F evidence."""
import json
from pathlib import Path
root=Path(__file__).resolve().parents[3];out=root/'sessions/evidence/S040'
s=json.loads((out/'summary.json').read_text());assert s['build_exit']==s['axiom_statement_exit']==0
sha=s['proof_source'];assert sha=='dd24ef3b4bd68d429c9c381908a7f3d5bfa9f85f'
utc=s['verified_utc'];seconds=s['build_seconds']
p=root/'research/CANDIDATES.md';t=p.read_text().replace('LOCAL_VERIFIED (S040, 2026-10-20); Gate F pending','FORMAL_VERIFIED (S040, 2026-10-20); Gate Z pending').replace('Explicit budget hypothesis, no repetition/FIDE claim semantics or numerical KRK bound.',f'Explicit budget hypothesis. Exact source `{sha}`; fresh 69-job build, 273 allowed reports. [Evidence](../sessions/evidence/S040/README.md). No repetition/FIDE claim semantics or numerical KRK bound.');p.write_text(t)
p=root/'audits/EC-C026_RAW_CLOCK_BUDGET_LEAN.md';p.write_text(p.read_text()+f"""
## Completed Gate F

Own published source `{sha}`; ONE NEW GitHub clone, no formal/.lake
before build. Full 69-job lake build exit 0, {seconds}s; complete AxiomCheck
exit 0 at {utc}. 273 allowed reports; main standard-three only.
Exact statement inspected, working/clean reports byte-identical; all source/
transitive hashes and clean HEAD/tree/status retained. No forbidden proof tokens.
Official core Lean4.35.0 release eb6cafb7290e8bd5f2937522d8d804f58f02bafc,
no dependencies/shim. Initial full-HEAD assertion rejected a short SHA BEFORE
any Lean command; same new clone resumed at FULL SHA, no cache, ONE build/runner.
That prebuild failure and original checkout/command records are retained. The
verifier gained an explicit prebuild-only resume guard; formal source unchanged.
Gate F passed, Gate Z pending; hosted CI unobserved. Evidence: sessions/evidence/S040/.
""")
p=root/'docs/SESSION_PROGRESS.md';t=p.read_text().replace('through S039.', 'through S040.').replace('counter and multi-step clock bound frozen |','counter and multi-step clock bound frozen; conditional clock certificate formally verified |');delta='Session change: S040 formally verified the conditional raw prefix and prospective-ply clock certificate; 23 bundles remain frozen and material-class coverage is unchanged.';t=t.replace(next(l for l in t.splitlines() if l.startswith('Session change:')),delta);p.write_text(t)
p=root/'README.md';t=p.read_text().replace('**After S039.**','**After S040.**').replace('- Next: S040, conditional raw prefix and prospective-ply clock certificate.', '- S040: **EC-C026 FORMAL_VERIFIED**: under an explicit clock(s)+n<100 hypothesis, every actual k≤n prefix and EVERY prospective raw step at k<n has clock<100. [Paper](proofs/EC-C026_RAW_CLOCK_BUDGET_CERTIFICATE.md), [evidence](sessions/evidence/S040/README.md). Gate Z pending; repetition/FIDE claim semantics and numerical KRK remain open.\n- Next: S041, exact-source Gate Z review of EC-C026.');p.write_text(t)
p=root/'docs/ROADMAP.md';t=p.read_text().replace('S040 targets an explicit-hypothesis prefix/prospective-ply clock certificate;', 'S040 formally verifies **EC-C026**, the explicit-hypothesis prefix/prospective-ply clock certificate ([paper](../proofs/EC-C026_RAW_CLOCK_BUDGET_CERTIFICATE.md), [evidence](../sessions/evidence/S040/README.md)); S041 Gate Z pending;');p.write_text(t)
(out/'README.md').write_text(f"""# S040 — EC-C026 Gate F evidence

Own published source `{sha}`, ONE NEW GitHub clone
`{s['fresh_clone']}`, no formal/.lake before build. Full **69-job build,
exit 0, {seconds}s**; COMPLETE AxiomCheck **exit 0**, **273 allowed reports**,
UTC **{utc}**. Main standard-three only. Full clean/working reports identical;
all source/transitive hashes and clean-source identity retained. Official core
Lean4.35.0 release eb6cafb7290e8bd5f2937522d8d804f58f02bafc; no dependency/shim.

commands.json retains clone, initial short-SHA checkout, exact FULL-SHA checkout,
toolchain/lake queries and ONE build/runner with exits/timings. Initial strict
HEAD assertion failed BEFORE any Lean command; initial-prebuild-failure.log
and initial-checkout.log record it. Same fresh clone resumed with exact SHA and
no .lake; no Lean command was repeated. Retained verifier has a guarded
--resume-prebuild option; default reproduction still requires a NEW clone.

Full lake-build.log, axioms-statements.log, working-build/axioms, source and
transitive hashes, toolchain/runtime identity, clean HEAD/tree/status, summary,
forbidden-token, preservation, ledger and document validation logs retained.
No unrelated diagnostics or new trivial tests. All prior source/records and
23 frozen ledger rows unchanged; aggregate imports/runner additive only.
No full compatible promotion/ep/castling/threshold game run. Hosted CI unobserved.

```sh
python sessions/evidence/S040/verify.py REPO_ROOT NEW_OUTPUT NEW_CLONE {sha}
python sessions/evidence/S040/validate.py
```

Conditional clock certificate only, not repetition/FIDE CanClaim semantics,
sufficient-budget lifting, numerical KRK mate bounds or new solved classes.
""")
table='\n'.join(l for l in (root/'docs/SESSION_PROGRESS.md').read_text().splitlines() if l.startswith('|'))
prompt=(root/'NEXT_SESSION.md').read_text().strip()
(root/'sessions/S040_RAW_CLOCK_BUDGET_CERTIFICATE.md').write_text(f"""# S040 — Conditional raw prefix and prospective-ply clock certificate

2026-10-20; base main 6b2d12a94bb72d4c22487aa6352501d6a0545cb7,
branch session/s040-clock-budget. Explicit all-heads fetch found no earlier
unmerged session. Existing checkout, publication authorised. Owner requested
consecutive sessions until stopped; S041 follows this completed session.

## Result and proof fidelity

**EC-C026 FORMAL_VERIFIED, Gate Z pending.** One new main in
RawClock/BudgetCertificate.lean, imports frozen EC-T0023 unchanged:

Under clock(s.trace)+n<100, EVERY k≤n and actual Extends k s u satisfies
clock(u.trace)<100 AND (k<n → EVERY RawBoardStep u v has clock(v.trace)<100).

The root budget is an explicit hypothesis; no numerical mate bound is supplied.
Full initial-rooted histories, actual Moves/legal witnesses and all raw replies
are retained. The prospective child is universally quantified, even outside a
strategy and for adverse/reset/draw-ending moves. It need not be played as a
claim action. k=n bounds only the current prefix; n=0 gives no prospective ply.
Proof applies frozen growth at k, and at k+1 via actual Extends.snoc, using
k+1≤n, monotone addition and transitivity. All units BOARD PLIES. No erased-board
surrogate, arbitrary seeded counter, endpoint-clock premise or terminal filter.
One theorem module, no extra definitions/redundant elementary declarations.

[Paper](../proofs/EC-C026_RAW_CLOCK_BUDGET_CERTIFICATE.md) and
[paper audit](../audits/EC-C026_RAW_CLOCK_BUDGET_PAPER.md) saved BEFORE Lean;
[Lean fidelity](../audits/EC-C026_RAW_CLOCK_BUDGET_LEAN.md). Same-agent review,
not independent external audit. Symbolic controls cover n=0, k=0, k=n, strict
99/100 boundary, quiet/reset/mixed paths, equal erasures with distinct histories,
and earlier raw draws. No concrete compatible full game was run/asserted.
Classical arithmetic, no novelty, tablebase, engine, enumeration or certificates.

## Observed checks and exact source

Published own exact source **{sha}** BEFORE one NEW GitHub clone
**{s['fresh_clone']}**, detached FULL SHA, no formal/.lake before build.
Full **69-job lake build, exit 0, {seconds}s**; COMPLETE **AxiomCheck exit 0**,
UTC **{utc}**, **273 allowed reports** (241 standard-three,
18 propext/Quot.sound, 9 propext, 5 axiom-free). Main standard-three only.
Exact statement inspected. Working/clean runner outputs identical; every
formal source matches exact anchor. Source/transitive hashes and clean-source
HEAD/tree/status retained. New module forbidden-token scan zero.

Incremental build/complete authoring runner passed FIRST ATTEMPT. The initial
fresh verifier invocation mistakenly used short SHA dd24ef3: clone/checkout
passed, strict full-HEAD comparison stopped BEFORE any Lean command. The same
new clone was observed at correct full SHA without .lake; retained prebuild
resume mode checked this, performed exact FULL-SHA checkout and ONE build/runner.
Original command records, short checkout and failure note retained. No Lean
build repeated; no formal statement weakened. Reproducer default still requires
a fresh clone; only infrastructure gained an explicit guarded resume option.

Official unmodified core Lean4.35.0 release eb6cafb7290e8bd5f2937522d8d804f58f02bafc,
no new dependency/shim. Existing elan/Git proxy sufficient, TLS/checksums unchanged.
Runtime current, connected, unrestricted/enforced, no new secret/configuration.
Hosted CI unobserved. [Full evidence](evidence/S040/README.md).
Relevant source/record preservation, ledger structure, evidence/table/full-prompt/
local-link/diff checks passed. No unrelated diagnostics or trivial tests.

## Preservation and limits

Twenty-three frozen bundles unchanged; no frozen source, prior candidate source,
paper, audit, session/evidence, manifest or ledger row edited. Aggregate Lean
files additive only. EC-C026 added and status grounded in observed Gate F.
The certificate proves no FIDE CanClaim predicate false, repetition certificate/
key correctness, no-earlier-terminal admissibility, current/intended claim
semantics, automatic fivefold/75-move adjudication, mate precedence, full Layer
A/B/C instance, strategy extraction, rule-aware lifting, numerical KRK bound,
holding/outcome, DTM/DTZ/WDL/Syzygy parity or initial-position value.
S041 installs separate exact-source Gate Z for this one module; full preceding
history and all defender claims remain separate. Session commits/pushes branch,
merges/pushes main and checks matching remote SHAs; final identity in Git history
and observed publication checks. Continuous execution proceeds to installed S041.

## Required progress table

{table}

{delta}

## Full installed S041 prompt

{prompt}
""")
p=root/'sessions/SESSION_LEDGER.md';t=p.read_text().replace('Full session closeouts live',f'| S040 | 2026-10-20 | EC-C026 conditional raw clock certificate (Gate L/F) | Explicit budget; all actual prefixes and EVERY prospective interior ply. Source `{sha}`; fresh 69-job build, 273 allowed reports. One new module; prior sources/records unchanged. S041 freeze installed. [Closeout](S040_RAW_CLOCK_BUDGET_CERTIFICATE.md) | None — 23 frozen bundles |\n\nFull session closeouts live');p.write_text(t)
print('Wrote S040 closeout and statuses from observed Gate F evidence.')
