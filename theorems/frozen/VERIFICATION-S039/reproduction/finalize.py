"""Finalize S039 only from an observed successful Gate Z summary."""
import csv,io,json,subprocess
from pathlib import Path
root=Path(__file__).resolve().parents[4]
out=root/'theorems/frozen/VERIFICATION-S039'
s=json.loads((out/'summary.json').read_text()); assert s['build_exit']==s['axiom_statement_exit']==0
sha=s['proof_source']; utc=s['verified_utc']; sec=s['build_seconds']
assert sha=='22243b9ca5769e1478c75a333befa3c8465c90f2'
assert (out/'axioms-statements.log').read_bytes()==(root/'sessions/evidence/S038/axioms-statements.log').read_bytes()
manifest=root/'theorems/frozen/EC-T0023/v1.md'; assert not manifest.exists()
manifest.parent.mkdir()
modules=s['complete_modules']
source='\n\n'.join('```lean\n'+(root/p).read_text()+'```' for p in modules)
statement=(out/'axioms-statements.log').read_text().split('inductive EndgameChess.Rules.RawTrace.Extends :')[1]
statement='inductive EndgameChess.Rules.RawTrace.Extends :'+statement
manifest.write_text(f"""# EC-T0023 v1 — Raw multi-step clock bound along actual trace extensions

**Status:** FROZEN (S039, 2026-10-20). Source candidate EC-C025.
**Own exact verified proof-source:** `{sha}`.
**Main:** EndgameChess.Rules.RawClock.clock_le_extension.

## Scope, sources and trust

For every actual Extends n s t, clock t.trace ≤ clock s.trace+n.
Extends zero retains the EXACT raw State. Its successor uses frozen RawBoardStep
with actual Move, source legality proof and exact append equality. Full initial-
rooted trace is retained; n counts actual board plies, including reset edges.
No endpoint-clock hypothesis, ReachK surrogate, arbitrary clock seed, material,
side, strategy or earlier-terminal filter occurs. Equal erased boards cannot
identify unrelated histories. Induction uses frozen append_clock_le, addition
monotonicity and transitivity; resets are included without assuming quietness.

[Paper](../../../proofs/EC-C025_RAW_CLOCK_EXTENSION_BOUND.md),
[paper audit](../../../audits/EC-C025_RAW_CLOCK_EXTENSION_PAPER.md),
[Lean audit](../../../audits/EC-C025_RAW_CLOCK_EXTENSION_LEAN.md), and
[S039 fidelity review](../VERIFICATION-S039/fidelity-review.md).
Reviews are same-agent, not independent external review. Classical finite-path
induction, no novelty claim, engine, tablebase, enumeration or stored certificate.
Rule edition FIDE Laws effective 2023-01-01, existing Article 3 legal-move kernel;
raw history/counter component only. No new English-FIDE correspondence claim.
Trusted: official Lean kernel and standard three axioms, A1 and existing
owner-reviewed FIDE-to-kernel encoding (2026-10-18). No new axiom is introduced.

No sufficient-budget lifting, numerical KRK mate bound, repetition certificate,
no-earlier-terminal admissibility, key correctness, current/intended claims,
fivefold/75-move adjudication, mate precedence, full Layer A/B/C instance,
holding/outcome theorem, DTM/DTZ/WDL/Syzygy parity or initial-position value.
h+n<100 remains a future certificate HYPOTHESIS. All raw replies are retained,
including adverse draw-ending children. No solved material-class upgrade.

## Immutable complete module boundary

- formal/EndgameChess/Rules/RawTrace/ExtensionDefinitions.lean
- formal/EndgameChess/Rules/RawClock/ExtensionBound.lean

Both COMPLETE modules, including shared definitions and constructor signatures,
are frozen byte-for-byte. Their transitive closure includes unchanged EC-T0021
and EC-T0022 sources. Corrections require new modules/version under the protocol.

## Exact definitions, public statement and axiom report

```text
{statement.strip()}
```

{source}

## Observed independent Gate Z run

ONE NEW GitHub clone `{s['fresh_clone']}`, detached at this own exact SHA;
formal/.lake absent before build. Full lake build: **68 jobs, exit 0, {sec}s**.
COMPLETE AxiomCheck: **exit 0**, verified UTC **{utc}**.
272 allowed reports, including 5 axiom-free; this main uses only
**[propext, Classical.choice, Quot.sound]**. Full output byte-identical to actual
S038 Gate F report. All source/import bytes matched own exact anchor/current
main. Clean HEAD/tree/status and full command exits/timings retained.
Official unmodified core Lean4.35.0 release
 eb6cafb7290e8bd5f2937522d8d804f58f02bafc; no dependencies/host shim.
Existing elan/Git proxy reused; TLS/checksum validation unchanged.
Hosted CI **unobserved**. This run certifies this bundle only.
[Full evidence](../VERIFICATION-S039/README.md).

## Transitive dependency SHA-256 inventory

```text
{(out/'dependency-sha256.txt').read_text()}```
""")
p=root/'theorems/LEDGER.csv'; old=p.read_bytes(); rows=list(csv.DictReader(io.StringIO(old.decode())))
assert len(rows)==22 and 'EC-T0023' not in [r['theorem_id'] for r in rows]
fields=list(rows[0]); row=dict.fromkeys(fields,'')
row.update(theorem_id='EC-T0023',title='Raw multi-step clock bound along actual trace extensions',statement_path='theorems/frozen/EC-T0023/v1.md',local_proof_path='proofs/EC-C025_RAW_CLOCK_EXTENSION_BOUND.md',lean_file=modules[1],lean_declaration=s['bundle_declarations'][0],lean_toolchain='leanprover/lean4:v4.35.0',proof_commit_sha=sha,verified_utc=utc,rule_edition='FIDE Laws of Chess 2023 legal-move kernel; raw history component only',manifest_path='theorems/frozen/EC-T0023/v1.md',status='FROZEN',notes='From EC-C025. New exact-source Gate Z. Both complete extension definition/proof modules frozen; standard three axioms. Raw clock growth only; no numerical KRK bound or full FIDE lifting.')
buf=io.StringIO(newline='');csv.DictWriter(buf,fieldnames=fields,lineterminator='\n').writerow(row)
p.write_bytes(old+buf.getvalue().encode())
p=root/'research/CANDIDATES.md';t=p.read_text().replace('FORMAL_VERIFIED (S038, 2026-10-20); Gate Z pending','**FROZEN as [EC-T0023](../theorems/frozen/EC-T0023/v1.md)** (S039, 2026-10-20)');p.write_text(t)
p=root/'docs/SESSION_PROGRESS.md';t=p.read_text().replace('through S038. Twenty-two','through S039. Twenty-three').replace('these are not twenty-two solved','these are not twenty-three solved').replace('raw traces and counter frozen; multi-step clock bound formally verified','raw traces, counter and multi-step clock bound frozen');t=t.replace(next(l for l in t.splitlines() if l.startswith('Session change:')),'Session change: S039 froze the raw multi-step clock bound as EC-T0023 after a new exact-source Gate Z check; 23 bundles are frozen and material-class coverage is unchanged.');p.write_text(t)
p=root/'README.md';t=p.read_text().replace('**After S038.** Twenty-two frozen theorem bundles (not twenty-two solved material classes).','**After S039.** Twenty-three frozen theorem bundles (not twenty-three solved material classes).').replace('- Next: S039, separate exact-source Gate Z review of EC-C025.', '- S039: EC-C025 frozen as [EC-T0023](theorems/frozen/EC-T0023/v1.md) after a new exact-source Gate Z build and complete axiom audit. All prior source/records unchanged.\n- Next: S040, conditional raw prefix and prospective-ply clock certificate.');p.write_text(t)
p=root/'docs/ROADMAP.md';t=p.read_text().replace('Gate Z is pending in S039; no numerical KRK bound, repetition certificate or sufficient-budget lifting follows.','S039 froze it as EC-T0023 after a new exact-source Gate Z build (68 jobs; 272 allowed reports). Twenty-three frozen bundles, no new solved material class. S040 targets an explicit-hypothesis prefix/prospective-ply clock certificate; no numerical KRK bound, repetition certificate or sufficient-budget lifting follows.');p.write_text(t)
p=root/'theorems/README.md';t=p.read_text().replace('EC-T0007–EC-T0022 were first frozen','EC-T0007–EC-T0023 were first frozen').replace('Current frozen count: **22 bundles**, not twenty-two solved','Current frozen count: **23 bundles**, not twenty-three solved');t+='\nS039: [EC-T0023](frozen/EC-T0023/v1.md) freezes raw multi-step clock growth on actual trace extensions. [Evidence](frozen/VERIFICATION-S039/README.md). Twenty-three bundles; class coverage unchanged.\n';p.write_text(t)
(out/'README.md').write_text(f"""# S039 — EC-C025 Gate Z evidence

ONE NEW GitHub clone at own exact published SHA `{sha}`;
formal/.lake absent before build. Full **68-job build, exit 0, {sec}s**;
complete AxiomCheck **exit 0**, **272 allowed reports**, UTC **{utc}**.
Exact Extends constructors/main statement inspected; main standard-three only.
Entire report byte-identical to actual S038 Gate F; all source/import bytes match.
Official unmodified core Lean4.35.0 release eb6cafb7290e8bd5f2937522d8d804f58f02bafc.
No dependencies/shim, changed TLS/checksum settings, engine/tablebase or diagnostics.
Hosted CI unobserved. EC-C025 frozen as EC-T0023; raw scope only.

Full build/statement logs, commands/exits/timings, toolchain/lake identity,
pre-build assertions, source/transitive hashes, clean-source identity and UTC
summary are retained here. fidelity-review.md records symbolic controls and
paper correspondence. Validation/preservation/ledger logs are separate.
All prior formal source/papers/audits/evidence/manifests and 22 ledger rows
remain unchanged. Only one new frozen bundle, not a new solved material class.

```sh
python theorems/frozen/VERIFICATION-S039/reproduction/verify.py REPO_ROOT NEW_OUTPUT NEW_CLONE {sha}
python theorems/frozen/VERIFICATION-S039/reproduction/validate.py REPO_ROOT
```
""")
table='\n'.join(l for l in (root/'docs/SESSION_PROGRESS.md').read_text().splitlines() if l.startswith('|'))
delta=next(l for l in (root/'docs/SESSION_PROGRESS.md').read_text().splitlines() if l.startswith('Session change:'))
prompt=(root/'NEXT_SESSION.md').read_text().strip()
(root/'sessions/S039_FREEZE_RAW_CLOCK_EXTENSION.md').write_text(f"""# S039 — Freeze the raw multi-step clock bound

2026-10-20, base main ad32029316149927cc7dc6190de49f3d5837b9a4,
branch session/s039-freeze-clock-extension. Explicit all-heads fetch; no earlier
unmerged remote sessions. Existing checkout, publication authorised. Owner
requested consecutive sessions until stopped; S040 follows this closeout.

## Result and observed evidence

**EC-C025 frozen as EC-T0023**, twenty-three bundles, not solved material classes.
No Lean source changes. Paper/fidelity review confirms exact-state zero,
actual Move/legal/append successor, full trace retention on resets, all raw
replies, and absence of erased-history substitution or terminal filtering.
Reviewed actual prior proof/audits/manifests, Gate F logs, summary, source
identities and frozen definitions. Same-agent review, not external independence.
Symbolic zero/quiet/reset/mixed/equal-erasure/earlier-draw controls found no gap;
no fixed initial-rooted promotion/ep/castling/threshold prefix run or asserted.
Classical induction, no novelty, oracle, tablebase, engine or enumeration.

Own proof-source **{sha}**, one NEW fresh GitHub Gate Z clone
**{s['fresh_clone']}**, detached exact SHA; no formal/.lake before build.
Full **68-job lake build, exit 0, {sec}s**; COMPLETE AxiomCheck **exit 0**,
UTC **{utc}**, **272 allowed reports**. Main standard-three only.
Full output byte-identical to actual Gate F; source/transitive hashes and clean
HEAD/tree/status retained. Official core Lean4.35.0 release
 eb6cafb7290e8bd5f2937522d8d804f58f02bafc; no dependencies/host shim.
Existing elan/Git proxy used, TLS/checksums unchanged. Runtime observations
current, connected, unrestricted/enforced; no secret or configuration changes.
Hosted CI unobserved. [Evidence](../theorems/frozen/VERIFICATION-S039/README.md).

One immutable manifest/new ledger row. Prior source, papers, audits, session
records/evidence, manifests and 22 ledger rows preserved. Relevant ledger,
preservation, evidence and document checks passed; no unrelated diagnostic
suite or new trivial tests. No incremental Lean build needed since no source
changed. Commit/push session branch, merge/push main and compare remote SHAs;
final publication identity is in Git history and observed publication checks.

## Limits and next obligation

No new mathematical coverage: raw clock(t)≤clock(s)+n only. No sufficient-budget
lifting, numerical KRK bound, repetition or full FIDE admissibility/adjudication,
claim semantics/mate precedence, full Layer instance, holding/outcome,
DTM/DTZ/WDL/Syzygy or initial-position result. h+n<100 stays a HYPOTHESIS.
S040 targets the current prefix and EVERY prospective one-ply successor under
that explicit bound, with k<n essential for the latter; no repetition inference.

## Required progress table

{table}

{delta}

## Full installed S040 prompt

{prompt}
""")
p=root/'sessions/SESSION_LEDGER.md';t=p.read_text().replace('Full session closeouts live',f'| S039 | 2026-10-20 | Freeze EC-C025 actual-trace clock bound (Gate Z) | New exact-source 68-job build; 272 allowed reports, main standard-three; full Gate F equality and source preservation. S040 conditional clock certificate installed. [Closeout](S039_FREEZE_RAW_CLOCK_EXTENSION.md) | **+1 → EC-T0023 FROZEN** (23 bundles) |\n\nFull session closeouts live');p.write_text(t)
print('Created EC-T0023 manifest/ledger row and complete S039 closeout from observed success.')
