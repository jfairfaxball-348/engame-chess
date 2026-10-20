"""Finalize concrete occurrence-count result from observed Gate F only."""
import json
from pathlib import Path
root=Path(__file__).resolve().parents[3];out=root/'sessions/evidence/S054';s=json.loads((out/'summary.json').read_text())
sha=s['proof_source'];assert sha=='9fccb2f46c0edcd358c25885b1f4cdae0f770233';assert s['build_exit']==s['axiom_statement_exit']==0
result=f"Own proof-source `{sha}`; NEW GitHub clone `{s['fresh_clone']}`, no .lake before build. Full {s['build_jobs']}-job build exit 0 in {s['build_seconds']}s; COMPLETE AxiomCheck exit 0 at {s['verified_utc']}, {s['total_axiom_reports']} allowed reports. Main standard-three; full working/clean report identical."
p=root/'research/CANDIDATES.md';t=p.read_text().replace('LOCAL_VERIFIED (S054, 2026-10-20); Gate F pending','FORMAL_VERIFIED (S054, 2026-10-20); Gate Z pending').replace('No FIDE threshold/adjudication result.',result+' [Evidence](../sessions/evidence/S054/README.md). No FIDE threshold/adjudication result.');p.write_text(t)
p=root/'audits/EC-C033_OCCURRENCES_LEAN.md';p.write_text(p.read_text()+'\n## Observed Gate F\n\n'+result+'\nExact main inspected; all formal bytes match own anchor; full source/transitive\nhashes, clean HEAD/tree/status and full commands/exits/times/UTC/toolchain retained.\nBoth NEW modules forbidden scan zero. Official core Lean4.35.0, no dependencies/\nshim. All authoring/fresh checks first attempt, no warning/failure/repeated clean\nbuild. Hosted CI unobserved. Gate Z pending.\n')
p=root/'docs/SESSION_PROGRESS.md';t=p.read_text().replace('through S053.','through S054.').replace('normalization/key-congruence prerequisites frozen |','normalization/key-congruence prerequisites frozen; concrete count law formally verified |');delta='Session change: S054 formally verified the current normalized-key occurrence append law; 30 bundles remain frozen and material-class coverage is unchanged.';t=t.replace(next(l for l in t.splitlines() if l.startswith('Session change:')),delta);p.write_text(t)
p=root/'README.md';t=p.read_text().replace('**After S053.**','**After S054.**').replace('- Next: S054, full normalized-key current occurrence append law.','- Next: S055, separate exact-source freeze of the normalized-key count law.');t+='\n- S054: EC-C033 **FORMAL_VERIFIED**, current count after append queries the NEW endpoint key in the OLD full history, plus one. [Paper](proofs/EC-C033_NORMALIZED_KEY_OCCURRENCES.md), [evidence](sessions/evidence/S054/README.md).\n';p.write_text(t)
p=root/'docs/ROADMAP.md';t=p.read_text().replace('S054 targets concrete normalized-key occurrence bookkeeping.','S054 formally verified EC-C033, concrete current normalized-key occurrence append law ([paper](../proofs/EC-C033_NORMALIZED_KEY_OCCURRENCES.md), [evidence](../sessions/evidence/S054/README.md)); S055 separate freeze next.');p.write_text(t)
(out/'README.md').write_text(f'''# S054 — Concrete normalized-key occurrences Gate F

{result}

Exact main inspected, all formal bytes match own anchor; full source/transitive
SHA256, clean HEAD/tree/status, full logs/commands/exits/times/UTC/toolchain retained.
Official core Lean4.35.0 release eb6cafb7290e8bd5f2937522d8d804f58f02bafc,
no dependency/shim/TLS/checksum change; both new modules forbidden scan zero.
All authoring/fresh checks passed first attempt without warnings/failures/repeated
clean build. Hosted CI unobserved. Prior protected files/30 rows unchanged,
aggregates additive. Gate F complete, Gate Z pending. No threshold/adjudication.

Reproduce: `python sessions/evidence/S054/verify.py REPO_ROOT NEW_OUTPUT NEW_CLONE {sha}`
Validate: `python sessions/evidence/S054/validate.py`.
''')
table='\n'.join(l for l in (root/'docs/SESSION_PROGRESS.md').read_text().splitlines() if l.startswith('|'));prompt=(root/'NEXT_SESSION.md').read_text().strip()
(root/'sessions/S054_NORMALIZED_KEY_OCCURRENCES.md').write_text(f'''# S054 — Current normalized-key occurrence append law

2026-10-20, base main 6d4d125905fdbd30eeda11042eb467b4500fd10b;
branch session/s054-normalized-key-occurrences. Explicit all-heads fetch,
no unmerged prior work, existing checkout; consecutive sessions/publication
authorised. EC-C033 FORMAL_VERIFIED; Gate Z pending.

## Exact result and audit

NEW shared occurrences wrapper uses frozen full normalized key and local classical
DecidableEq Position; currentOccurrences queries actual endpoint. ONE NEW main:
for every s,m,hm actual legal append, new current count equals old FULL history
queried at NEW endpoint plusone. Unfold actual append/erase/wrappers, specialize
frozen generic append_occurrences, reflexive indicator=1. Actual indexed trace/hm
unchanged; no proof-irrelevance shortcut, reset truncation/terminal/reply filter.
Full root/prior/current endpoints retained. No global executable hash/search.

Standalone [paper](../proofs/EC-C033_NORMALIZED_KEY_OCCURRENCES.md) and separate
[paper audit](../audits/EC-C033_OCCURRENCES_PAPER.md) BEFORE Lean;
[Lean review](../audits/EC-C033_OCCURRENCES_LEAN.md). Same-agent review,
not independent external audit. Symbolic [A,B,A] thenB control rejects old-current-
plus-one, not an actual compatible game run. Both colours/all flags/promotions/
castling/EP/every legal reply; no artificial append without hm. No concrete full
game diagnostic, enumeration/engine/tablebase/stored certificate/novelty claim.

## Observed verification

{result}
[Evidence](evidence/S054/README.md). All formal bytes match own anchor; full
source/transitive hashes, clean HEAD/tree/status and full commands/exits/times/UTC/
toolchain retained. Official core Lean4.35.0 release
 eb6cafb7290e8bd5f2937522d8d804f58f02bafc, no dependencies/shim/TLS/checksum change.
Both new modules forbidden scan zero. Incremental 81-job build/complete working
runner passed first attempt, no warnings/failures; one successful new clean run,
no repeated build. Existing environment/proxy sufficient; hosted CI unobserved.
Relevant ledger/evidence/preservation/full-table/full-prompt/local-link/diff checks
passed; every prior protected source/paper/audit/evidence/manifest/30 rows unchanged,
aggregates additive only. No unrelated diagnostics/trivial tests. Own source pushed
before clone; closeout commit/push/merge/push and remote identity checked and
retained in Git/observed publication. Continue S055 under owner authorisation.

## Limits

Concrete chosen-key count law, no full FIDE identity/rights-history correspondence,
repetition threshold/claim/adjudication/mate precedence, lawful histories, strategy
lifting, numerical KRK, holding/outcome, WDL/DTZ/Syzygy or initial-position result.

## Required progress table

{table}

{delta}

## Full installed S055 prompt

{prompt}
''')
p=root/'sessions/SESSION_LEDGER.md';t=p.read_text().replace('Full session closeouts live','| S054 | 2026-10-20 | EC-C033 concrete normalized-key current count (Gate L/F) | Full-history count of NEW endpoint plusone after every actual legal append. [Closeout](S054_NORMALIZED_KEY_OCCURRENCES.md) | None — 30 frozen bundles |\n\nFull session closeouts live');p.write_text(t)
print(result)
