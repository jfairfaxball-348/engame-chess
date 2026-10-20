"""Finalize S052 only after observed own-source Gate F."""
import json
from pathlib import Path
root=Path(__file__).resolve().parents[3];out=root/'sessions/evidence/S052';s=json.loads((out/'summary.json').read_text())
sha=s['proof_source'];assert sha=='7ada0bfa5731cae92a965a17d56695b4dbd221ef';assert s['build_exit']==s['axiom_statement_exit']==0
result=f"Own proof-source `{sha}`; NEW GitHub clone `{s['fresh_clone']}`, no .lake before build. Full {s['build_jobs']}-job build exit 0 in {s['build_seconds']}s; COMPLETE AxiomCheck exit 0 at {s['verified_utc']}; {s['total_axiom_reports']} allowed reports, main standard-three. Full working/clean report byte-identical."
p=root/'research/CANDIDATES.md';t=p.read_text().replace('LOCAL_VERIFIED (S052, 2026-10-20); Gate F pending','FORMAL_VERIFIED (S052, 2026-10-20); Gate Z pending').replace('No full FIDE identity iff, rights-history, claim or numerical KRK result.',result+' [Evidence](../sessions/evidence/S052/README.md). No full FIDE identity iff, rights-history, claim or numerical KRK result.');p.write_text(t)
p=root/'audits/EC-C032_KEY_CONGRUENCE_LEAN.md';p.write_text(p.read_text()+'\n## Observed Gate F\n\n'+result+'\nExact main inspected; all formal bytes match own anchor; full source/transitive\nhashes and clean HEAD/tree/status retained. Both new modules forbidden scan zero.\nOfficial core Lean4.35.0, no dependencies/shim. All authoring/fresh checks passed\nfirst attempt, no warning/failure/repeated clean build. Hosted CI unobserved.\n')
p=root/'docs/SESSION_PROGRESS.md';t=p.read_text().replace('through S051.','through S052.').replace('normalization prerequisites frozen |','normalization prerequisites frozen; key congruence formally verified |');delta='Session change: S052 formally verified equal normalized keys preserve legal moves and full legal endpoints; 29 bundles remain frozen and material-class coverage is unchanged.';t=t.replace(next(l for l in t.splitlines() if l.startswith('Session change:')),delta);p.write_text(t)
p=root/'README.md';t=p.read_text().replace('**After S051.**','**After S052.**').replace('- Next: S052, normalized-key legal-move congruence.','- Next: S053, separate exact-source freeze of normalized-key congruence.');t+='\n- S052: EC-C032 **FORMAL_VERIFIED**, equal full normalized keys have equal Boolean legality and full legal endpoints. [Paper](proofs/EC-C032_NORMALIZED_KEY_CONGRUENCE.md), [evidence](sessions/evidence/S052/README.md).\n';p.write_text(t)
p=root/'docs/ROADMAP.md';t=p.read_text().replace('S052 targets normalized-key congruence.','S052 formally verified EC-C032, normalized-key legal-move/full-legal-endpoint congruence ([paper](../proofs/EC-C032_NORMALIZED_KEY_CONGRUENCE.md), [evidence](../sessions/evidence/S052/README.md)); S053 separate freeze next.');p.write_text(t)
(out/'README.md').write_text(f'''# S052 — Normalized-key congruence Gate F

{result}

All formal source bytes match own anchor; full source/transitive SHA256,
clean HEAD/tree/status, full logs/commands/exits/times/UTC/toolchain retained.
Official core Lean4.35.0 release eb6cafb7290e8bd5f2937522d8d804f58f02bafc,
no dependencies/shim/TLS/checksum change. Both new modules forbidden scan zero.
All incremental/fresh authoring/build/runner checks passed first attempt, no
warnings/failures/repeated clean build. Hosted CI unobserved. Prior protected
records/source/29 rows unchanged; aggregates additive. Gate F complete, Gate Z
pending. No full FIDE identity iff/rights-history/adjudication or KRK distance.

Reproduce: `python sessions/evidence/S052/verify.py REPO_ROOT NEW_OUTPUT NEW_CLONE {sha}`
Validate: `python sessions/evidence/S052/validate.py`.
''')
table='\n'.join(l for l in (root/'docs/SESSION_PROGRESS.md').read_text().splitlines() if l.startswith('|'));prompt=(root/'NEXT_SESSION.md').read_text().strip()
(root/'sessions/S052_NORMALIZED_KEY_CONGRUENCE.md').write_text(f'''# S052 — Normalized-key legal-move congruence

2026-10-20, base main e5941b458609a9bb764e6a778729c4950e180b32;
branch session/s052-normalized-key-congruence. All-heads fetch, no unmerged prior
work, existing checkout; owner authorises consecutive sessions/publication.
EC-C032 FORMAL_VERIFIED, Gate Z pending.

## Result and audit

NEW shared noncomputable key := normalizeEP; ONE NEW main theorem module.
For all raw q,r under full normalized key equality, every actual Move m has
equal Boolean legality and FULL legal played endpoint. Both frozen normalization
legality equations compose via congrArg at exact normalized identity; obtain
r legality before its endpoint clause; compose full play equalities. No extra
history/material/terminal/colour/promotion restrictions, illegal raw endpoint
claim or adverse reply pruning. No global classical DecidableEq/hash/search.

Standalone [paper](../proofs/EC-C032_NORMALIZED_KEY_CONGRUENCE.md) and separate
[paper audit](../audits/EC-C032_KEY_CONGRUENCE_PAPER.md) saved BEFORE Lean;
[Lean review](../audits/EC-C032_KEY_CONGRUENCE_LEAN.md). Same-agent review,
not independent external audit. Full-record vs board-only/turn/rights/effective
marker premise controls, pseudo-only/pinned EP, promotions, king/castling,
source=destination, no legal moves and every actual reply treated symbolically
through frozen preservation. No concrete full-game diagnostic, enumeration/
engine/tablebase/stored certificate or novelty claim.

## Observed checks and publication

{result}
[Evidence](evidence/S052/README.md). Exact main inspected; all formal bytes match
own anchor, full source/transitive SHA256, clean HEAD/tree/status and full commands/
exits/times/UTC/toolchain retained. Official core Lean4.35.0 release
 eb6cafb7290e8bd5f2937522d8d804f58f02bafc, no dependencies/shim/TLS/checksum
change. Both new modules forbidden scan zero. Incremental changed modules/importer
79-job build and full working runner passed FIRST attempt, no warnings/failures.
One new successful clean run, no repeated build. Existing cloud/proxy sufficient;
hosted CI unobserved. Relevant ledger/evidence/preservation/full-table/full-prompt/
local-link/diff checks passed, all prior protected source/papers/audits/evidence/
manifests/29 rows unchanged, aggregates additive only. No unrelated diagnostics/
trivial tests. Own source published before clone. Commit/push/merge/push and remote
identity checks retained in Git/observed publication. Continue S053 unless stopped.

## Limits

One-way key congruence, not a full FIDE Article9.2.3 iff/converse, historical rights
validity, lawful histories/claims/adjudication/mate precedence, strategy lifting,
numerical KRK, holding/outcome, WDL/DTZ/Syzygy or initial-position result.

## Required progress table

{table}

{delta}

## Full installed S053 prompt

{prompt}
''')
p=root/'sessions/SESSION_LEDGER.md';t=p.read_text().replace('Full session closeouts live','| S052 | 2026-10-20 | EC-C032 normalized-key congruence (Gate L/F) | Equal keys imply equal Boolean legality and full legal endpoints, all raw q,r,m. [Closeout](S052_NORMALIZED_KEY_CONGRUENCE.md) | None — 29 frozen bundles |\n\nFull session closeouts live');p.write_text(t)
print(result)
