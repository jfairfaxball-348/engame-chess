"""Finalize S050 only from observed own Gate F success."""
import json
from pathlib import Path
root=Path(__file__).resolve().parents[3];out=root/'sessions/evidence/S050';s=json.loads((out/'summary.json').read_text())
sha=s['proof_source'];assert sha=='4d47b33549fc5286099cae0bd89de76b05fbeb42';assert s['build_exit']==s['axiom_statement_exit']==0
result=f"Own proof-source `{sha}`; NEW GitHub clone `{s['fresh_clone']}`, no .lake before build. Full {s['build_jobs']}-job build exit 0 in {s['build_seconds']}s, COMPLETE AxiomCheck exit 0 at {s['verified_utc']}; {s['total_axiom_reports']} allowed reports, main standard-three. Full working/clean report byte-identical."
p=root/'research/CANDIDATES.md';t=p.read_text().replace('LOCAL_VERIFIED (S050, 2026-10-20); Gate F pending','FORMAL_VERIFIED (S050, 2026-10-20); Gate Z pending').replace('No full FIDE key/adjudication or numerical KRK claim.',result+' [Evidence](../sessions/evidence/S050/README.md). No full FIDE key/adjudication or numerical KRK claim.');p.write_text(t)
p=root/'audits/EC-C031_NORMALIZATION_LEAN.md';p.write_text(p.read_text()+'\n## Observed Gate F\n\n'+result+'\nFull source/transitive hashes, clean HEAD/tree/status and command/exits/times\nretained; exact main inspected, forbidden scan zero. Official core Lean4.35.0,\nno dependency/shim. No clean-build failure/repetition. Hosted CI unobserved.\n')
p=root/'docs/SESSION_PROGRESS.md';t=p.read_text().replace('through S049.','through S050.').replace('ordinary ep-irrelevance prerequisites frozen |','ordinary ep-irrelevance prerequisites frozen; normalization formally verified |').replace('| FIDE history/adjudication and distance |','| Concrete rule integration and distance |');delta='Session change: S050 formally verified effective-ep normalization preserves legal moves and their full endpoints; 28 bundles remain frozen and material-class coverage is unchanged.';t=t.replace(next(l for l in t.splitlines() if l.startswith('Session change:')),delta);p.write_text(t)
p=root/'README.md';t=p.read_text().replace('**After S049.**','**After S050.**').replace('- Next: S050, effective en-passant normalization preservation.','- Next: S051, separate exact-source freeze of effective ep normalization.');t+='\n- S050: EC-C031 **FORMAL_VERIFIED**, effective ep normalization preserves Boolean legality for every move and full endpoints of legal moves. [Paper](proofs/EC-C031_EFFECTIVE_EP_NORMALIZATION.md), [evidence](sessions/evidence/S050/README.md). No full FIDE repetition-key result.\n';p.write_text(t)
p=root/'docs/ROADMAP.md';t=p.read_text().replace('S050 targets effectiveEP normalization preservation.','S050 formally verified EC-C031: effectiveEP normalization preserves Boolean legality and full legal-move endpoints ([paper](../proofs/EC-C031_EFFECTIVE_EP_NORMALIZATION.md), [evidence](../sessions/evidence/S050/README.md)); S051 separate freeze next.');p.write_text(t)
(out/'README.md').write_text(f'''# S050 — Effective ep normalization Gate F

{result}

All formal source bytes match own anchor; full source/transitive SHA256,
clean HEAD/tree/status, full logs/commands/exits/times/UTC/toolchain retained.
Official core Lean4.35.0 release eb6cafb7290e8bd5f2937522d8d804f58f02bafc,
no dependency/shim/TLS/checksum change. Exact main inspected; both NEW modules
forbidden-token scan zero. Initial incremental simp unfolding failure retained,
fixed explicit rewriting without statement change; final incremental/full working
runner passed. No clean failure/repeated build. Hosted CI unobserved.
Prior sources/records/28 rows unchanged; aggregate imports/runner additive only.
Gate F complete, Gate Z pending. No full FIDE key/adjudication or KRK distance.

Reproduce: `python sessions/evidence/S050/verify.py REPO_ROOT NEW_OUTPUT NEW_CLONE {sha}`
Validate: `python sessions/evidence/S050/validate.py`.
''')
table='\n'.join(l for l in (root/'docs/SESSION_PROGRESS.md').read_text().splitlines() if l.startswith('|'));prompt=(root/'NEXT_SESSION.md').read_text().strip()
(root/'sessions/S050_EFFECTIVE_EP_NORMALIZATION.md').write_text(f'''# S050 — Effective ep normalization preserves legal play

2026-10-20. Base main 985854c4e852d68668d109b2fdbdfbb21665198f;
branch session/s050-effective-ep-normalization. Explicit all-heads fetch,
no prior unmerged work, existing checkout; consecutive sessions/publication
authorised by owner. EC-C031 FORMAL_VERIFIED, Gate Z pending.

## Result and audit

NEW shared normalizeEP definition and ONE NEW main theorem module. Every raw q,m:
Boolean legality unchanged by normalization, FULL played Position unchanged for
actual original legal moves. Available EP yields identity; absent EP/nonshape
uses frozen OrdinaryEP then same-turn self-check; absent EP/shape contradicts
original legality via legalEP_iff_shape and makes normalized pseudo false via
nonzero dx, empty dst and none marker. No unconditional raw illegal EP play
equality, history/material/terminal/colour/promotion restriction or reply pruning.

Standalone [paper](../proofs/EC-C031_EFFECTIVE_EP_NORMALIZATION.md) and separate
[adversarial paper audit](../audits/EC-C031_NORMALIZATION_PAPER.md) saved BEFORE
Lean. [Lean fidelity](../audits/EC-C031_NORMALIZATION_LEAN.md). Same-agent review,
not independent external audit. Symbolic missing/wrong-colour/nonpawn/king/castling,
same-file/occupied pawn/promotion/source=destination/both-colour/malformed-marker/
pseudo-only-self-check cases reviewed. No concrete pinned/compatible full-game
run, enumeration/engine/tablebase/stored certificate or novelty claim.

## Observed verification

{result}
[Evidence](evidence/S050/README.md). Exact main inspected; all formal bytes match
own anchor. Full formal/transitive hashes, clean HEAD/tree/status and full commands/
exits/times/UTC/toolchain retained. Official core Lean4.35.0 release
 eb6cafb7290e8bd5f2937522d8d804f58f02bafc; no dependencies/shim. Forbidden scan
zero on both NEW modules. First incremental simp unfolding failure retained;
explicit change/rw fixed unchanged statement; final 77-job incremental build/full
working runner passed without warnings. One new successful clean run, no repeated
clean build. Existing current connected runtime/proxy/CA sufficient, no setup/
TLS/checksum changes. Hosted CI unobserved. Relevant ledger/evidence/preservation/
full table/prompt/local-link/diff checks passed; prior source/papers/audits/evidence/
manifests and 28 rows unchanged, aggregates additive only. No unrelated diagnostics/
trivial tests. Own source published before clone; commit/push/merge/push and remote
identity checks retained in Git/observed publication, continuing S051 unless stopped.

## Limits

One normalization prerequisite, not full FIDE repetition key/rights-history,
claims/no-earlier-terminal/adjudication/mate precedence, strategy lifting,
numerical KRK, holding/outcome, WDL/DTZ/Syzygy or initial-position value.
Altered raw positions need not have compatible initial-rooted histories.
Remaining work described as concrete rule integration/distance to distinguish
already specified/frozen foundations from outstanding model/strategy obligations.

## Required progress table

{table}

{delta}

## Full installed S051 prompt

{prompt}
''')
p=root/'sessions/SESSION_LEDGER.md';t=p.read_text().replace('Full session closeouts live','| S050 | 2026-10-20 | EC-C031 effective ep normalization (Gate L/F) | Boolean legality and full legal endpoints preserved for every raw q,m. [Closeout](S050_EFFECTIVE_EP_NORMALIZATION.md) | None — 28 frozen bundles |\n\nFull session closeouts live');p.write_text(t)
print(result)
