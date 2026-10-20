"""Finalize exact raw threshold complement only from observed Gate F."""
import json
from pathlib import Path
root=Path(__file__).resolve().parents[3];out=root/'sessions/evidence/S058';s=json.loads((out/'summary.json').read_text());sha=s['proof_source'];assert sha=='c75b3760022717e586a789e47c09c03911a43a56' and s['build_exit']==s['axiom_statement_exit']==0
result=f"Own source `{sha}`; NEW GitHub clone `{s['fresh_clone']}`, no .lake before build. Full {s['build_jobs']}-job build exit 0, {s['build_seconds']}s; COMPLETE AxiomCheck exit 0 at {s['verified_utc']}, {s['total_axiom_reports']} allowed reports. Main standard-three; whole working/clean report identical."
checks='''Exact main inspected, full formal bytes match own anchor; full source/transitive
SHA256, clean HEAD/tree/status and full logs/commands/exits/times/UTC/toolchain
retained. Official core Lean4.35.0 release eb6cafb7290e8bd5f2937522d8d804f58f02bafc,
no dependency/shim/TLS/checksum change. New module forbidden scan zero. Initial
incremental unknown by_contra tactic failure retained; core Nat.lt_of_not_ge
resolved unchanged statement. Final incremental 84-job build/full working runner
passed without warnings; clean verification passed once, no repeated clean build.
Relevant ledger/evidence/preservation/full-table/full-prompt/local-link/diff checks
passed; prior protected files/32 rows unchanged, aggregate imports/runner additive.
No unrelated diagnostics/trivial tests. Hosted CI unobserved.'''
scope='''Exact IFF for every raw s: no AvailableThreshold iff rootclock<100/rootcount<3
and EVERY actual legal intended child clock<100/NEW endpoint OLD-history query<2.
Forward inject root/child threshold into availability, obtain strict Nat bounds;
frozen current append count+1 yields query<2. Reverse root/ALL child bounds refute
both disjuncts. Exact childclock retained, no sufficient root+1 budget substitution.
All actual Moves/promotions/flags/colours/indexed trace/hm retained. Root bounds
separate; no adverse move pruning/reset truncation/parent-current-query shortcut.'''
limits='''Raw bookkeeping NOT certified FIDE CanClaim/adjudication; no FIDE key/rights-history,
lawful no-earlier-terminal histories, automatic draw/mate precedence/claim protocol,
strategy lifting, numerical KRK, holding/outcome, WDL/DTZ or initial value.
Paper and separate adversarial audit saved BEFORE Lean; same-agent review, not
independent external audit. Boundaries99/100,2/3,zeroing/no-reply/pseudo-only controls
symbolic, no concrete full-game diagnostics/enumeration/oracle/certificates/novelty.'''
p=root/'research/CANDIDATES.md';t=p.read_text().replace('LOCAL_VERIFIED (S058, 2026-10-20); Gate F pending','FORMAL_VERIFIED (S058, 2026-10-20); Gate Z pending').replace('Raw bookkeeping only, no FIDE adjudication or KRK distance.',result+' [Evidence](../sessions/evidence/S058/README.md). Raw bookkeeping only, no FIDE adjudication or KRK distance.');p.write_text(t)
p=root/'audits/EC-C035_EXCLUSION_LEAN.md';p.write_text(p.read_text()+'\n## Observed Gate F\n\n'+result+'\n\n'+checks+'\n')
p=root/'docs/SESSION_PROGRESS.md';t=p.read_text().replace('through S057.','through S058.').replace('raw threshold prerequisites frozen |','raw threshold prerequisites frozen; exact threshold iff formally verified |');delta='Session change: S058 formally verified the exact raw current/intended threshold exclusion characterization; 32 bundles remain frozen and material-class coverage is unchanged.';t=t.replace(next(l for l in t.splitlines() if l.startswith('Session change:')),delta);p.write_text(t)
p=root/'README.md';t=p.read_text().replace('**After S057.**','**After S058.**').replace('- Next: S058, exact raw threshold exclusion characterization.','- Next: S059, separate own-source freeze of exact raw threshold exclusion.');t+='\n- S058: EC-C035 **FORMAL_VERIFIED**, exact current/ALL intended-child raw threshold exclusion iff. [Paper](proofs/EC-C035_EXACT_RAW_THRESHOLD_EXCLUSION.md), [evidence](sessions/evidence/S058/README.md).\n';p.write_text(t)
p=root/'docs/ROADMAP.md';p.write_text(p.read_text().replace('S058 targets exact raw threshold exclusion characterization.','S058 formally verified EC-C035, exact raw threshold exclusion iff ([paper](../proofs/EC-C035_EXACT_RAW_THRESHOLD_EXCLUSION.md), [evidence](../sessions/evidence/S058/README.md)); S059 separate freeze next.'))
(out/'README.md').write_text(f'''# S058 — Exact raw threshold exclusion Gate F

{result}

{scope}

{checks}

{limits}

Reproduce: `python sessions/evidence/S058/verify.py REPO_ROOT NEW_OUTPUT NEW_CLONE {sha}`
Validate: `python sessions/evidence/S058/validate.py`.
''')
table='\n'.join(l for l in (root/'docs/SESSION_PROGRESS.md').read_text().splitlines() if l.startswith('|'));prompt=(root/'NEXT_SESSION.md').read_text().strip()
(root/'sessions/S058_EXACT_RAW_THRESHOLD_EXCLUSION.md').write_text(f'''# S058 — Exact raw threshold exclusion characterization

2026-10-20, base main a8b026ead9d69ae0b069905687b7b2e7153f3c3c,
branch session/s058-exact-raw-threshold-exclusion. All-heads fetch, no prior
unmerged work, existing checkout; consecutive sessions/publication authorised.
EC-C035 FORMAL_VERIFIED, Gate Z pending.

{scope}

[Paper](../proofs/EC-C035_EXACT_RAW_THRESHOLD_EXCLUSION.md),
[paper audit](../audits/EC-C035_EXCLUSION_PAPER.md),
[Lean fidelity](../audits/EC-C035_EXCLUSION_LEAN.md).

{limits}

## Observed verification and publication

{result}

{checks}

[Evidence](evidence/S058/README.md). Own source pushed before clean clone;
closeout commit/push branch, merge/push main and remote identity verified,
retained in Git/observed publication. Continue installed S059 until stopped.

## Required progress table

{table}

{delta}

## Full installed S059 prompt

{prompt}
''')
p=root/'sessions/SESSION_LEDGER.md';t=p.read_text().replace('Full session closeouts live','| S058 | 2026-10-20 | EC-C035 exact raw threshold complement (Gate L/F) | Exact root/ALL legal-child clock/count exclusion iff. [Closeout](S058_EXACT_RAW_THRESHOLD_EXCLUSION.md) | None — 32 frozen bundles |\n\nFull session closeouts live');p.write_text(t)
print(result)
