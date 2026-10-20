"""Write S062 closeout only after observed Gate F success."""
import json
from pathlib import Path
root=Path(__file__).resolve().parents[3];out=root/'sessions/evidence/S062'
s=json.loads((out/'summary.json').read_text());sha=s['proof_source'];assert s['build_exit']==s['axiom_statement_exit']==0
result=f"Own proof source `{sha}`; NEW GitHub clone `{s['fresh_clone']}`, .lake absent before build. Full {s['build_jobs']}-job build exit 0 ({s['build_seconds']}s); complete AxiomCheck exit 0 at {s['verified_utc']}, {s['total_axiom_reports']} allowed reports. Exact main inspected, standard-three axioms only; entire working/clean runner output and all formal bytes identical."
scope='''Admissible recurses on the actual initial-rooted indexed Trace: start True,
snoc requires admissible prior AND the exact parent State classifier ongoing.
The one main theorem combines the EVERY legal m/hm append IFF with EVERY Legal
reply lifting to admissible actual RawBoardStep and exact erased endpoint.
Guard is definitional after State cases; reply proof extracts the actual m/hm
witness and appends it. Terminal current endpoints/children are admitted; no
append after terminal parent. No legal reply is pruned. Optional claim
opportunities may be declined; successful/invalid claims and procedural phases
are absent from board-move traces.'''
limits='''This is stopped-history bookkeeping relative to the CHOSEN RAW classifier,
not certified full FIDE legal-history/rights-key/adjudication/claim correspondence.
No complete Layer, converse strategy lifting, numerical KRK, holding/outcome,
WDL/DTZ or initial-position value follows. Same-agent separate adversarial audit,
not independent external review. Zero/one-ply, terminal parent/child, exact
trace/hm, every terminal-ending reply, both colours/promotions/raw flags checked
symbolically; no full-game run/enumeration/oracle/certificates/novelty claim.'''
checks='''Paper and separate adversarial audit completed before Lean, then LOCAL_VERIFIED.
New definitions/main module, additive aggregate imports/runner; frozen sources
untouched. Working build and complete runner passed first attempt. One new GitHub
Gate F clone, no clean-build retry or failure. Full logs, commands/exits/times/UTC,
clean HEAD/tree/status, executable/toolchain identity, source/transitive SHA256
retained. Official core Lean4.35.0 release eb6cafb7290e8bd5f2937522d8d804f58f02bafc;
no dependency/shim/TLS/checksum changes. Runtime policy observation state unknown,
executor snapshot unrestricted, inherited proxy/CA sufficient. Hosted CI unobserved.
Relevant ledger tests/structure, evidence, preservation, full progress table/prompt,
local-link and diff checks passed. All prior protected files/34 ledger rows
unchanged. No unrelated diagnostics/trivial tests. Gate Z remains separate.'''
p=root/'research/CANDIDATES.md';p.write_text(p.read_text().replace('LOCAL_VERIFIED (S062, 2026-10-20); Gate F pending','FORMAL_VERIFIED (S062, 2026-10-20); Gate Z pending').replace('Actual initial-rooted indexed trace/m/hm retained;',result+' [Evidence](../sessions/evidence/S062/README.md). Actual initial-rooted indexed trace/m/hm retained;'))
p=root/'audits/EC-C037_STOPPED_HISTORY_LEAN.md';p.write_text(p.read_text().replace('Gate F evidence pending.','Gate F passed.\n\n'+result+'\n\n'+checks))
p=root/'docs/SESSION_PROGRESS.md';t=p.read_text().replace('through S061.','through S062.').replace('endpoint classifier prerequisites frozen |','endpoint classifier prerequisites frozen; stopped-history append/reply lifting formally verified |');delta='Session change: S062 formally verified stopped-history append and full legal-reply lifting relative to the raw classifier; 34 bundles remain frozen and material-class coverage is unchanged.';t=t.replace(next(l for l in t.splitlines() if l.startswith('Session change:')),delta);p.write_text(t)
p=root/'README.md';t=p.read_text().replace('**After S061.**','**After S062.**').replace('- Next: S062, stopped-history append and full legal-reply lifting.','- Next: S063, separate own-source freeze of stopped-history append and full legal-reply lifting.');t+='\n- S062: EC-C037 **FORMAL_VERIFIED**, exact stopped-history append guards and EVERY legal-reply lifting, including terminal children. [Paper](proofs/EC-C037_STOPPED_HISTORY_LIFTING.md), [evidence](sessions/evidence/S062/README.md). Gate Z pending; raw classifier-relative history only.\n';p.write_text(t)
p=root/'docs/ROADMAP.md';p.write_text(p.read_text().replace('S062 targets stopped-history append/full-reply lifting.','S062 formally verified EC-C037, stopped-history append/full-reply lifting ([paper](../proofs/EC-C037_STOPPED_HISTORY_LIFTING.md), [evidence](../sessions/evidence/S062/README.md)); S063 separate freeze next.'))
(out/'README.md').write_text(f'''# S062 — Stopped-history append/full-reply lifting Gate F

{result}

{scope}

{checks}

{limits}

Reproduce: `python sessions/evidence/S062/verify.py REPO_ROOT NEW_OUTPUT NEW_CLONE {sha}`.
Validate: `python sessions/evidence/S062/validate.py`.
''')
p=root/'NEXT_SESSION.md';p.write_text(p.read_text().replace('S062 develops EC-C037, exact stopped-history append/full legal-reply interface.', 'S062 FORMAL_VERIFIED EC-C037, exact stopped-history append/full legal-reply interface.\nOWN full proof-source SHA: '+sha+'.'))
table='\n'.join(l for l in (root/'docs/SESSION_PROGRESS.md').read_text().splitlines() if l.startswith('|'));prompt=(root/'NEXT_SESSION.md').read_text().strip()
(root/'sessions/S062_STOPPED_HISTORY_LIFTING.md').write_text(f'''# S062 — Stopped-history actual append and full legal-reply lifting

2026-10-20. Base main 12d6945f1aadd8e3b82410644d1c0f85bf8fd376,
branch session/s062-stopped-history-lifting. Fetched ALL remote heads; updated
existing main by fast-forward, all fetched prior heads already merged. Initial
checkout was stale S058, so fetched main's installed S062 governed the session.
EC-C037 FORMAL_VERIFIED; no theorem-ledger addition (34 frozen bundles).

{scope}

[Paper](../proofs/EC-C037_STOPPED_HISTORY_LIFTING.md),
[paper audit](../audits/EC-C037_STOPPED_HISTORY_PAPER.md),
[Lean fidelity audit](../audits/EC-C037_STOPPED_HISTORY_LEAN.md).

{limits}

## Observed verification and publication

{result}

{checks}

[Evidence](evidence/S062/README.md). Proof source committed and pushed before
fresh clone; closeout committed/pushed on session branch and merged/pushed to
main, with matching remote identities observed at publication. Full source SHA
and verified tree recorded in evidence; final closeout commit identified by Git.

## Required progress table

{table}

{delta}

## Full installed S063 prompt

{prompt}
''')
p=root/'sessions/SESSION_LEDGER.md';p.write_text(p.read_text().replace('Full session closeouts live','| S062 | 2026-10-20 | EC-C037 stopped-history append/full replies (Gate L/F) | Exact admissible ongoing-parent append iff; every legal reply lifted, terminal children retained. [Closeout](S062_STOPPED_HISTORY_LIFTING.md) | None — 34 frozen bundles |\n\nFull session closeouts live'))
print(result)
