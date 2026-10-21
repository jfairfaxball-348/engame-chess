"""Close S080 only after observed exact-own-source Gate F."""
import json,re
from pathlib import Path
r=Path(__file__).resolve().parents[3];s=json.loads((r/'sessions/evidence/S080/gate-f/summary.json').read_text(encoding='utf-8'))
assert s['build_exit']==s['axiom_statement_exit']==0 and s['complete_runner_matches_working']
def read(p):return (r/p).read_text(encoding='utf-8')
def write(p,t):(r/p).write_text(t,encoding='utf-8',newline='\n')
def append(p,t):write(p,read(p)+'\n'+t+'\n')
observed=f"OWN source `{s['proof_source']}`; NEW GitHub clone without .lake, full{s['build_jobs']}-job build exit0 in{s['build_seconds']}s; COMPLETE{s['total_axiom_reports']}-report AxiomCheck exit0 at{s['verified_utc']}. Whole working/clean runner and published Git source bytes match. All10 public types/11 complete modules and transitive imports inspected. Official native Windows Lean4.35.0; source/import/executable hashes, commands/exits/times/UTC and clean HEAD/tree/status retained. No dependency/shim/TLS/checksum change. Hosted CI unobserved."
delta='S080 formally verified universal strong RAW holding/weak nonforcing, exact ongoing high-clock criteria (weak h>=99; strong h>=98 iff immediate mate), and exact one-ply budget on those wins.43 bundles remain frozen; low-clock geometry, actual winning-policy bridge, full FIDE and global WDL/DTZ remain open.'
candidate=read('research/CANDIDATES.md').replace('Possible future IDs `EC-C047` onwards','Possible future IDs `EC-C048` onwards').replace('LOCAL_VERIFIED; incremental Lean passed, exact-source Gate F pending','FORMAL_VERIFIED (S080); separate Gate Z pending');write('research/CANDIDATES.md',candidate)
for p in ['proofs/EC-C047_KRK_HIGH_CLOCK.md','audits/EC-C047_KRK_HIGH_CLOCK_LEAN.md','sessions/evidence/S080/README.md']:append(p,'Observed Gate F: '+observed+' Separate Gate Z pending.')
prompt=f'''# NEXT SESSION — S081: Freeze strong RAW nonloss and exact high-clock KRK

Owner2026-10-21: continue consecutive KRK sessions until closure; stop before
KQK. Fetch ALL heads, reconcile earlier unmerged work/latest main; commit/push
branch, ordinary merge/push main and compare identities.43 frozen bundles;
next free EC-T0044. Preserve prior43 rows/records and all older frozen modules.

Direct milestone EC-C047: all-history actual strong holding/weak nonforcing;
ongoing weak h>=99 strong nonforcing+weak policy; ongoing strong h>=98 forcing
iff actual immediate mate, exact winning budget1/not0. Both turns/colours/all
actual flags and incoming full trace/counts. Root ongoing mandatory for clock
criteria, terminal mate at150 retained; no universal quiet-witness assumption.
Full low-clock geometric classification, actual winning-policy correspondence,
full FIDE and exact global WDL/DTZ remain open. No class closure inferred.

Read exact paper, separate same-agent paper/Lean audits, all11 complete new
KRKHighClock modules and10 main types/imports. {observed}

Separate Gate Z: ONE NEW GitHub clone at FULL OWN SHA {s['proof_source']}, .lake
absent before full build and COMPLETE own AxiomCheck. Compare ENTIRE own Gate F
source/transitive inventories and complete decoded runner, not later aggregates.
Native official pinned4.35.0/inherited environment; no source/toolchain/dependency/
shim/TLS/checksum changes or incremental substitute. Record full logs/commands/
exits/times/UTC, all failures/retries, source/import/executable hashes and clean
identity. Hosted CI only passed if actually observed. Only then freeze EC-T0044
with all11 complete modules/helpers/Definitions, all10 verbatim types and full
transitive closure/trust/scope/provenance; exactly one new ledger row. Relevant
ledger/preservation/hash/type/link/diff/full prompt/stable table checks. Update
all current statuses, full session closeout/table/immediate delta; publish/merge.

Return directly to S082 candidate EC-C048: actual winning policies corresponding
to full finite rule-forcing certificates on every admitted RAW KRK history.
Exact blocked step: holding duality and certificate recurrences alone do not
prove an ACTUAL winner policy forces named mate against every move/claim. Define
winning independently: globally legal total history policy, own ongoing moves
never select a claim, every opponent ongoing prefix has NO correct current/
intended claim, every terminal prefix is named mate, and a UNIFORM finite board-
ply cap prevents vacuous infinite play. Extract a policy preserving full F;
universal KRK fuel gives its cap. Converse extracts W(B) by induction on actual
policy horizon B, preserving every opponent child, not by renaming RW. Prove
bounded actual terminal continuation and mate, including all zero-ply claims.
This is the smallest direct strategy-soundness gap; exit back to low-clock
history/geometry and correct distances after it closes. Paper/separate audit
BEFORE additive Lean and all exact-source gates. No oracle/tablebase/class
enumeration or stored certificates. Do not claim this generic bridge decides
the remaining low-clock boards or completes FIDE/WDL/DTZ. Continue until actual
KRK closure under owner authority; stop before KQK.
'''
write('NEXT_SESSION.md',prompt)
progress=read('docs/SESSION_PROGRESS.md').replace('through S079','through S080')
progress=progress.replace('all-history RAW holding frozen','all-history RAW holding frozen; strong nonloss/high-clock criteria formally verified')
progress=progress.replace('Concrete FIDE integration, geometric outcome coverage and exact distance','Full FIDE, low-clock geometric coverage, actual winning-policy bridge and global exact distance')
progress=re.sub(r'Session change: [^\n]+','Session change: '+delta,progress);write('docs/SESSION_PROGRESS.md',progress)
table='| Endgames / target |'+progress.split('| Endgames / target |',1)[1].split('\n\n',1)[0]
for p in ['README.md','docs/ROADMAP.md','docs/KRK_COMPLETION.md']:append(p,delta+' [Paper]('+('../' if p.startswith('docs/') else '')+'proofs/EC-C047_KRK_HIGH_CLOCK.md).')
write('sessions/S080_KRK_HIGH_CLOCK.md',f'''# S080 — Universal strong nonloss and exact high-clock RAW KRK criteria

2026-10-21, base970d7ee7cc180920ef55e52d9b68da3dbe74b32a; branch
session/s080-krk-high-clock. S079 local/main/remote branch identities matched,
all heads fetched/no unmerged work. Owner continues KRK until closure.

EC-C047 FORMAL_VERIFIED. {observed}
[Evidence](evidence/S080/README.md), [paper](../proofs/EC-C047_KRK_HIGH_CLOCK.md),
[paper audit](../audits/EC-C047_KRK_HIGH_CLOCK_PAPER.md),
[fidelity audit](../audits/EC-C047_KRK_HIGH_CLOCK_LEAN.md). Same-agent, not external.

NEW input coverage: every admitted KRK root strong-holds and weak cannot force;
on ongoing weak h>=99 strong cannot force and weak holds; on ongoing strong
h>=98 forcing iff an actual immediate mate move, exactly1 optimal board ply
on wins. All incoming history/count/clock/flags, both material/player colours.
Mate149->150 included. Initial-rooted king safety and KRK-or-dead invariant,
actual intended claim before execution, all chosen/universal child quantifiers
retained. No failed sufficient73 predicate is used as a draw proof.

Still OPEN: low-clock arbitrary-history geometry, independent actual winning
policy bridge, full FIDE correspondence and global exact WDL/DTZ. No class
closure.43 frozen ledger rows unchanged; additive source only. The initial
dependent-clock elaboration failure was fixed with explicit stored append
equality; all working attempts retained. Failed documentation patch contexts
made no changes. Earlier frozen deprecated-if warnings retained unchanged.
Relevant preservation/ledger/source/type/hash/link/table/prompt/diff checks
in evidence/S080/checks.log are packaging evidence only. S081 separate freeze
serves these actual outcome inputs, then S082 closes the precise winning-policy
gap before returning to low-clock geometry. Publication recorded by Git commit/
push branch, ordinary main merge/push and exact remote identity comparison.

{table}

Session change: {delta}

## Full installed next prompt

{prompt}''')
append('sessions/SESSION_LEDGER.md','| S080 | 2026-10-21 | Strong nonloss and exact high-clock RAW KRK (Gate F) | All-history strong holding; weak h>=99 nonforcing/hold; strong h>=98 forcing iff mate-in1 with exact budget1. Own source '+s['proof_source']+'; new190-job build/374 permitted reports. [Closeout](S080_KRK_HIGH_CLOCK.md) | None —43 bundles; new partial RAW outcome/distance coverage |')
print(observed)
