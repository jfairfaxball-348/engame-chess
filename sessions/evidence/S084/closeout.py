"""Record S084 only after observed own-source fresh Gate F."""
import json,re
from pathlib import Path
r=Path(__file__).resolve().parents[3];s=json.loads((r/'sessions/evidence/S084/gate-f/summary.json').read_text(encoding='utf-8'))
assert s['build_exit']==s['axiom_statement_exit']==0 and s['complete_runner_matches_working']
def read(p):return (r/p).read_text(encoding='utf-8')
def write(p,t):(r/p).write_text(t,encoding='utf-8',newline='\n')
def append(p,t):write(p,read(p)+'\n'+t+'\n')
observed=f"OWN source `{s['proof_source']}`; NEW GitHub clone without .lake, full{s['build_jobs']}-job build exit0 in{s['build_seconds']}s; COMPLETE{s['total_axiom_reports']}-report runner exit0 at{s['verified_utc']}. Whole working/clean runner and exact published Git source bytes match. All8 main types/9 complete modules/imports inspected. Official native Windows Lean4.35.0; source/import/executable hashes, commands/exits/times/UTC, clean HEAD/tree/status retained. No source/dependency/shim/TLS/checksum changes; hosted CI unobserved."
delta='S084 formally verified automatic KRK incoming-count control at nondead clock0 and same-budget lifting of any supplied N<100 certificate; framed rank-six clock0 walls now have RAW W73/actual win without incoming premises.45 bundles frozen; full low-clock geometry/FIDE/global exact WDL-DTZ remain open.'
write('research/CANDIDATES.md',read('research/CANDIDATES.md').replace('Possible future IDs `EC-C049` onwards','Possible future IDs `EC-C050` onwards').replace('LOCAL_VERIFIED; incremental Lean passed, exact-source Gate F pending','FORMAL_VERIFIED (S084); separate Gate Z pending'))
for p in ['proofs/EC-C049_KRK_FRESH_HISTORY.md','audits/EC-C049_KRK_FRESH_HISTORY_LEAN.md','sessions/evidence/S084/README.md']:append(p,'Observed Gate F: '+observed+' Separate Gate Z pending.')
prompt=f'''# NEXT SESSION — S085: Freeze clock-zero KRK history and actual73 wall wins

Owner2026-10-21: continue KRK sessions until closure; stop before KQK. Fetch ALL
heads, reconcile unmerged work/latest main, commit/push branch, ordinary main
merge/push and compare identities.45 frozen bundles; next EC-T0046. Preserve
all prior complete frozen modules/records and45 ledger rows.

Direct EC-C049 milestone: actual admitted earlier-KRK prefix propagates Region;
at nondead clock0 no earlier KRK endpoint exists and every KRK query full count
<=1. New material-restricted lower-rank history lift, not the old all-material
histogram. ANY supplied clock-free KRK MateWithin N with N<100 lifts at clock0
to same N RAW certificate AND ActualWin, with NO incoming count/histogram input.
Concrete strong framed rank-six wall gives W73/ActualWin at clock0, both colours/
all actual flags/full original history/every defensive executed/intended move.
Nondeadness explicit in count lemma, derived from supplied clock-free winning;
child material obtained from CLOCK-FREE ForceMate, never circular RAW premise.
No actual history truncation or compatible-history witness from a local board.

Read paper, separate same-agent audits, all9 complete KRKFresh modules (including
private absent_count/shared Definitions),8 main types and imports. {observed}

Separate Gate Z: ONE NEW GitHub clone at FULL OWN SHA {s['proof_source']}, .lake
absent before full build/COMPLETE own runner. Compare ENTIRE own Gate F source/
transitive inventories and decoded complete output, not later aggregates. Native
official4.35.0/inherited environment; no Lean/dependency/shim/TLS/checksum change
or incremental substitute. Record full commands/logs/exits/times/UTC, all failures,
source/import/executable hashes and clean identity. Only after observed success
freeze EC-T0046 full9 modules/8 exact types/helpers/Definitions/transitive closure/
scope/trust/provenance and exactly one ledger row. Relevant ledger/preservation/
hash/type/link/diff/full prompt/full stable table checks; current statuses and
closeout with immediate delta. Publish/merge/compare exact remote main.

Return directly to S086 global geometric coverage. Exact next blocked step:
fresh clock0 lift needs a supplied N<100, but global strong-arrival bound is442.
Parametric setup costs B+4, so a PROVED uniform wall budget B<=95 would give
strong-arrival N<=99 and extend clock0 history-safe RAW wins to all strong legal
arrivals. Do not assume B95, a classical16-move maximum, or silently include weak
B+5=100 under a strict<100 lift. Attack a real all-defence geometric budget or
replacement box/confinement strategy, exposing every tempo/rook-safety/stalemate
branch. Existing73*(7-r) bound alone cannot yield95 at low rook ranks.

Standalone paper/attempt and separate adversarial audit BEFORE any new Lean;
no formal promotion unless every inequality/strategy branch closes. If blocked,
retain exact failed inequalities/uncovered geometric input family and the new
proof obligation; do not replace the principal attack with generic bookkeeping
or declare success from termination/strategy equivalence. Full arbitrary-clock/
incoming-history outcomes, FIDE rights/key/claim/adjudication and exact global
WDL/DTZ remain additional closure obligations. No tablebase/engine oracle/class
enumeration or stored certificates. Continue under owner authority, stop before
KQK. Every closeout includes stable progress table and exact mathematical delta.
'''
write('NEXT_SESSION.md',prompt)
progress=read('docs/SESSION_PROGRESS.md').replace('through S083','through S084').replace('actual winning-policy bridge frozen','actual winning-policy bridge frozen; clock0 history-free73 family formally verified')
progress=re.sub(r'Session change: [^\n]+','Session change: '+delta,progress);write('docs/SESSION_PROGRESS.md',progress)
table='| Endgames / target |'+progress.split('| Endgames / target |',1)[1].split('\n\n',1)[0]
for p in ['README.md','docs/ROADMAP.md','docs/KRK_COMPLETION.md']:append(p,delta+' [Paper]('+('../' if p.startswith('docs/') else '')+'proofs/EC-C049_KRK_FRESH_HISTORY.md).')
write('sessions/S084_KRK_FRESH_HISTORY.md',f'''# S084 — Actual clock-zero KRK history and incoming-count-free73 wall wins

2026-10-21, base83da892f7a082328873e4dafc174cde559569936, all heads
fetched/no unmerged work; branch session/s084-krk-fresh-history. S083 local/
main/remote session identities equal. Owner continues KRK until actual closure.
EC-C049 FORMAL_VERIFIED. {observed}
[Evidence](evidence/S084/README.md), [paper](../proofs/EC-C049_KRK_FRESH_HISTORY.md),
[paper audit](../audits/EC-C049_KRK_FRESH_HISTORY_PAPER.md),
[fidelity audit](../audits/EC-C049_KRK_FRESH_HISTORY_LEAN.md). Same-agent, not external.

Actual trace induction plus all-move closure excludes earlier KRK endpoints
at current nondead clock0. Every KRK query full count<=1; older larger-material
history remains physically counted. New restricted rank-history invariant
preserves every executed/intended weak reply and same supplied budget. Any
clock-free N<100 KRK certificate lifts at clock0 with NO incoming premises.
Concrete framed rank-six W73/ActualWin now follows from geometry and clock0
alone. Both colours/all actual flags/original histories. This removes actual
input hypotheses rather than changing definitions or assuming all-material
LowerRankHistory. No compatibility witness is asserted from a local board.

New partial RAW family,73 is an upper bound. Global all-strong geometry still
has442 bound>100; full arbitrary-clock/history outcomes, FIDE and global exact
WDL/DTZ OPEN.45 ledger rows unchanged; no oracle/tablebase/enumeration/certificates.
Initial projection/rewrite authoring errors retained and repaired with explicit
projections/full-list append counting, same statements. Older frozen sources/
warnings unchanged. Packaging/preservation/ledger/type/hash/link/table/prompt/
diff checks in evidence/S084/checks.log. S085 own-source freeze serves this
direct family; S086 returns to the precise missing global geometric ceiling.
Publication recorded by Git branch commit/push, ordinary main merge/push and
exact remote identity comparison. Stop before KQK.

{table}

Session change: {delta}

## Full installed next prompt

{prompt}''')
append('sessions/SESSION_LEDGER.md','| S084 | 2026-10-21 | Clock-zero KRK history and incoming-count-free73 walls (Gate F) | Actual KRK query counts<=1 at nondead clock0; supplied N<100 same-budget RAW/ActualWin, concrete framed73 family. Own source '+s['proof_source']+'; new208-job build/390 permitted reports. [Closeout](S084_KRK_FRESH_HISTORY.md) | None —45 bundles; new partial RAW input coverage |')
print(observed)
