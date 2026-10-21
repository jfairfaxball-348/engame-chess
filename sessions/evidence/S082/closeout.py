"""Close S082 only after observed own-source fresh Gate F."""
import json,re
from pathlib import Path
r=Path(__file__).resolve().parents[3];s=json.loads((r/'sessions/evidence/S082/gate-f/summary.json').read_text(encoding='utf-8'))
assert s['build_exit']==s['axiom_statement_exit']==0 and s['complete_runner_matches_working']
def read(p):return (r/p).read_text(encoding='utf-8')
def write(p,t):(r/p).write_text(t,encoding='utf-8',newline='\n')
def append(p,t):write(p,read(p)+'\n'+t+'\n')
observed=f"OWN source `{s['proof_source']}`; NEW GitHub clone without .lake, full{s['build_jobs']}-job build exit0 in{s['build_seconds']}s; COMPLETE{s['total_axiom_reports']}-report AxiomCheck exit0 at{s['verified_utc']}. Whole working/clean runner and exact published Git source bytes match. All8 main types/9 complete modules and imports inspected. Official native Windows Lean4.35.0; complete source/import/executable hashes, clean HEAD/tree/status, commands/exits/times/UTC retained. No source/dependency/shim/TLS/checksum changes; hosted CI unobserved."
delta='S082 formally verified independent actual bounded winning policies iff full RAW forcing on every admitted KRK history, exact same-B certificate extraction and actual terminal mate continuations.44 bundles frozen; geometric low-clock coverage, full FIDE and global exact WDL/DTZ remain open.'
write('research/CANDIDATES.md',read('research/CANDIDATES.md').replace('Possible future IDs `EC-C048` onwards','Possible future IDs `EC-C049` onwards').replace('LOCAL_VERIFIED; incremental Lean passed, exact-source Gate F pending','FORMAL_VERIFIED (S082); separate Gate Z pending'))
for p in ['proofs/EC-C048_KRK_WINNING_POLICY.md','audits/EC-C048_KRK_WINNING_POLICY_LEAN.md','sessions/evidence/S082/README.md']:append(p,'Observed Gate F: '+observed+' Separate Gate Z pending.')
prompt=f'''# NEXT SESSION — S083: Freeze actual RAW KRK winning-policy correspondence

Owner2026-10-21: continue consecutive sessions until KRK closes; stop before
KQK. Fetch ALL heads, reconcile unmerged work/latest main; commit/push branch,
ordinary merge/push main, compare identities.44 frozen bundles, next EC-T0045.
Preserve every earlier complete frozen module/record and prior44 ledger rows.

Direct EC-C048 milestone: ActualWin is independent actual global legal history
policy + all-prefix outcome/claim safety + UNIFORM finite B bound. On every
admitted exact KRK history or terminal Region, ActualWin iff full old F.
ANY bounded winning policy gives the EXACT B-ply old certificate. Actual maximal
endpoints and a genuine terminal continuation are named mate within fuel.
Every opponent child and correct current/intended claim retained; claims0 plies,
never passes. No generic F-preserving-no-cycle assumption: KRK fuel supplies cap.
Both named/material colours/turns/all actual flags and complete incoming traces/
clocks/counts. No evaluated low-clock geometric formula/FIDE/global WDL-DTZ.

Read standalone paper, separate same-agent paper/fidelity audits, all9 complete
KRKWinning modules (all helpers/shared definitions),8 main types and imports.
{observed}

Gate Z: ONE NEW GitHub clone at FULL OWN SHA {s['proof_source']}, .lake absent
before full build and COMPLETE OWN AxiomCheck. Compare ENTIRE own Gate F source/
transitive inventories and full decoded runner, not later aggregate outputs.
Native official pinned4.35.0/inherited environment; no Lean/dependency/shim/TLS/
checksum changes or incremental substitute. Record full command/log/exits/times/
UTC, source/import/executable hashes, clean identity and retained failures.
Only after observed success freeze EC-T0045 with all9 complete modules/helpers,
8 exact types/full source boundary/transitive closure/scope/trust/provenance,
exactly one row. Relevant ledger/preservation/type/hash/link/diff checks; update
all current statuses, stable table/immediate delta, full prompt and closeout.
Publish/merge/compare remote main; return directly to low-clock KRK history.

S084 candidate EC-C049: attack the concrete low-clock incoming-history gap.
Target a history-unrestricted clock-zero rank-six framed-wall RAW winning family,
using the proved73-ply geometry. Existing LowerRankHistory ranges over ALL earlier
material and is too broad; earlier larger-material repeats cannot match future
KRK boards. Prove from actual strict-prefix admission and all-move material
closure that an earlier exact KRK prefix forces every later ongoing prefix into
exact same-colour KRK; a rook capture is dead and cannot be followed by a move.
At a last clock-reset step ending nondead, any earlier KRK prefix would make
that reset impossible (quiet retained KRK or dead KK). Hence an admitted nondead
clock-zero KRK root has NO earlier KRK endpoints: each matching KRK query key
occurs only at current root, at most1. Do not prune arbitrary earlier history
without this proof or assume an arbitrary compatible count vector.

Use the smallest KRK-restricted lower-rank count invariant, preserved by actual
rank-policy append, to remove the original incoming assumptions in the clock0
wall family. It is NOT enough to assert the old all-material histogram follows.
Paper and separate audit BEFORE any additive Lean; if the route blocks, record
the exact missing statement/inequality and keep the input scope open. No unrelated
generic detours or class-completion claims. Low-clock ALL-board geometry, full
FIDE correspondence and exact global WDL/DTZ still required. No oracle/tablebase/
class enumeration or stored per-position certificates. Continue direct KRK
work under owner authority; stop before KQK.
'''
write('NEXT_SESSION.md',prompt)
progress=read('docs/SESSION_PROGRESS.md').replace('through S081','through S082').replace('strong nonloss/high-clock criteria frozen','strong nonloss/high-clock criteria frozen; actual winning-policy bridge formally verified').replace('Full FIDE, low-clock geometric coverage, actual winning-policy bridge and global exact distance','Full FIDE, low-clock geometric coverage and global exact distance')
progress=re.sub(r'Session change: [^\n]+','Session change: '+delta,progress);write('docs/SESSION_PROGRESS.md',progress)
table='| Endgames / target |'+progress.split('| Endgames / target |',1)[1].split('\n\n',1)[0]
for p in ['README.md','docs/ROADMAP.md','docs/KRK_COMPLETION.md']:append(p,delta+' [Paper]('+('../' if p.startswith('docs/') else '')+'proofs/EC-C048_KRK_WINNING_POLICY.md).')
write('sessions/S082_KRK_WINNING_POLICY.md',f'''# S082 — Independent actual RAW KRK winning-policy correspondence

2026-10-21, base9b09e381ab07722940d3b37609caf263f2dd3dba. Branch
session/s082-krk-winning-policy; all heads fetched/no unmerged work, S081
local/main/remote session identities observed equal. Owner continues KRK.

EC-C048 FORMAL_VERIFIED. {observed}
[Evidence](evidence/S082/README.md), [paper](../proofs/EC-C048_KRK_WINNING_POLICY.md),
[paper audit](../audits/EC-C048_KRK_WINNING_POLICY_PAPER.md),
[fidelity audit](../audits/EC-C048_KRK_WINNING_POLICY_LEAN.md). Same-agent, not external.

ActualWin independently requires globally legal full-history policy, all-prefix
named terminal outcomes/opponent no-claim/own Some moves AND a uniform board-ply
horizon. F-preserving choices alone can cycle generically; existing KRK fuel
provides the missing horizon. Converse extracts EXACT W(B) from ANY bounded
actual winning policy by prefix induction, retaining all opponent moves/claims.
Every maximal endpoint and an actual continuation are genuine named terminal
mate, not merely fuel0. Both named/material colours/turns/all actual flags and
full incoming histories/clocks/counts, zero-root mate and mate150 retained.

Direct strategy semantics obligation discharged; NO new evaluated geometric
input family. Full low-clock classification, full FIDE correspondence and exact
global WDL/DTZ OPEN.44 ledger rows/frozen records unchanged. Nine new complete
modules/eight main declarations, aggregate importer/runner only; no oracle,
tablebase, enumeration or stored certificates. Initial dependent Option case
equality repaired with same statement; full failed working logs retained.
Earlier frozen deprecation warnings unchanged. Relevant preservation/ledger/
hash/type/link/table/prompt/diff checks in evidence/S082/checks.log are packaging
evidence only. S083 freeze serves this direct obligation, then concrete clock0
history restriction attack. Publication recorded by Git commit/push branch,
ordinary main merge/push and exact remote identity comparison.

{table}

Session change: {delta}

## Full installed next prompt

{prompt}''')
append('sessions/SESSION_LEDGER.md','| S082 | 2026-10-21 | Actual RAW KRK winning-policy correspondence (Gate F) | Independent legal bounded policy iff F, exact B certificate and actual terminal mate continuation. Own source '+s['proof_source']+'; new199-job build/382 permitted reports. [Closeout](S082_KRK_WINNING_POLICY.md) | None —44 bundles; strategy bridge, no evaluated geometric coverage |')
print(observed)
