"""Record observed Gate F and install the separate own-source holding freeze."""
import json,re
from pathlib import Path
r=Path(__file__).resolve().parents[3]
s=json.loads((r/'sessions/evidence/S078/gate-f/summary.json').read_text(encoding='utf-8'))
assert s['build_exit']==s['axiom_statement_exit']==0 and s['complete_runner_matches_working']
def read(p):return (r/p).read_text(encoding='utf-8')
def write(p,t):(r/p).write_text(t,encoding='utf-8',newline='\n')
def append(p,t):write(p,read(p)+'\n'+t+'\n')
observed=f"OWN proof-source `{s['proof_source']}`; NEW GitHub clone without .lake, full{s['build_jobs']}-job build exit0 in{s['build_seconds']}s; complete{s['total_axiom_reports']}-report AxiomCheck exit0 at{s['verified_utc']}. Full working/clean runner and published Git source bytes match; source/transitive/executable hashes and clean identity retained. Official native Windows Lean4.35.0; inherited environment, no toolchain/dependency/shim/TLS/checksum changes. Hosted CI unobserved."
delta='S078 formally verified actual legal all-history RAW KRK holding policies iff opponent nonforcing, plus bounded stopped compliant play.42 bundles remain frozen; geometric outcome characterisation, full FIDE correspondence and exact WDL/DTZ remain open.'
candidate=read('research/CANDIDATES.md').replace('`n| EC-C046','\n| EC-C046').replace('Possible future IDs `EC-C046` onwards','Possible future IDs `EC-C047` onwards').replace('LOCAL_VERIFIED; incremental Lean passed, exact-source Gate F pending','FORMAL_VERIFIED (S078); separate Gate Z pending')
write('research/CANDIDATES.md',candidate)
for p in ['proofs/EC-C046_KRK_HOLDING.md','audits/EC-C046_KRK_HOLDING_LEAN.md','sessions/evidence/S078/README.md']:
    append(p,'Observed exact-source Gate F: '+observed+' Separate Gate Z pending.')
prompt=f'''# NEXT SESSION — S079: Freeze actual all-history RAW KRK holding

Owner 2026-10-21: continue consecutive sessions until KRK closes; stop before
KQK. Fetch ALL remote heads, merge earlier unmerged work, latest main, commit/
push branch, ordinary merge/push main and compare exact identities. Preserve
all42 frozen records and older complete modules; exactly one new row if Gate Z
passes, next free ID EC-T0043. No paper/Lean edits or incremental substitutes.

Direct KRK milestone: EC-C046 genuine policy holding/complement relationship
for EVERY existing admitted RAW KRK history. This freeze serves complete
outcome/holding, not a generic library detour. Read standalone paper, separate
same-agent paper/fidelity audits and all eleven complete KRKHolding modules,
ten public main types, full imports and S078 observed own-source evidence.
{observed}

Use ONE NEW GitHub clone at FULL OWN SHA {s['proof_source']}, .lake absent before
full build and COMPLETE matching OWN AxiomCheck. Compare ENTIRE own-source and
transitive inventories plus complete decoded runner to S078 Gate F, not later
aggregate inventories. Record exact source/import/executable hashes, commands/
exits/timings/UTC, all failures/retries, clean HEAD/tree/status and exact types.
Use native official pinned Lean4.35.0 and inherited environment on this host.
No dependency/shim/TLS/checksum changes. No hosted CI success without inspection.

Exact theorem: independently defined actual globally legal history policy and
all-compliant-prefix opponent-mate avoidance iff NOT full opponent RuleForceMate
on KRK-or-terminal Region. Fuel saturation supplies uniform child budgets;
every opponent reply retained, correct present/intended claims stop at0 board
plies, policy None never passes. Bounded compliant paths; maximal endpoint is
raw terminal OR own selected correct claim, stopped continuation exists. Both
player/material colours, turns, actual flags/all incoming trace/clock/counts.
No geometric evaluation of the full forcing predicate or FIDE/parity inferred.

Only after observed success create EC-T0043 full immutable manifest: all11
complete modules/private helpers/shared Definitions, all10 observed exact types,
full transitive closure, scope/trust/provenance. Add exactly one ledger row,
prior42 unchanged. Relevant ledger/structure/preservation/type/hash/link/diff/
full prompt/stable table checks. Update all current authority/status files,
full session closeout and immediate delta; publish/merge and verify remote main.

Then return directly to KRK-specific outcomes, S080: prove exact high-clock
strong-win criteria and all-history strong holding where the argument closes.
Target ongoing weak-turn h>=99: legal rook capture draws, or a quiet intended
claim is available; strong turn h>=98 wins iff an actual legal move mates
immediately. Retain every history/current/intended count and mate-first at150;
prove actual RAW assertions, never treat a failed sufficient family as draw.
Paper and separate adversarial audit BEFORE additive Lean. Do not assume all
rook endgames win within a classical numeric maximum without kernel proof.
Complete low-clock/history geometry, full FIDE correspondence and exact WDL/DTZ
remain separate closure obligations; no tablebase/oracle/class enumeration or
stored position certificates. Continue under owner authority, stop before KQK.
'''
write('NEXT_SESSION.md',prompt)
progress=read('docs/SESSION_PROGRESS.md').replace('through S077','through S078')
progress=progress.replace('bounds and universal RAW termination frozen','bounds and universal RAW termination frozen; all-history RAW holding formally verified')
progress=progress.replace('Concrete FIDE integration, complete rule-aware outcomes/holding and exact distance','Concrete FIDE integration, geometric outcome coverage and exact distance')
progress=re.sub(r'Session change: [^\n]+','Session change: '+delta,progress)
write('docs/SESSION_PROGRESS.md',progress)
table='| Endgames / target |'+progress.split('| Endgames / target |',1)[1].split('\n\n',1)[0]
for p in ['README.md','docs/ROADMAP.md','docs/KRK_COMPLETION.md']:
    append(p,delta+' [Paper]('+('../' if p.startswith('docs/') else '')+'proofs/EC-C046_KRK_HOLDING.md).')
write('sessions/S078_KRK_HOLDING.md',f'''# S078 — Actual all-history admitted RAW KRK holding policies

2026-10-21. Base main a9cea278ecd680f661a464f24fb20416a96a1efc, branch
session/s078-krk-holding. Earlier S077 merged/pushed, all three exact identities
observed equal. Owner authorised consecutive KRK work until closure.

EC-C046 FORMAL_VERIFIED, separate Gate Z pending. {observed}
[Gate F evidence](evidence/S078/README.md), [paper](../proofs/EC-C046_KRK_HOLDING.md),
[paper audit](../audits/EC-C046_KRK_HOLDING_PAPER.md),
[Lean audit](../audits/EC-C046_KRK_HOLDING_LEAN.md). Same-agent, not external review.

Genuine holding strategy is defined independently as a globally legal full-history
policy and safety at EVERY compliant finite prefix. It is proved equivalent to
opponent nonforcing on all admitted exact KRK histories and terminal Region.
Uniform fuel saturation makes defensive choice possible; own claim stops rather
than passes. Maximal compliant endpoints are terminal or a selected correct
claim; stopped continuation exists within frozen fuel. Every opponent board
reply and both current/intended claims retained. All incoming histories/counts/
clocks, both colours/turns/all actual flags. No geometric outcome evaluation,
full FIDE correspondence or exact WDL/DTZ established; KRK remains OPEN.

Authoring reused ignored native cache only for incremental work, followed by
the mandatory genuinely new own-source clean build. Initial core tactic,
projection and dependent-induction mistakes and Windows console-print failure
were corrected; full original failures/logs retained. Prior frozen modules
unchanged, including replayed deprecated-if warnings.42 ledger rows unchanged.
Relevant packaging/preservation checks are in evidence/S078/checks.log.
Publication recorded in Git by commit/push branch, ordinary merge/push main
and exact remote identity comparison. Next freeze serves this direct milestone;
return immediately to specific high-clock outcomes after S079.

{table}

Session change: {delta}

## Full installed next prompt

{prompt}''')
append('sessions/SESSION_LEDGER.md','| S078 | 2026-10-21 | All-history RAW KRK holding policies (Gate F) | Actual legal policy/complement iff and bounded stopped compliant play. Own source '+s['proof_source']+'; new179-job build/364 permitted reports. [Closeout](S078_KRK_HOLDING.md); S079 separate own-source freeze | None —42 frozen bundles; full KRK closure open |')
print(observed)
