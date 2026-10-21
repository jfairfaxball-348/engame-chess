"""Freeze only the exact normalized C051 source after its separate fresh Gate Z."""
import csv,io,json,subprocess
from pathlib import Path
r=Path(__file__).resolve().parents[3]
e=r/'theorems/frozen/VERIFICATION-S088'
s=json.loads((e/'summary.json').read_text(encoding='utf-8'))
assert s['gate']=='Z' and s['entire_own_gate_f_inventory_and_complete_runner_match']
assert s['total_axiom_reports']==395 and len(s['bundle_declarations'])==5 and len(s['complete_modules'])==6
assert not (r/'theorems/frozen/EC-T0047').exists()
identity=json.loads((e/'clean-source-identity.json').read_text(encoding='utf-8'))
assert identity['status']==identity['tracked_diff']==''
def read(p):return (r/p).read_text(encoding='utf-8')
def write(p,t):
    (r/p).parent.mkdir(parents=True,exist_ok=True)
    (r/p).write_text(t,encoding='utf-8',newline='\n')
old=read('theorems/LEDGER.csv')
assert len(list(csv.DictReader(io.StringIO(old))))==46
sha=s['proof_source']
observed=f"Own published source `{sha}`; SEPARATE NEW GitHub clone `{s['fresh_clone']}`, .lake absent before full{s['build_jobs']}-job build exit0 in{s['build_seconds']}s. COMPLETE395-report axiom/type runner exit0 at{s['verified_utc']}. Entire own Gate F source/transitive inventories, exact main types and full runner match; standard-three axioms only. Official native Windows Lean4.35.0/inherited environment; full commands/exits/times/UTC, source/import/executable hashes and clean identities retained. Hosted CI unobserved."
scope='''For either strong material colour and arbitrary actual flags, exact strong-turn
KRK, S=(a-1,b-1), R=(a,b), W strictly NE,1<=a<=2,1<=b<=6:
an actual legal all-reply phase reaches BoxCorner within at most FOUR pairs,
EIGHT board plies. The right branch has R=(a+1,b),S=(a,b-1),W.x>a+1;
the left crossing branch pays two extra king/reply escort pairs and ends at
R=(a+1,b),S=(a+2,b-1),W.x<a+1. All weak endpoints remain above b.
Every weak node has an explicit legal reply; the rook is protected throughout,
all actual legal weak replies are retained and no rook capture is allowed.

Both actual endpoint widths6-a and a+1 pay the eight-ply worst-case cap in
the potential8*((w-4)+(h-4)), with NATURAL subtraction. The phase relation's
done constructor pads only after the endpoint holds; pair requires actual
Legal, turns, NONEMPTY reply set and EVERY bounded weak continuation. This
is a finite chess control certificate, not an assumed strategy or surrogate
legality. The private pair helper and shared definitions are included in full.

The fixed16-ply ordinary kernel sequence from White Kc3/Rd4, Black Ke5 returns
the EXACT full Position, all16 moves legal. It falsifies only the naive width4
escort policy. No infinite RAW play or counterexample to a better global95
strategy is inferred. decide is kernel checked; no native_decide is used.

IMPORTANT SCOPE LIMIT: normalized large-box phase ONLY. The paper's <=32-ply
repeated/reflected/axis small-box-entry corollary is NOT a frozen declaration.
No arbitrary guarded entry, small-box mating finish, global sub100 ceiling,
complete low-clock/history outcome formula, full FIDE correspondence or exact
global WDL/DTZ. The phase is clock-free; no full initial history is invented.
Legal-move kernel follows the project's FIDE2023 scope; full history/rules
correspondence remains open. No tablebase/engine oracle, exhaustive class proof
or stored per-position value certificates. Classical geometry, no novelty claim.
'''
manifest=f'''# EC-T0047 v1 — Guarded large-box contraction phase and width4 control

FROZEN (S088,2026-10-21), candidate EC-C051.
Representative: EndgameChess.Rules.krk_guarded_large_box_phase.
Full own verified proof source `{sha}`.

## Exact scope and trust

{scope}
## Proof, audits and observed verification

[Standalone paper](../../../proofs/EC-C051_KRK_GUARDED_BOX_PHASE.md),
[separate paper audit](../../../audits/EC-C051_KRK_GUARDED_BOX_PAPER.md),
[Lean fidelity audit](../../../audits/EC-C051_KRK_GUARDED_BOX_LEAN.md).
Paper/separate same-agent audit preceded Lean, not independent external review.
Five public main declarations/six complete modules/definitions/private helpers
reviewed. Earlier source and frozen records remain unchanged.

{observed}

[Gate Z summary](../VERIFICATION-S088/summary.json),
[commands](../VERIFICATION-S088/commands.json),
[complete build](../VERIFICATION-S088/lake-build.log),
[full runner](../VERIFICATION-S088/axioms-statements.log),
[all source hashes](../VERIFICATION-S088/source-sha256.txt),
[transitive imports](../VERIFICATION-S088/dependency-sha256.txt),
[clean identity](../VERIFICATION-S088/clean-source-identity.json).

## Immutable full module boundary

All six COMPLETE modules including private helpers/shared Definitions freeze
at the above SHA. Corrections or strengthening require a new module/ID.

```text
'''+ '\n'.join(s['complete_modules'])+'\n```\n\n## New main declaration types and axioms\n\n```text\n'
runner=(e/'axioms-statements.log').read_text(encoding='utf-8')
start=runner.index("'EndgameChess.Rules.krk_box_reply_exists'")
manifest+=runner[start:]+'\n```\n\n## Exact own-source transitive inventory\n\n```text\n'+(e/'dependency-sha256.txt').read_text(encoding='utf-8')+'```\n'
write('theorems/frozen/EC-T0047/v1.md',manifest)
row=['EC-T0047','Guarded large-box KRK contraction phase and width-four cycle','theorems/frozen/EC-T0047/v1.md','proofs/EC-C051_KRK_GUARDED_BOX_PHASE.md','formal/EndgameChess/Rules/KRKBox/Phase.lean','EndgameChess.Rules.krk_guarded_large_box_phase','leanprover/lean4:v4.35.0',sha,s['verified_utc'],'FIDE Laws of Chess 2023 (effective 2023-01-01)','theorems/frozen/EC-T0047/v1.md','FROZEN','Normalized NE widths5/6; actual all-reply phase<=8 plies and cost inequalities; fixed16-ply cycle refutes naive width4 extension. Five main declarations/six complete modules; own-source separate Gate F/Z. Paper32 corollary not frozen; global mate/RAW/FIDE/WDL-DTZ remain open.']
buf=io.StringIO(newline='');csv.writer(buf,lineterminator='\n').writerow(row)
write('theorems/LEDGER.csv',old+('' if old.endswith('\n') else '\n')+buf.getvalue())
candidate=read('research/CANDIDATES.md').replace('FORMAL_VERIFIED (S087); separate Gate Z pending','FROZEN as EC-T0047 (S088), own-source separate Gate Z passed')
write('research/CANDIDATES.md',candidate)
progress=read('docs/SESSION_PROGRESS.md').replace('through S087. Forty-six','through S088. Forty-seven')
progress=progress.replace('normalized guarded large-box phase formally verified, awaiting freeze','normalized guarded large-box phase frozen')
start=progress.index('Session change:');end=progress.index('\n\n',start)
delta='Session change: S088 freezes EC-T0047 after a separate fresh own-source Gate Z: normalized guarded large-box phase<=8 plies, both cost inequalities and the fixed16-ply width4 control.47 bundles frozen; no new mathematical scope beyond S087. Arbitrary entry/small-box finish/global sub100 and full KRK closure remain OPEN.'
progress=progress[:start]+delta+progress[end:]
write('docs/SESSION_PROGRESS.md',progress)
road=read('docs/KRK_COMPLETION.md')
road=road.replace('## S087 direct geometry advance', '''## S088 verification update — KRK NOT CLOSED

EC-C051 is now FROZEN as EC-T0047 after separate fresh own-source Gate Z.
47 bundles; normalized guarded width5/6 phase<=8 plies, both cost inequalities
and fixed16-ply width4 cycle only. S087 scope limits below remain. The next
principal geometry target is a safe small-box mating finish and costed entry.

## S087 direct geometry advance''',1)
write('docs/KRK_COMPLETION.md',road)
prompt='''# NEXT SESSION — S089: Close the guarded small-box mating phase

Owner2026-10-21: continue consecutive sessions until KRK is closed, no inferred
pause or new approval gate. Fetch ALL heads/reconcile unmerged work/latest main;
commit/push branch, ordinary main merge/push and exact remote identity comparison.
Stop before KQK; preserve all frozen sources/records.47 frozen bundles.

New direct geometry: EC-T0047 freezes OWN source
84161c2650b902e98f37252532a706ec50f40ed4 after S087 Gate F and S088 separate
fresh Gate Z,214-job builds and complete395 permitted axiom/type reports.
Read C051 paper, separate paper/Lean audits, full new modules and exact source
manifests. The FORMAL result is NORMALIZED NE guarded widths5/6 contraction
within8 plies with EVERY actual weak reply, both endpoint cost inequalities,
and a fixed16-ply kernel cycle defeating the naive width4 extension. The paper
repeated/reflected/axis <=32-ply SMALL-BOX ENTRY corollary is NOT a frozen
declaration and is NOT mate. No full history symmetry is assumed.

Principal EC-C050 global sub100 remains PROPOSED/open. Exact next obligation:
an actual all-defence mating policy for guarded boxes with both dimensions<=4,
or another genuine global sub100 strong-arrival strategy. Use a new well-posed
numeric statement, explicit invariant/potential, rook protection/nonempty and
nonstalemate conditions, EVERY weak reply and all paid king/rook tempos.
Guarded normal input S=(a-1,b-1), R=(a,b), W.x>a,W.y>b with3<=a,b<=6;
reflect/transpose only through proved geometric/kernel interfaces. Need to
handle the 1x1 corner and width4 crossing/cycle explicitly, not assume monotone
box shrink. Choose derived cap F, not an unproved classical number. Full
arbitrary guarded-box entry has separate cost E. Any integrated wall target
must actually pay entry+large-box phase+finish<=95, or prove another real N<100
strong-arrival certificate. Do not fill these missing inequalities with a
generic finite-policy/semantic equivalence or relabel a paper box-entry bound.

Read S086 failed scalar/amortisation/no-wait controls too. Existing442/443
remain the global certified ceilings. Strong wall B<=95 would give B+4<=99
and fresh clock0 RAW coverage; weak B+5=100 at B95 does NOT satisfy N<100.
The separate complete arbitrary-clock/incoming-history outcome formula, full
FIDE rights/key/current-and-intended-claim/adjudication correspondence and exact
global WDL/DTZ conventions/optimality remain OPEN. Partial geometry/high-clock/
fresh-wall results and47 bundles do not establish material-class closure.

Standalone paper/separate adversarial audit BEFORE Lean. Additive one-main-
theorem modules/all AxiomCheck entries, actual own published-source NEW clean
Gate F then SEPARATE NEW Gate Z. Official native pinned4.35.0/inherited environment;
full logs/commands/exits/times/UTC, source/import/executable hashes, clean identity
and failures retained. No dependency/shim/TLS/checksum change, proof escape,
invented hosted CI success, tablebase/oracle/exhaustive class proof or stored
per-position value certificates. Selected local diagnostics only, explicitly
scoped. Full stable progress table/immediate mathematical delta/full next prompt
and honest closeout; publish/merge/check remote main. Continue toward closure.
'''
write('NEXT_SESSION.md',prompt)
table='| Endgames / target |'+progress.split('| Endgames / target |',1)[1].split('\n\n',1)[0]
close=f'''# S088 — Own-source guarded-box freeze

2026-10-21. Base main3e08ebead15c4fd9980174d9daa319b12f2fcfad, all remote heads
reconciled, S087 exact main/session/remote identity checked. Branch
session/s088-krk-box-freeze. The repeated S087 post-merge structural check passed;
its new output is retained separately rather than replacing historical evidence.

{observed}

EC-T0047 freezes ONLY the exact five public statements and six COMPLETE modules
at own source, including shared Definitions and private pair helper. New immutable
[manifest](../theorems/frozen/EC-T0047/v1.md) and one appended ledger row.
No Lean/module/import/runner/dependency change at this gate; old frozen records
unchanged. Same-agent audits, not external independent review; hosted CI unobserved.

The normalized actual8-ply phase supplies a closed large-box progress/cost step.
Paper <=32 repeated/axis small-box entry is not frozen or mate. Arbitrary entry,
small-box mating finish and integrated global sub100 remain unproved; complete
history outcomes/FIDE/exact WDL-DTZ also remain. KRK NOT CLOSED; no KQK executed.

This closeout/evidence are committed/pushed and ordinarily merged to main; final
local/main/session/remote refs checked after publication. Checks are packaging/
preservation evidence and do not add mathematical scope.

## Required progress table

{table}

{delta}

## Full installed next-session prompt

```text
{prompt}```
'''
write('sessions/S088_KRK_GUARDED_BOX_FREEZE.md',close)
write('sessions/evidence/S088/README.md','# S088 own-source Gate Z\n\n'+observed+'\n\nFull evidence under theorems/frozen/VERIFICATION-S088. No new mathematical scope beyond S087.\n')
print(observed)
