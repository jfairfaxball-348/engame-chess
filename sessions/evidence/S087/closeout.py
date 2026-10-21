"""Record observed own-source Gate F, with no ledger/freeze promotion."""
import json
from pathlib import Path
r=Path(__file__).resolve().parents[3]
e=r/'sessions/evidence/S087/gate-f'
s=json.loads((e/'summary.json').read_text(encoding='utf-8'))
assert s['build_exit']==s['axiom_statement_exit']==0
assert s['total_axiom_reports']==395 and len(s['complete_modules'])==6
assert s['proof_source']=='84161c2650b902e98f37252532a706ec50f40ed4'

def read(p):return (r/p).read_text(encoding='utf-8')
def write(p,t):
    (r/p).parent.mkdir(parents=True,exist_ok=True)
    (r/p).write_text(t,encoding='utf-8',newline='\n')

observed=f"Own published source `{s['proof_source']}`; NEW GitHub clone `{s['fresh_clone']}`, .lake absent before full{s['build_jobs']}-job build exit0 in{s['build_seconds']}s. Complete395-report runner exit0 at{s['verified_utc']}, full working/clean runner and published source bytes match; standard-three axioms only. Gate Z pending; hosted CI unobserved."
candidate=read('research/CANDIDATES.md').replace('LOCAL_VERIFIED paper; incremental Lean passed, fresh Gate F pending (S087)', 'FORMAL_VERIFIED (S087); separate Gate Z pending')
write('research/CANDIDATES.md',candidate)
for p in ['proofs/EC-C051_KRK_GUARDED_BOX_PHASE.md','audits/EC-C051_KRK_GUARDED_BOX_LEAN.md']:
    write(p,read(p)+'\n\nS087 observed Gate F addendum: '+observed+'\n')
write('proofs/EC-C050_KRK_GLOBAL_GEOMETRY_ATTACK.md',read('proofs/EC-C050_KRK_GLOBAL_GEOMETRY_ATTACK.md')+'''

## S087 substantive phase advance

[EC-C051](EC-C051_KRK_GUARDED_BOX_PHASE.md) supplies an actual guarded NE
width5/6 phase within8 plies with all weak replies, paid crossing escort and
closed endpoint cost inequalities; own-source Gate F passed. A fixed16-ply
kernel cycle shows why blindly extending that phase to width4 fails. The paper
repeated/reflected <=32-ply corollary ends at a small guarded box and is NOT
a newly formalised result or a mate bound. Arbitrary guarded entry, small-box
mating finish and an integrated global sub100 budget remain unproved.
Thus the principal EC-C050 claim remains PROPOSED/open; this is partial direct
geometry progress, not full outcome/FIDE/distance closure.
''')
progress=read('docs/SESSION_PROGRESS.md').replace('through S086.','through S087.')
progress=progress.replace('high-clock criteria and clock0 73-ply wall family frozen |','high-clock criteria and clock0 73-ply wall family frozen; normalized guarded large-box phase formally verified, awaiting freeze |')
start=progress.index('Session change:');end=progress.index('\n\n',start)
delta='Session change: S087 proves and formally verifies normalized guarded large-box contraction within8 plies, both cost inequalities and a fixed16-ply width4 failed-policy cycle. Arbitrary guarded entry/small-box mate and global sub100 remain open; the32-ply repeated/axis corollary is paper only.46 frozen bundles unchanged; KRK NOT CLOSED.'
progress=progress[:start]+delta+progress[end:]
write('docs/SESSION_PROGRESS.md',progress)
road=read('docs/KRK_COMPLETION.md')
note='''## S087 direct geometry advance — KRK NOT CLOSED

EC-C051 has passed its own-source Gate F; separate Gate Z is pending. The actual
normalized guarded NE phase contracts widths5/6 within at most8 plies, including
all crossing replies and two paid escort pairs. Both endpoint costs decrease
8*large-side-excess. A fixed16-ply kernel cycle refutes its naive width4 extension.
Five main declarations/six complete modules; older frozen sources unchanged.

The repeated/reflected/axis <=32-ply result reaches a guarded <=4x4 box on PAPER
only; it is neither a newly formalised theorem nor a mate bound. Entry from
arbitrary KRK, an actual small-box mating finish and their combined global budget
remain unproved. This phase fills one explicit EC-C050 geometric step; it does
not close the global95/sub100 claim, all-history outcomes, full FIDE or exact
global WDL/DTZ. No class completion follows from theorem counts.

'''
road=road.replace('## Live closure audit after S086',note+'## Live closure audit after S086',1)
write('docs/KRK_COMPLETION.md',road)
prompt='''# NEXT SESSION — S088: Own-source guarded-box Gate Z, then return to geometry

Owner2026-10-21: continue consecutive sessions until KRK closure; no inferred
pause/new approval gate; stop before KQK. Fetch ALL heads/reconcile unmerged
work/latest main; commit/push branch, ordinary main merge/push and exact remote
main/session identity comparison. Do not edit frozen sources/records.

EC-C051 FORMAL_VERIFIED at OWN published proof source
84161c2650b902e98f37252532a706ec50f40ed4. S087 fresh Gate F passed214 jobs,
complete395 permitted axiom/type reports, five main declarations and six complete
KRKBox modules/private helpers/Definitions. Read full paper and separate paper/
Lean audits, own Gate F inventories/full runner, and the selected six local
phase trees plus16-ply counterexample.46 bundles frozen; KRK NOT CLOSED.

Run a SEPARATE NEW exact-source GitHub clone with .lake absent before full build,
official pinned native Windows Lean4.35.0/inherited environment. Recheck ALL own
source and transitive inventories, five exact main types and COMPLETE395-report
runner against own Gate F. Retain full logs/commands/exits/times/UTC, source/
import/executable hashes and clean identities/failures. No dependency/shim/TLS/
checksum changes, incremental substitute, editing source or invented hosted CI.
Only observed Gate Z permits new immutable EC-T0047 manifest and ONE ledger row.

Exact formal scope: normalized NE guarded box with widths5/6, every actual weak
reply, <=8-ply contraction and both endpoint cost inequalities; kernel16-ply
width4 escort cycle. Both colours/arbitrary flags, ordinary chosen strong moves.
The paper <=32 repeated/reflected/axis small-box-entry corollary is NOT in the
new formal declarations. Do not freeze it as a mate or global sub100 result.

After freezing/publishing S088, continue directly to S089 geometric work under
the persistent owner instruction. Principal EC-C050 remains PROPOSED/open. Need
an actual safe <=4x4 guarded-box mating finish AND costed arbitrary guarded-box
entry, or another genuine global sub100 strong-arrival strategy. The large-box
phase does not solve these. Blind width4 contraction cycles; blindly shrinking
one-square boxes stalemates. Specify a genuine all-defence geometric phase,
rook protection/nonempty replies, legal progress and numeric potential, with
paper/separate audit BEFORE Lean. No unrelated strategy-bookkeeping detour.

Existing442/443 are the global certified ceilings;95 remains only a sufficient
wall target. Strong B+4<=99 would enter the fresh clock0 lift; weak B+5=100
at B95 does NOT satisfy N<100. Complete arbitrary-clock/incoming-history outcomes,
FIDE rights/key/current-and-intended-claim/adjudication and exact global WDL/DTZ
remain additional closure obligations. No tablebase/oracle/exhaustive class proof
or stored position-value certificates. Selected local diagnostics only, scoped.

Full stable progress table/immediate mathematical delta/full next prompt and
honest session closeout; publish/merge and compare actual remote main. KQK stays
unexecuted. Keep working toward KRK closure; do not infer closure from a freeze.
'''
write('NEXT_SESSION.md',prompt)
table='| Endgames / target |'+progress.split('| Endgames / target |',1)[1].split('\n\n',1)[0]
close=f'''# S087 — Guarded large-box contraction, with the small-box limit exposed

2026-10-21. Base main a58d6be5bb3109385c5bba2e4a743f0c164958a0; fetched all
heads, none unmerged, clean main. Branch session/s087-krk-guarded-box. Owner's
continue-until-closure direction persists. No KQK, tablebase/engine oracle,
exhaustive class proof, stored per-position values, dependency or frozen edit.

## Mathematical result and limits

[Paper](../proofs/EC-C051_KRK_GUARDED_BOX_PHASE.md),
[separate same-agent paper audit](../audits/EC-C051_KRK_GUARDED_BOX_PAPER.md),
[Lean fidelity audit](../audits/EC-C051_KRK_GUARDED_BOX_LEAN.md).
This is a new explicit EC-C050 phase, not generic bookkeeping: normalize a
protected NE box of width5/6, pay king support then rook shift, retain BOTH
right/crossing reply branches, and pay two escort pairs in the crossing branch.
All weak replies preserve material; actual horizontal witnesses rule out
stalemate at every weak node. At most8 plies; both endpoint widths reduce the
large-side-excess potential enough to pay that cap. Both colours/all flags.

Six complete modules/five main declarations, no prior frozen source change.
The naive width4 extension has a proved16-ply exact full kernel Position cycle.
The <=32 repeated/reflected/axis small-box-entry corollary is paper only and
ends at a box, NOT mate. Arbitrary entry, small-box mate, global sub100 and all
history/FIDE/exact distance obligations remain open. EC-C050 NOT CLOSED/rejected.

## Observed checks and provenance

{observed}

[Full clean evidence](evidence/S087/gate-f/summary.json),
[recorded working commands](evidence/S087/working-commands.jsonl),
[selected local phase diagnostic](evidence/S087/guarded-box.json).
Six fixed local roots, every weak branch for <=8 plies:57 weak nodes,261 weak
edges,73 right and137 left leaves; additional16-ply cycle. Direct independently
written ordinary-edge replay passed every generated weak edge/prescribed strong
edge. These are diagnostics only, not a universal/class proof or initial history.
Full first authoring command outputs remain in the tool transcript; the working
and fresh runs retain full machine logs, source hashes/timings. Source/type audit
is same-agent, not independent external review. No hosted CI success observed.

Ledger effect: NONE;46 bundles frozen. Gate Z is the next exact-source obligation.
Source84161c2 was pushed before clean verification. Session closeout/evidence
are committed/pushed and ordinarily merged to main; final refs checked after merge.

## Required progress table

{table}

{delta}

## Full installed next-session prompt

```text
{prompt}```
'''
write('sessions/S087_KRK_GUARDED_BOX.md',close)
write('sessions/evidence/S087/README.md','# S087 observed Gate F\n\n'+observed+'\n\nSee gate-f for complete build, runner, source/import/executable hashes, commands and clean identities. Selected local diagnostics do not certify class outcomes.\n')
print(observed)
