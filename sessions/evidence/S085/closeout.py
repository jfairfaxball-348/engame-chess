"""Immutable C049 freeze only after observed separate own-source Gate Z."""
import csv,io,json,re
from pathlib import Path
r=Path(__file__).resolve().parents[3];e=r/'theorems/frozen/VERIFICATION-S085'
s=json.loads((e/'summary.json').read_text(encoding='utf-8'))
assert s['gate']=='Z' and s['entire_own_gate_f_inventory_and_complete_runner_match']
assert not (r/'theorems/frozen/EC-T0046').exists()
identity=json.loads((e/'clean-source-identity.json').read_text(encoding='utf-8'));assert identity['status']==identity['tracked_diff']==''
def read(p):return (r/p).read_text(encoding='utf-8')
def write(p,t):
    (r/p).parent.mkdir(parents=True,exist_ok=True);(r/p).write_text(t,encoding='utf-8',newline='\n')
def append(p,t):write(p,read(p)+'\n'+t+'\n')
old=read('theorems/LEDGER.csv');assert len(list(csv.DictReader(io.StringIO(old))))==45
sha=s['proof_source']
observed=f"OWN source `{sha}`; ONE NEW GitHub clone `{s['fresh_clone']}`, .lake absent before full{s['build_jobs']}-job build exit0 in{s['build_seconds']}s; COMPLETE{s['total_axiom_reports']}-report runner exit0 at{s['verified_utc']}. ENTIRE own Gate F source/transitive inventories and full decoded runner match. Official native Windows Lean4.35.0/inherited environment; source/import/executable hashes, clean identity, commands/exits/times/UTC retained. No source/dependency/shim/TLS/checksum changes or incremental substitute; hosted CI unobserved."
scope='''Exact actual initial-rooted admitted RAW histories, every incoming trace/count,
both material colours/all actual flags. Normalized key equality preserves boards.
Any earlier exact same-colour KRK occurrence propagates through typed admitted
Region. A NONDEAD clock0 endpoint cannot have an earlier KRK prefix: parent
ongoing yields KRK, then quiet step forces positive clock or rook capture gives
dead KK. Hence EVERY KRK query has full-history count<=1. Nondeadness is explicit;
no arbitrary earlier history is truncated or presumed free of larger-material
repetitions. Private absent_count and all helpers/Definitions included in full.

New KRK-restricted lower-winning-rank histogram replaces the stronger all-material
premise ONLY in the new lifting theorem. Actual descending append and key-rank
equality preserve it. Child material follows CLOCK-FREE forcing/nondeadness,
never a circular RAW certificate. Every weak legal executed/intended reply and
correct claim remains, original full history/ranks/keys counted in original frame.

For ANY admitted exact KRK root of clock0, supplied clock-free MateWithin N with
N<100 gives SAME-N RAW W and independent ActualWin with NO supplied incoming
count/histogram. This does not assert arbitrary geometry has a sub100 certificate.
Concrete strong-turn framed rank-six wall supplies the proved73 budget, so
geometry and clock0 alone give W73/ActualWin, both colours/all actual flags.
No compatible full-history witness is inferred from a local board/count vector.

Partial RAW family and nonoptimal73 upper bound, NOT all low-clock histories,
full FIDE key/rights/claim/adjudication correspondence or exact global DTM/WDL/DTZ.
FIDE2023 legal-move kernel/chosen RAW classifier and claims are the normative
scope; core Lean/standard-three axioms trusted. No novelty/tablebase/engine oracle,
exhaustive class proof or stored per-position certificates. Older frozen source
and records unchanged; no material-class completion inferred.
'''
manifest=f'''# EC-T0046 v1 — Clock-zero KRK history control and actual73 wall wins

FROZEN (S085,2026-10-21), candidate EC-C049.
Representative EndgameChess.Rules.KRKFresh.clock_zero_axis_wall.
Full OWN verified proof-source `{sha}`.

## Exact scope and trust

{scope}
## Paper, audits and observed own-source Gate Z

[Paper](../../../proofs/EC-C049_KRK_FRESH_HISTORY.md),
[separate paper audit](../../../audits/EC-C049_KRK_FRESH_HISTORY_PAPER.md),
[Lean fidelity audit](../../../audits/EC-C049_KRK_FRESH_HISTORY_LEAN.md).
Paper/separate same-agent audit preceded new Lean; not independent external review.
All8 main types/9 complete modules/private helpers/shared Definitions/imports
reviewed. Initial authoring errors/repairs retained in S084 working evidence.
Every main declaration standard-three only, no proof escape or source edits here.

{observed}

[Summary](../VERIFICATION-S085/summary.json),
[commands/exits/times/UTC](../VERIFICATION-S085/commands.json),
[build](../VERIFICATION-S085/lake-build.log),
[complete runner](../VERIFICATION-S085/axioms-statements.log),
[source](../VERIFICATION-S085/source-sha256.txt),
[imports](../VERIFICATION-S085/dependency-sha256.txt),
[clean identity](../VERIFICATION-S085/clean-source-identity.json).

## Complete newly frozen source boundary

All9 COMPLETE modules/private helpers/shared Definitions frozen at the source SHA.
Future strengthening/correction uses new module/ID; no silent source edit.

```text
'''
manifest+='\n'.join(line for line in read('theorems/frozen/VERIFICATION-S085/source-sha256.txt').splitlines() if line.split('  ',1)[1] in s['complete_modules'])+'\n```\n\n## Full transitive project source closure\n\n```text\n'+read('theorems/frozen/VERIFICATION-S085/dependency-sha256.txt')+'```\n\n## Verbatim observed public types\n\n```text\n'
log=read('theorems/frozen/VERIFICATION-S085/axioms-statements.log')
for name in s['bundle_declarations']:manifest+=re.search(r'^@?'+re.escape(name)+r' :.*?(?=^\S|\Z)',log,re.M|re.S)[0].rstrip()+'\n\n'
manifest+='```\n';write('theorems/frozen/EC-T0046/v1.md',manifest)
row=['EC-T0046','Clock-zero KRK history control and actual73 wall wins','theorems/frozen/EC-T0046/v1.md','proofs/EC-C049_KRK_FRESH_HISTORY.md','formal/EndgameChess/Rules/KRKFresh/Wall.lean','EndgameChess.Rules.KRKFresh.clock_zero_axis_wall','leanprover/lean4:v4.35.0',sha,s['verified_utc'],'FIDE Laws of Chess 2023 legal-move kernel; actual RAW clock-zero history scope','theorems/frozen/EC-T0046/v1.md','FROZEN','From EC-C049. Separate own-source Gate Z;9 complete modules/8 public types. Full KRK counts<=1 at nondead clock0; supplied N<100 same-budget RAW/ActualWin and concrete73 wall family, no incoming premises. Full geometry/FIDE/global WDL-DTZ open.']
buf=io.StringIO(newline='');csv.writer(buf,lineterminator='\n').writerow(row);write('theorems/LEDGER.csv',old+buf.getvalue())
delta='S085 froze clock-zero KRK count control, incoming-premise-free supplied-budget lift and concrete73 framed-wall actual wins as EC-T0046;46 bundles. Mathematical coverage unchanged from S084; complete low-clock/history outcomes, full FIDE and global exact WDL-DTZ remain open.'
progress=read('docs/SESSION_PROGRESS.md').replace('through S084','through S085').replace('Forty-five','Forty-six')
progress=re.sub(r'^\| K\+R vs K \|.*$', '| K+R vs K | Dead/live and clock-free forcing; RAW termination, holding/winning policies, strong nonloss, high-clock criteria and clock0 73-ply wall family frozen | Complete low-clock/history outcomes, full FIDE correspondence and global exact WDL/DTZ |',progress,flags=re.M)
progress=re.sub(r'Session change: [^\n]+','Session change: '+delta,progress);write('docs/SESSION_PROGRESS.md',progress)
table='| Endgames / target |'+progress.split('| Endgames / target |',1)[1].split('\n\n',1)[0]
prompt='''# NEXT SESSION — S086: Direct global KRK geometric budget attack

Owner2026-10-21: keep going until KRK closes; stop before KQK. Fetch ALL heads,
reconcile unmerged work/latest main; commit/push branch, ordinary merge/push
main and compare exact identities.46 frozen bundles after EC-T0046. Preserve
all older frozen modules/records and ledger rows; candidate EC-C050 only PROPOSED
until a new complete paper proof and separate adversarial audit close.

Principal direct claim: a real all-defence global wall budget B<=95 (or another
proved sub100 strong-arrival strategy), exposing every setup/tempo/pursuit/
rank-advance/rook-safety/stalemate branch. Existing actual setup costs B+4;
B<=95 would give strong arrivals<=99 and the new clock0 history theorem would
give all-strong clock0 RAW actual wins without incoming assumptions. This is a
sufficient route, not a necessary condition for KRK closure. Do not assume95 or
a classical16-move maximum. Weak B+5=100 does NOT meet strict<100 lift at B95.

Read exact C040/C043/C044 quantitative papers/modules, KRKFresh supplied-budget
lift and frozen failed-policy controls. Attack actual geometry rather than
another generic rule/strategy-equivalence lemma. Try improved global accounting
of existing phases and, if insufficient, genuine box/confinement strategy with
explicit protected-rook/legal-choice/nonstalemate progress. A recombination of
73*(7-r) cannot simply be relabelled95. A global file-progress potential needs
actual post-rank-transition file relations, not an assumed no-reset credit.

Paper/attempt plus separate adversarial audit BEFORE any Lean. Retain precise
failed inequalities and missing geometric successor statement if not closed.
Local disclosed ray-model trajectory diagnostics may falsify a proposed policy,
but never certify class outcomes or prove the optimal budget95 false. Any
trajectory after a draw threshold is CLOCK-FREE only, not an admitted RAW play;
no compatible full initial history follows from a local board. No tablebases,
engine oracle, exhaustive class proof or stored per-position certificates.

Only a fully closed exact claim goes to new additive Lean/AxiomCheck and actual
new own-source clean Gate F; no fabricated theorem, axiom or status promotion.
If blocked, record the honest frontier and specific next proof obligation,
including complete arbitrary-clock/history geometry, full FIDE rights/key/claim/
adjudication and optimal global WDL/DTZ still required. Termination, policies,
partial families and an upper bound alone are not KRK closure. Update candidate/
roadmap/completion/README/progress/session ledger and full closeout with stable
table/immediate mathematical delta/full next prompt. Every authorised session
ends committed/pushed/merged on main with verified identities. Owner's continue
instruction persists; no KQK or unrelated detour. Do not label an unproved route
complete or pause the owner's campaign by inference.
'''
write('NEXT_SESSION.md',prompt)
write('research/CANDIDATES.md',read('research/CANDIDATES.md').replace('FORMAL_VERIFIED (S084); separate Gate Z pending','FROZEN as EC-T0046 (S085)'))
for p in ['README.md','docs/ROADMAP.md','docs/KRK_COMPLETION.md']:
    text=read(p)
    if p=='README.md':text=text.replace('**After S083.** Forty-five frozen theorem bundles (not forty-five solved material classes).','**After S085.** Forty-six frozen theorem bundles (not forty-six solved material classes).')
    if p=='docs/KRK_COMPLETION.md':text=text.replace('45 frozen bundles after S083','46 frozen bundles after S085')
    write(p,text+'\n'+delta+' [EC-T0046]('+('../' if p.startswith('docs/') else '')+'theorems/frozen/EC-T0046/v1.md).\n')
append('theorems/README.md','- [EC-T0046](frozen/EC-T0046/v1.md): actual clock0 KRK incoming counts<=1, supplied N<100 same-budget RAW/ActualWin with no incoming premises, concrete73 framed-wall family. [Separate own-source Gate Z](frozen/VERIFICATION-S085/README.md).')
write('theorems/frozen/VERIFICATION-S085/README.md','# S085 — observed own-source Gate Z\n\n'+observed+'\n\nAll8 exact types/9 complete modules/scope/trust/full source closure in [EC-T0046](../EC-T0046/v1.md). Logs/hashes/identity retained. Same-agent audits; no class/FIDE/global distance closure.\n')
write('sessions/evidence/S085/README.md','# S085 — clock0 history/fresh73 freeze\n\n'+observed+'\n\nBase mainbd1c6812429848551829a39ed11de099f0a5d008, all heads fetched/no unmerged work. All exact sources/types/papers/audits/imports reread; no Lean edits. Older deprecation warnings retained. Packaging/preservation checks in checks.log.\n')
write('sessions/S085_FREEZE_KRK_FRESH_HISTORY.md',f'''# S085 — Freeze actual clock-zero KRK history and fresh73 wall wins

2026-10-21, base mainbd1c6812429848551829a39ed11de099f0a5d008, all heads
fetched/no unmerged work; branch session/s085-freeze-krk-fresh-history.
EC-C049 frozen as EC-T0046. {observed}
[Manifest](../theorems/frozen/EC-T0046/v1.md),
[evidence](../theorems/frozen/VERIFICATION-S085/README.md).

{scope}
Paper/separate same-agent audits/all complete source/types/imports reviewed;
not independent external review. Prior45 rows/records/source preserved; exactly
one new row. No Lean edits/incremental substitute. Relevant packaging checks
in evidence/S085/checks.log. Publication recorded by Git branch commit/push,
ordinary main merge/push and exact remote identity comparison. S086 returns
to the missing real global geometric budget; no generic detour or class claim.

{table}

Session change: {delta}

## Full installed next prompt

{prompt}''')
append('sessions/SESSION_LEDGER.md','| S085 | 2026-10-21 | Freeze clock0 KRK history/fresh73 wins (Gate Z) | New own-source208-job build/390 permitted reports, complete own source/import/runner equality. [Closeout](S085_FREEZE_KRK_FRESH_HISTORY.md); direct global geometry next | **+1 -> EC-T0046 FROZEN** (46 bundles); mathematical coverage unchanged |')
print(observed)
