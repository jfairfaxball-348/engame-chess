"""Immutable C048 freeze after observed separate own-source Gate Z."""
import csv,io,json,re
from pathlib import Path
r=Path(__file__).resolve().parents[3];e=r/'theorems/frozen/VERIFICATION-S083'
s=json.loads((e/'summary.json').read_text(encoding='utf-8'))
assert s['gate']=='Z' and s['entire_own_gate_f_inventory_and_complete_runner_match']
assert not (r/'theorems/frozen/EC-T0045').exists()
identity=json.loads((e/'clean-source-identity.json').read_text(encoding='utf-8'));assert identity['status']==identity['tracked_diff']==''
def read(p):return (r/p).read_text(encoding='utf-8')
def write(p,t):
    (r/p).parent.mkdir(parents=True,exist_ok=True);(r/p).write_text(t,encoding='utf-8',newline='\n')
def append(p,t):write(p,read(p)+'\n'+t+'\n')
old=read('theorems/LEDGER.csv');assert len(list(csv.DictReader(io.StringIO(old))))==44
sha=s['proof_source']
observed=f"OWN source `{sha}`; ONE NEW GitHub clone `{s['fresh_clone']}`, .lake absent before full{s['build_jobs']}-job build exit0 in{s['build_seconds']}s; COMPLETE{s['total_axiom_reports']}-report runner exit0 at{s['verified_utc']}. ENTIRE own Gate F source/transitive inventories and complete decoded runner match. Official native Windows Lean4.35.0/inherited environment, exact executable/source/import hashes and clean identity retained. No Lean/dependency/shim/TLS/checksum changes or incremental substitute; hosted CI unobserved."
scope='''ActualWin is INDEPENDENT actual semantics: a total globally legal full-history
policy, ALL-prefix terminal named mate/own ongoing Some/opponent ongoing NO
correct current-or-intended claim, AND a uniform finite board-ply horizon B.
Correct claims consume0 board plies and end immediately, never pass or append
the announced move. A cap is essential: F-preserving choices can cycle on a
generic graph. Full F certificate action inversion gives a globally legal
F-preserving policy; all-prefix F gives outcome/claim safety; the actual KRK
fuel supplies its horizon. ANY actual bounded winning policy gives exactly the
old W(B) by uniform prefix induction, with no KRK premise in this converse.

On EVERY admitted exact KRK history (or terminal Region), ActualWin iff full F,
either named/material colour, both turns/all actual flags/incoming full trace,
clock/count. All opponent board children and current/intended claims retained.
Every maximal compliant endpoint under WinningSafety is actual named mate;
some genuine terminal named-mate continuation exists within root fuel. No
arbitrary short prefix is called complete. Terminal draw/opposite mate fails
the zero-prefix requirement; named root mate permits bound0. Mate at150 remains
mate-first. Every public helper and shared definition is included in the bundle.

Strategy semantics only, NOT an evaluated low-clock geometric outcome formula,
full FIDE rights/key/claim/adjudication correspondence or exact global DTM/WDL/DTZ.
The existing FIDE2023 legal-move kernel and chosen RAW model are the normative
boundary. Core Lean and standard-three axioms remain trusted. No tablebase,
engine oracle, exhaustive class proof, stored position certificates or novelty
claim. Previous frozen sources/records are unchanged; no class closure inferred.
'''
manifest=f'''# EC-T0045 v1 — Actual bounded RAW KRK winning-policy correspondence

FROZEN (S083,2026-10-21), candidate EC-C048.
Representative EndgameChess.Rules.KRKWinning.actual_win_iff_force.
Full OWN verified proof-source `{sha}`.

## Exact scope and trust

{scope}
## Paper/audits and observed own-source Gate Z

[Paper](../../../proofs/EC-C048_KRK_WINNING_POLICY.md),
[separate paper audit](../../../audits/EC-C048_KRK_WINNING_POLICY_PAPER.md),
[Lean fidelity audit](../../../audits/EC-C048_KRK_WINNING_POLICY_LEAN.md).
Paper/separate same-agent audit preceded Lean; same-agent is not independent
external review. All8 main types/9 complete modules and transitive imports
reviewed; full private helpers/Definitions frozen. Initial authoring failure
and repair retained in S082 evidence. Every declaration standard-three only.

{observed}

[Summary](../VERIFICATION-S083/summary.json),
[commands/exits/times/UTC](../VERIFICATION-S083/commands.json),
[build](../VERIFICATION-S083/lake-build.log),
[complete runner](../VERIFICATION-S083/axioms-statements.log),
[source](../VERIFICATION-S083/source-sha256.txt),
[imports](../VERIFICATION-S083/dependency-sha256.txt),
[clean identity](../VERIFICATION-S083/clean-source-identity.json).

## Complete newly frozen source boundary

All9 complete modules/private helpers/shared Definitions frozen at the SHA.
Future strengthening/correction uses new module/ID, no silent source edit.

```text
'''
manifest+='\n'.join(line for line in read('theorems/frozen/VERIFICATION-S083/source-sha256.txt').splitlines() if line.split('  ',1)[1] in s['complete_modules'])+'\n```\n\n## Full transitive project source closure\n\n```text\n'+read('theorems/frozen/VERIFICATION-S083/dependency-sha256.txt')+'```\n\n## Verbatim observed public types\n\n```text\n'
log=read('theorems/frozen/VERIFICATION-S083/axioms-statements.log')
for name in s['bundle_declarations']:manifest+=re.search(r'^@?'+re.escape(name)+r' :.*?(?=^\S|\Z)',log,re.M|re.S)[0].rstrip()+'\n\n'
manifest+='```\n';write('theorems/frozen/EC-T0045/v1.md',manifest)
row=['EC-T0045','Actual bounded RAW KRK winning-policy correspondence','theorems/frozen/EC-T0045/v1.md','proofs/EC-C048_KRK_WINNING_POLICY.md','formal/EndgameChess/Rules/KRKWinning/Equivalence.lean','EndgameChess.Rules.KRKWinning.actual_win_iff_force','leanprover/lean4:v4.35.0',sha,s['verified_utc'],'FIDE Laws of Chess 2023 legal-move kernel; RAW actual bounded history policy scope','theorems/frozen/EC-T0045/v1.md','FROZEN','From EC-C048. Separate own-source Gate Z;9 complete modules/8 public types. Independent actual strategy iff full F; same-B certificate and actual mate continuation. Geometric low-clock/FIDE/global WDL-DTZ open.']
buf=io.StringIO(newline='');csv.writer(buf,lineterminator='\n').writerow(row);write('theorems/LEDGER.csv',old+buf.getvalue())
delta='S083 froze independent actual bounded RAW winning-policy correspondence, exact B certificate extraction and actual terminal mate continuation as EC-T0045;45 bundles. Mathematical coverage unchanged from S082; low-clock geometry/full FIDE/global exact WDL-DTZ remain open.'
progress=read('docs/SESSION_PROGRESS.md').replace('through S082','through S083').replace('Forty-four','Forty-five').replace('actual winning-policy bridge formally verified','actual winning-policy bridge frozen')
progress=re.sub(r'Session change: [^\n]+','Session change: '+delta,progress);write('docs/SESSION_PROGRESS.md',progress)
table='| Endgames / target |'+progress.split('| Endgames / target |',1)[1].split('\n\n',1)[0]
prompt='''# NEXT SESSION — S084: Clock-zero KRK histories and assumption-free incoming counts

Owner2026-10-21: continue consecutive KRK sessions until closure; stop before
KQK. Fetch ALL remote heads/reconcile unmerged work/latest main; commit/push
branch, ordinary merge/push main and compare identities.45 frozen bundles after
EC-T0045. Preserve every frozen source/record; next candidate EC-C049.

Direct principal payoff: an admitted clock-zero strong-turn framed rank-six KRK
wall has RAW W73 AND ActualWin with NO supplied current-count or incoming
histogram assumptions. Keep both colours/all actual flags/full incoming history
and every weak executed/intended move. The73 bound is nonoptimal; this remains
a partial RAW family, not full low-clock geometry/FIDE/global WDL-DTZ closure.
No compatible-history witness is asserted merely from a board/count vector.

Read C045 all-move closure/admission/fuel, C042 actual rank-history lifting,
C043 framed73 geometry, C048 actual winning-policy bridge and raw key/count
definitions. Paper and separate adversarial audit BEFORE new Lean.

Exact blocked KRK step: old LowerRankHistory quantifies ALL earlier material
and is too strong to follow from clock0. Earlier larger-material repetitions
cannot match future KRK boards. Smallest statement/payoff: normalized key
equality preserves boards, an earlier exact same-colour KRK prefix forces all
later ongoing admitted endpoints into exact KRK (capture dead KK stops), and
clock0/nondead current endpoint excludes ANY earlier KRK prefix. A quiet last
KRK move gives clock>0; a reset capture gives dead child. Thus each KRK query
has full incoming count<=1 at clock0. Do not silently truncate history or assume
an arbitrary independent incoming count vector is compatible.

Define a NEW KRK-restricted lower-winning-rank histogram. Prove preservation
on an actual descending KRK append, retaining original counts. A CLOCK-FREE
winning child from KRK cannot be dead capture, so material survives; do NOT
use a RAW certificate before proving the lift. Adapt the same-budget rank
lifting at exact KRK nodes, including every weak legal intended move. It is
NOT enough to assert the older all-material histogram. Instantiate73 wall at
clock0, derive root/current/restricted counts from the new actual history lemma,
then obtain actual winning policy via the frozen bridge. Exit directly into
this new input family; if blocked record precise missing lemma and leave scope
open, no generic detour or class completion claim.

Additive one-main-theorem modules and complete AxiomCheck; no frozen edits.
Gate F is NEW own published exact-source GitHub clone without .lake, full build
and complete matching runner, exact statements/source/import/executable hashes,
clean identity, commands/exits/times/UTC and retained failures. Native official
4.35.0/inherited environment, no dependencies/shims/TLS/checksum changes. Gate Z
separate. Relevant checks/current statuses/full table/immediate delta/full next
prompt/session closeout; publish/merge/compare main. No tablebase/engine oracle,
class enumeration or stored per-position certificates. Continue direct KRK
work under owner authority; stop before KQK.
'''
write('NEXT_SESSION.md',prompt)
write('research/CANDIDATES.md',read('research/CANDIDATES.md').replace('FORMAL_VERIFIED (S082); separate Gate Z pending','FROZEN as EC-T0045 (S083)'))
for p in ['README.md','docs/ROADMAP.md','docs/KRK_COMPLETION.md']:
    text=read(p)
    if p=='README.md':text=text.replace('**After S081.** Forty-four frozen theorem bundles (not forty-four solved material classes).','**After S083.** Forty-five frozen theorem bundles (not forty-five solved material classes).')
    if p=='docs/KRK_COMPLETION.md':text=text.replace('44 frozen bundles after S081','45 frozen bundles after S083')
    write(p,text+'\n'+delta+' [EC-T0045]('+('../' if p.startswith('docs/') else '')+'theorems/frozen/EC-T0045/v1.md).\n')
append('theorems/README.md','- [EC-T0045](frozen/EC-T0045/v1.md): independent actual bounded RAW KRK winning policy iff full F, same-B certificate extraction and actual terminal mate continuation. [Separate own-source Gate Z](frozen/VERIFICATION-S083/README.md).')
write('theorems/frozen/VERIFICATION-S083/README.md','# S083 — observed own-source Gate Z\n\n'+observed+'\n\nAll8 exact types/9 complete modules and scope/trust/full closure in [EC-T0045](../EC-T0045/v1.md). Full logs/hashes/identity retained. Same-agent audits, no class/FIDE/global distance closure.\n')
write('sessions/evidence/S083/README.md','# S083 — actual winning-policy freeze\n\n'+observed+'\n\nBase mainb0bf372ec0c2350333e6d472822ed3f196465a8f; all heads fetched/no unmerged work. All exact sources/types/papers/audits/imports reread; no Lean edits. Prior frozen deprecation warnings retained. Packaging/preservation checks in checks.log.\n')
write('sessions/S083_FREEZE_KRK_WINNING_POLICY.md',f'''# S083 — Freeze independent actual RAW KRK winning policies

2026-10-21, base mainb0bf372ec0c2350333e6d472822ed3f196465a8f; all heads
fetched/no unmerged work; branch session/s083-freeze-krk-winning-policy.
EC-C048 frozen as EC-T0045. {observed}
[Manifest](../theorems/frozen/EC-T0045/v1.md),
[evidence](../theorems/frozen/VERIFICATION-S083/README.md).

{scope}
Paper and separate same-agent audits/complete source/types/imports reviewed;
not independent external review. Prior44 rows/frozen records/source preserved;
exactly one new row. No Lean edits/incremental substitute. Relevant packaging
checks in evidence/S083/checks.log. Publication recorded by Git branch commit/
push, ordinary main merge/push and exact remote identity comparison. Return
directly to clock0 KRK history control and new73 family in S084; no class claim.

{table}

Session change: {delta}

## Full installed next prompt

{prompt}''')
append('sessions/SESSION_LEDGER.md','| S083 | 2026-10-21 | Freeze actual RAW KRK winning policies (Gate Z) | New own-source199-job build/382 permitted reports, complete own source/import/runner equality. [Closeout](S083_FREEZE_KRK_WINNING_POLICY.md); direct clock0 history gap next | **+1 -> EC-T0045 FROZEN** (45 bundles); no new geometric coverage |')
print(observed)
