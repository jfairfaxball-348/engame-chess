"""Freeze C047 only after observed own-source Gate Z; never overwrite record."""
import csv,io,json,re
from pathlib import Path
r=Path(__file__).resolve().parents[3];e=r/'theorems/frozen/VERIFICATION-S081'
s=json.loads((e/'summary.json').read_text(encoding='utf-8'))
assert s['gate']=='Z' and s['entire_own_gate_f_inventory_and_complete_runner_match']
assert not (r/'theorems/frozen/EC-T0044').exists()
identity=json.loads((e/'clean-source-identity.json').read_text(encoding='utf-8'));assert identity['status']==identity['tracked_diff']==''
def read(p):return (r/p).read_text(encoding='utf-8')
def write(p,t):
    (r/p).parent.mkdir(parents=True,exist_ok=True);(r/p).write_text(t,encoding='utf-8',newline='\n')
def append(p,t):write(p,read(p)+'\n'+t+'\n')
old=read('theorems/LEDGER.csv');assert len(list(csv.DictReader(io.StringIO(old))))==43
sha=s['proof_source']
observed=f"OWN source `{sha}`; ONE NEW GitHub clone `{s['fresh_clone']}`, .lake absent before full{s['build_jobs']}-job build exit0 in{s['build_seconds']}s; COMPLETE{s['total_axiom_reports']}-report runner exit0 at{s['verified_utc']}. ENTIRE own Gate F source/transitive inventories and decoded complete runner match. Official native Windows Lean4.35.0, inherited environment; no source/dependency/shim/TLS/checksum changes or incremental substitute. Hosted CI unobserved."
scope='''For either strong material colour, EVERY admitted exact KRK root has an
actual globally legal strong holding policy, and weak RuleForceMate is
impossible. Both turns/all actual flags/full incoming trace/clock/counts. Root
king safety follows actual initial-rooted last Legal move, not an assumed
arbitrary-board king-separation invariant. KRK-or-dead is preserved by all
actual moves including castling and dead KK rook capture; it excludes weak
Goal at every policy prefix.

On ONGOING weak-turn roots with h>=99: strong nonforcing AND an actual weak
holding policy. Under a hypothetical strong certificate its retained child
cannot be dead capture and is quiet, yielding a correct intended clock claim
at the PARENT before executing it. No unconditional quiet witness is assumed.
On ONGOING strong-turn roots with h>=98: strong forcing IFF an actual admitted
one-move child is named mate. Exactly W(1) iff forcing and NOT W(0), hence optimal
one-board-ply budget on those wins. A strong player may decline its own claim;
mate149->150 retains mate-first status. All incoming repetition counts remain,
terminal draw children are retained and cannot carry winning certificates.

RAW scope only, not complete low-clock arbitrary-history geometric outcomes,
full FIDE correspondence, actual winning-policy bridge or global numeric
DTM/WDL/DTZ parity. Terminal classifier/claim model and legal-move kernel are
the existing normative encodings, not a theorem of the whole FIDE rulebook.
Core Lean and standard-three axioms remain trusted. Classical reproof, no
novelty/tablebase/engine/exhaustive class proof or stored position certificates.
'''
manifest=f'''# EC-T0044 v1 — Strong RAW KRK nonloss and exact high-clock forcing

Status FROZEN (S081,2026-10-21), candidate EC-C047.
Representative EndgameChess.Rules.KRKHighClock.strong_high_clock_iff.
Full OWN verified proof-source `{sha}`.

## Scope, limits and trust

{scope}
## Paper, audits and separate own-source Gate Z

[Paper](../../../proofs/EC-C047_KRK_HIGH_CLOCK.md),
[paper audit](../../../audits/EC-C047_KRK_HIGH_CLOCK_PAPER.md),
[Lean fidelity audit](../../../audits/EC-C047_KRK_HIGH_CLOCK_LEAN.md).
Paper and separate same-agent audit preceded Lean; local one-ply corollary
was included in the pre-Lean audit. Same-agent is not external independent review.
All10 public declarations/11 complete modules inspected, full private helpers
and Definitions included. Original authoring failures retained in S080 evidence.
No Lean edits; prior frozen sources/records preserved. Standard-three only.

{observed}

[Summary](../VERIFICATION-S081/summary.json),
[commands/exits/times/UTC](../VERIFICATION-S081/commands.json),
[build](../VERIFICATION-S081/lake-build.log),
[complete runner](../VERIFICATION-S081/axioms-statements.log),
[source](../VERIFICATION-S081/source-sha256.txt),
[imports](../VERIFICATION-S081/dependency-sha256.txt),
[clean identity](../VERIFICATION-S081/clean-source-identity.json).
Rule edition: FIDE2023 legal-move kernel, RAW history/action scope stated above.

## Complete newly frozen source boundary

All11 COMPLETE modules/private helpers/shared Definitions frozen at the SHA;
future strengthening/correction uses new module/ID, no silent source edits.

```text
'''
manifest+='\n'.join(line for line in read('theorems/frozen/VERIFICATION-S081/source-sha256.txt').splitlines() if line.split('  ',1)[1] in s['complete_modules'])+'\n```\n\n## Full transitive project source closure\n\n```text\n'+read('theorems/frozen/VERIFICATION-S081/dependency-sha256.txt')+'```\n\n## Verbatim observed public statements\n\n```text\n'
log=read('theorems/frozen/VERIFICATION-S081/axioms-statements.log')
for name in s['bundle_declarations']:manifest+=re.search(r'^@?'+re.escape(name)+r' :.*?(?=^\S|\Z)',log,re.M|re.S)[0].rstrip()+'\n\n'
manifest+='```\n';write('theorems/frozen/EC-T0044/v1.md',manifest)
row=['EC-T0044','Strong RAW KRK nonloss and exact high-clock forcing','theorems/frozen/EC-T0044/v1.md','proofs/EC-C047_KRK_HIGH_CLOCK.md','formal/EndgameChess/Rules/KRKHighClock/StrongHighClock.lean','EndgameChess.Rules.KRKHighClock.strong_high_clock_iff','leanprover/lean4:v4.35.0',sha,s['verified_utc'],'FIDE Laws of Chess 2023 legal-move kernel; RAW history scope','theorems/frozen/EC-T0044/v1.md','FROZEN','From EC-C047. Separate own-source Gate Z;11 complete modules/10 public types. Universal strong holding, exact high-clock partial outcomes and optimal1 ply on those wins; full low-clock/FIDE/global WDL-DTZ open.']
buf=io.StringIO(newline='');csv.writer(buf,lineterminator='\n').writerow(row);write('theorems/LEDGER.csv',old+buf.getvalue())
delta='S081 froze universal strong RAW nonloss, exact high-clock forcing criteria and local optimal one-ply budget as EC-T0044;44 bundles. Mathematical coverage unchanged from S080; low-clock geometry, actual winning-policy bridge, full FIDE and global WDL/DTZ remain open.'
progress=read('docs/SESSION_PROGRESS.md').replace('through S080','through S081').replace('Forty-three','Forty-four').replace('strong nonloss/high-clock criteria formally verified','strong nonloss/high-clock criteria frozen')
progress=re.sub(r'Session change: [^\n]+','Session change: '+delta,progress);write('docs/SESSION_PROGRESS.md',progress)
table='| Endgames / target |'+progress.split('| Endgames / target |',1)[1].split('\n\n',1)[0]
prompt='''# NEXT SESSION — S082: Actual winning policies for admitted RAW KRK

Owner2026-10-21: continue consecutive KRK sessions until closure; stop before
KQK. Fetch ALL heads, reconcile unmerged work/latest main, commit/push branch,
ordinary merge/push main and compare exact identities.44 frozen bundles after
EC-T0044. Preserve all earlier frozen source/records; next candidate EC-C048.

Exact direct gap: finite RuleForceMate certificates and actual holding duality
do not yet prove an ACTUAL legal winning policy against every move/claim.
Define independently a total globally legal full-history policy and ALL-prefix
WinningSafety: every terminal endpoint is named Goal, own ongoing choices are
Some actual child (never a selected claim), opponent ongoing prefixes have NO
correct current/intended claim. ActualWin ALSO requires a UNIFORM finite board-
ply bound B on every compliant path, excluding vacuous infinite-policy cycles.
Correct claims stop at0 plies, never pass or append the intended move.

Prove full F certificate action inversion and a globally legal F-preserving
policy. The F-prefix invariant gives safety, not termination by itself. Apply
the existing universal KRK-or-terminal Region fuel to get cap fuel(root), hence
ActualWin. Converse: ANY globally legal WinningSafety policy with horizon B
gives the EXACT old RuleMateWithin(B) by induction on B, uniformly lowering all
child horizons by prefixing one actual compliant edge. Keep every opponent
child/no-claim/nonempty guard; zero horizon ongoing child contradicts bound.
Thus ActualWin iff old full F on every admitted exact KRK root (both named/
material colours/turns/all actual flags/full incoming history/count/clock).
Prove actual maximal endpoints and an actual terminal continuation are named
mate within fuel; the stopped-own-claim branch contradicts WinningSafety.

Do NOT claim a merely F-preserving policy cannot cycle on a generic graph.
The smallest needed dependency is existing all-board KRK fuel; no new generic
detour required. Exit back to low-clock history/geometry and correct distances
after this exact bridge. It does not evaluate low-clock boards or prove full
FIDE/WDL/DTZ; KRK remains open until those and all freeze gates close.

Standalone paper/separate same-agent adversarial audit BEFORE additive Lean.
One main theorem per module, all main types/axioms in complete AxiomCheck.
Gate F: NEW GitHub clone at OWN published exact SHA, .lake absent, full build/
complete matching runner, exact statements/source/import/executable hashes,
clean HEAD/tree/status, logs/commands/exits/times/UTC and retained failures.
Native official pinned4.35.0/inherited environment; no dependencies/shims/TLS/
checksum changes. Separate Gate Z. Relevant ledger/preservation/hash/type/
link/diff checks, full stable table/immediate delta, full next prompt and session
closeout; publish/merge/compare remote main. No tablebase/engine oracle/class
enumeration or stored certificates. Continue direct KRK work until actual
closure under owner authority; stop before KQK.
'''
write('NEXT_SESSION.md',prompt)
write('research/CANDIDATES.md',read('research/CANDIDATES.md').replace('FORMAL_VERIFIED (S080); separate Gate Z pending','FROZEN as EC-T0044 (S081)'))
for p in ['README.md','docs/ROADMAP.md','docs/KRK_COMPLETION.md']:
    text=read(p)
    if p=='README.md':text=text.replace('**After S079.** Forty-three frozen theorem bundles (not forty-three solved material classes).','**After S081.** Forty-four frozen theorem bundles (not forty-four solved material classes).')
    if p=='docs/KRK_COMPLETION.md':text=text.replace('43 frozen bundles after S079','44 frozen bundles after S081')
    write(p,text+'\n'+delta+' [EC-T0044]('+('../' if p.startswith('docs/') else '')+'theorems/frozen/EC-T0044/v1.md).\n')
append('theorems/README.md','- [EC-T0044](frozen/EC-T0044/v1.md): universal actual strong holding and weak nonforcing, exact high-clock RAW forcing criteria, exact one-ply optimal budget on those wins. [Separate own-source S081 Gate Z](frozen/VERIFICATION-S081/README.md).')
write('theorems/frozen/VERIFICATION-S081/README.md','# S081 — observed separate own-source Gate Z\n\n'+observed+'\n\nAll10 exact types/11 complete modules and scope/trust/source closure in [EC-T0044](../EC-T0044/v1.md). Full logs/hashes/clean identity retained. Same-agent audits; no class/FIDE/global distance closure.\n')
write('sessions/evidence/S081/README.md','# S081 — C047 separate own-source freeze\n\n'+observed+'\n\nBase maina5bce9bc7377a28dc786f5977af33601c9ba9207, all heads fetched/no unmerged work. Entire papers/audits/modules/types/imports reread; no Lean edits. Older frozen deprecated-if warnings preserved. Relevant checks in checks.log; they are packaging evidence only.\n')
write('sessions/S081_FREEZE_KRK_HIGH_CLOCK.md',f'''# S081 — Freeze strong RAW nonloss and exact high-clock KRK

2026-10-21. Base maina5bce9bc7377a28dc786f5977af33601c9ba9207, all heads
fetched/no unmerged work; branch session/s081-freeze-krk-high-clock.
EC-C047 frozen as EC-T0044. {observed}
[Manifest](../theorems/frozen/EC-T0044/v1.md),
[evidence](../theorems/frozen/VERIFICATION-S081/README.md).

{scope}
Paper/separate same-agent audits and all sources/types/imports reviewed; not
independent external review. Older43 rows/frozen records/source preserved;
exactly one new row. No Lean edits or incremental verification substitute.
Relevant checks in evidence/S081/checks.log; packaging evidence only.
Publication recorded in Git by branch commit/push, ordinary main merge/push
and exact remote identity comparison. Return directly to S082 actual policy
strategy bridge, then low-clock geometry; stop before KQK.

{table}

Session change: {delta}

## Full installed next prompt

{prompt}''')
append('sessions/SESSION_LEDGER.md','| S081 | 2026-10-21 | Freeze strong nonloss/high-clock RAW KRK (Gate Z) | Own-source new190-job build/374 permitted reports, whole own source/import/runner equality. [Closeout](S081_FREEZE_KRK_HIGH_CLOCK.md); direct actual winning policies next | **+1 -> EC-T0044 FROZEN** (44 bundles); no new mathematical coverage |')
print(observed)
