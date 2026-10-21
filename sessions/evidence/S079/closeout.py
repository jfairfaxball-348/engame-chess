"""Create immutable EC-T0043 only after observed separate own-source Gate Z."""
import csv,io,json,re
from pathlib import Path
r=Path(__file__).resolve().parents[3];e=r/'theorems/frozen/VERIFICATION-S079'
s=json.loads((e/'summary.json').read_text(encoding='utf-8'))
assert s['gate']=='Z' and s['entire_own_gate_f_inventory_and_complete_runner_match']
assert not (r/'theorems/frozen/EC-T0043').exists(), 'Never rewrite a frozen record'
identity=json.loads((e/'clean-source-identity.json').read_text(encoding='utf-8'))
assert identity['status']==identity['tracked_diff']==''
def read(p):return (r/p).read_text(encoding='utf-8')
def write(p,t):
    (r/p).parent.mkdir(parents=True,exist_ok=True);(r/p).write_text(t,encoding='utf-8',newline='\n')
def append(p,t):write(p,read(p)+'\n'+t+'\n')
sha=s['proof_source']
observed=f"OWN source `{sha}`; ONE NEW GitHub clone `{s['fresh_clone']}`, formal/.lake absent before full{s['build_jobs']}-job build exit0 in{s['build_seconds']}s; COMPLETE{s['total_axiom_reports']}-report AxiomCheck exit0 at{s['verified_utc']}. ENTIRE own Gate F source/transitive inventories and complete decoded runner match. Official native Windows Lean4.35.0; inherited environment. No source/dependency/shim/TLS/checksum changes or incremental substitute; hosted CI unobserved."
manifest=f'''# EC-T0043 v1 — Actual all-history admitted RAW KRK holding policies

Status FROZEN (S079,2026-10-21), candidate EC-C046.
Representative EndgameChess.Rules.KRKHolding.holding_iff_not_force.
Full OWN verified proof-source `{sha}`.

## Exact scope and trust

For either material colour sigma and holder colour c, every existing admitted
RAW exact KRK history (and terminal Region endpoints) has an actual globally
legal holding policy iff the opponent has NO full RuleForceMate certificate.
Holding is defined independently by a total policy on FULL admitted histories
and avoidance of opponent mate at EVERY compliant prefix, including zero.
None is a correct present/intended claim on an ongoing own-turn, consuming0
board plies, never a pass. Some is an actual admitted child. Every opponent
board reply is retained; opponent claims can draw sooner. No low-clock, count,
histogram, safety, noRights or chosen-strategy restriction. Both turns/all
actual flags, every complete incoming history. Fuel saturation proves the
uniform child budgets used for defensive choice; converse applies to ANY
holding policy and EVERY finite opponent winning certificate.

Every compliant path projects to an actual typed path with endpoint Region
and fuel(end)+length<=fuel(root). Maximal compliant endpoints are raw terminal
OR an ongoing own-turn selected correct claim; some stopped continuation exists
within fuel(root). Terminal fuel0 does not imply draw, and mate at150 remains
mate-first. Arbitrary truncated prefixes need not be stopped.

RAW strategy duality only: NOT a geometric evaluation of the full forcing
predicate, complete FIDE correspondence, numeric optimal distance or WDL/DTZ
parity. No class closure. Classical bounded-game reasoning, no novelty claim,
tablebase, engine, exhaustive class proof or stored per-position certificates.
Rule edition/trust: existing FIDE2023 legal-move kernel with chosen RAW
classifier/thresholds, core Lean and standard axioms. Normative full FIDE
history/rights/key/claim/adjudication correspondence remains open.

## Paper, separate same-agent audits and observed evidence

[Paper](../../../proofs/EC-C046_KRK_HOLDING.md),
[paper audit](../../../audits/EC-C046_KRK_HOLDING_PAPER.md),
[Lean fidelity audit](../../../audits/EC-C046_KRK_HOLDING_LEAN.md).
Paper/audit preceded Lean; same-agent review is not independent external review.
Authoring failures and original repairs remain in sessions/evidence/S078/.
All10 public types and11 complete modules inspected, including all private
helpers/shared Definitions and actual frozen dependencies. Standard-three
axioms only, no proof escape. Older frozen source and records unchanged.

Separate own-source Gate Z: {observed}

[Summary](../VERIFICATION-S079/summary.json),
[commands/exits/times/UTC](../VERIFICATION-S079/commands.json),
[build](../VERIFICATION-S079/lake-build.log),
[complete runner](../VERIFICATION-S079/axioms-statements.log),
[source inventory](../VERIFICATION-S079/source-sha256.txt),
[imports](../VERIFICATION-S079/dependency-sha256.txt),
[clean identity](../VERIFICATION-S079/clean-source-identity.json).

## Complete newly frozen module boundary

All11 complete modules below, ALL helpers and shared definitions, frozen in full
at the source SHA. Future strengthening/correction uses new modules/ID.

```text
'''
manifest+='\n'.join(line for line in read('theorems/frozen/VERIFICATION-S079/source-sha256.txt').splitlines() if line.split('  ',1)[1] in s['complete_modules'])+'\n```\n\n## Full transitive project closure\n\n```text\n'+read('theorems/frozen/VERIFICATION-S079/dependency-sha256.txt')+'```\n\n## Verbatim observed public types\n\n```text\n'
log=read('theorems/frozen/VERIFICATION-S079/axioms-statements.log')
for name in s['bundle_declarations']:
    manifest+=re.search(r'^@?'+re.escape(name)+r' :.*?(?=^\S|\Z)',log,re.M|re.S)[0].rstrip()+'\n\n'
manifest+='```\n';write('theorems/frozen/EC-T0043/v1.md',manifest)
old=read('theorems/LEDGER.csv');assert len(list(csv.DictReader(io.StringIO(old))))==42
row=['EC-T0043','Actual all-history admitted RAW KRK holding policies','theorems/frozen/EC-T0043/v1.md','proofs/EC-C046_KRK_HOLDING.md','formal/EndgameChess/Rules/KRKHolding/Equivalence.lean','EndgameChess.Rules.KRKHolding.holding_iff_not_force','leanprover/lean4:v4.35.0',sha,s['verified_utc'],'FIDE Laws of Chess 2023 legal-move kernel; RAW admitted history policy scope','theorems/frozen/EC-T0043/v1.md','FROZEN','From EC-C046. Separate own-source Gate Z;11 complete modules and10 declarations; standard-three only. Genuine policy/nonforcing duality and bounded stopped play; geometric classification/full FIDE/exact WDL-DTZ open.']
buf=io.StringIO(newline='');csv.writer(buf,lineterminator='\n').writerow(row);write('theorems/LEDGER.csv',old+buf.getvalue())
delta='S079 froze actual all-history RAW KRK holding duality and bounded stopped policy play as EC-T0043;43 bundles. Mathematical coverage is unchanged from S078; geometric outcomes, full FIDE correspondence and exact WDL/DTZ remain open.'
progress=read('docs/SESSION_PROGRESS.md').replace('through S078','through S079').replace('Forty-two','Forty-three').replace('all-history RAW holding formally verified','all-history RAW holding frozen')
progress=re.sub(r'Session change: [^\n]+','Session change: '+delta,progress);write('docs/SESSION_PROGRESS.md',progress)
table='| Endgames / target |'+progress.split('| Endgames / target |',1)[1].split('\n\n',1)[0]
prompt='''# NEXT SESSION — S080: Exact high-clock RAW KRK outcomes and strong nonloss

Owner2026-10-21: continue consecutive sessions until KRK closure; stop before
KQK. Fetch ALL heads, reconcile unmerged work/latest main; commit/push branch,
ordinary merge/push main and compare exact remote identities.43 frozen bundles
after EC-T0043, all-history actual RAW holding duality and150-h horizon available.

Direct principal candidate EC-C047, paper/audit BEFORE new Lean:
(1) Every admitted exact KRK root has an actual strong-side holding policy,
and weak-side full RuleForceMate is impossible, both turns/all incoming data.
(2) Ongoing weak-turn h>=99: strong nonforcing and actual weak holding.
(3) Ongoing strong-turn h>=98: strong forcing IFF an actual admitted child is
immediate named mate; otherwise both sides hold. Both colours/all actual flags,
every complete history/count/clock; no histogram or low-repetition assumption.
These are exact high-clock criteria, not a renamed generic game recurrence.

Strong nonloss: actual KRK is not initial, last legal weak move at a strong-turn
root leaves weak king safe, so king-distance symmetry excludes strong check.
Every admitted KRK move retains KRK or dead KK; KRK-or-dead invariant excludes
weak Goal on every path. Use a globally legal policy and actual S078 safety
definition, not an assumed no-loss slogan. Root terminal/current mate respected.

High-clock proof: under a hypothetical strong certificate at ongoing weak turn,
choose its retained legal child. A dead capture contradicts certificate
projection/nondeadness; retained KRK is quiet, actual append has h+1>=100 and
supports intended claim at parent. Contradicts noClaim. Do NOT assert every
weak KRK root has a quiet legal move without excluding dead captures. On strong
h>=98 a certified child is quiet KRK on weak turn with h>=99; if ongoing it
cannot force, if terminal its certificate is already Goal. Converse is actual
one-ply mate. Retain every legal move/current/intended claim and mate at150.

No unsupported classical16-move maximum. No tablebase/oracle/class enumeration
or stored certificates. Prior frozen sources/records immutable; one main theorem
per additive module and all main declarations in AxiomCheck. Separate adversarial
same-agent paper/Lean audits. Gate F is NEW own published-source GitHub clone,
.lake absent, full build/complete matching runner; record exact commands/exits/
times/UTC, source/import/executable hashes, clean identity and failures/retries.
Native official pinned4.35.0/inherited environment; no shim/dependency/TLS changes.
Gate Z separate. Relevant checks, full stable progress table/immediate delta,
full installed next prompt, current statuses and session closeout; publish/merge.

Full low-clock arbitrary-history geometry, FIDE rights/key/claim/adjudication
correspondence and exact WDL/DTZ remain closure obligations. The442/443 bounds
exceed100 and sufficient73 family is partial. Continue the next direct KRK
obligation after publication; do not call the high-clock family class closure.
'''
write('NEXT_SESSION.md',prompt)
candidate=read('research/CANDIDATES.md').replace('FORMAL_VERIFIED (S078); separate Gate Z pending','FROZEN as EC-T0043 (S079)');write('research/CANDIDATES.md',candidate)
for p in ['README.md','docs/ROADMAP.md','docs/KRK_COMPLETION.md']:
    text=read(p)
    if p=='README.md':text=text.replace('**After S077.** Forty-two frozen theorem bundles (not forty-two solved material classes).','**After S079.** Forty-three frozen theorem bundles (not forty-three solved material classes).')
    if p=='docs/KRK_COMPLETION.md':text=text.replace('42 frozen bundles after S077','43 frozen bundles after S079')
    write(p,text+'\n'+delta+' [EC-T0043]('+('../' if p.startswith('docs/') else '')+'theorems/frozen/EC-T0043/v1.md).\n')
append('theorems/README.md','- [EC-T0043](frozen/EC-T0043/v1.md): genuine actual all-history RAW KRK holding/nonforcing duality, full legal policies and bounded stopped play. [Own-source S079 Gate Z](frozen/VERIFICATION-S079/README.md).')
write('theorems/frozen/VERIFICATION-S079/README.md','# S079 — observed separate own-source holding Gate Z\n\n'+observed+'\n\nAll10 public types/11 complete modules; exact types/source boundary/transitive closure in [EC-T0043](../EC-T0043/v1.md). Same-agent audits, not external review. RAW scope only, no class/FIDE/distance closure. Full source/import/executable hashes, clean identity and logs retained here.\n')
write('sessions/evidence/S079/README.md','# S079 — actual holding freeze\n\n'+observed+'\n\nBase main9af2a6f0ff72cab56bab5c38bf3e029aee6b6dae, all heads fetched/no unmerged work. All sources/types and exact original proof/audits reread. No Lean edits. Replay deprecation warnings in prior frozen modules retained unchanged. Preservation/ledger/manifest/type/link/table/prompt/diff checks in checks.log.\n')
write('sessions/S079_FREEZE_KRK_HOLDING.md',f'''# S079 — Freeze actual all-history RAW KRK holding

2026-10-21. Base main9af2a6f0ff72cab56bab5c38bf3e029aee6b6dae, all heads
fetched/no unmerged work; branch session/s079-freeze-krk-holding.
EC-C046 frozen as EC-T0043 after observed separate own-source Gate Z.
{observed}
[Manifest](../theorems/frozen/EC-T0043/v1.md),
[evidence](../theorems/frozen/VERIFICATION-S079/README.md).

Both turns/player/material colours/all actual flags/full incoming histories,
globally legal actual policy, all-opponent-reply safety and correct zero-ply
claims. Saturation supplies genuine defensive choice; full converse and bounded
maximal/stopped play. RAW policy duality is not a geometric outcome formula,
full FIDE correspondence or exact WDL/DTZ. Ten types/eleven complete modules
and original paper/audits/imports reviewed; same-agent, not independent external
review. Older frozen modules/records and42 ledger rows preserved. Exactly one
new row. No oracle/enumeration/certificates, no new Lean or incremental build.
Relevant checks in evidence/S079/checks.log; they are packaging evidence only.
Publication recorded by Git commit/push, ordinary main merge/push and exact
remote identity comparison. Next direct S080 claim is exact high-clock forcing
criteria and universal strong holding; stop before KQK.

{table}

Session change: {delta}

## Full installed next prompt

{prompt}''')
append('sessions/SESSION_LEDGER.md','| S079 | 2026-10-21 | Freeze actual RAW KRK holding (Gate Z) | Separate own-source new179-job build/364 permitted reports; complete own-source/import/runner equality. [Closeout](S079_FREEZE_KRK_HOLDING.md); direct S080 high-clock outcomes | **+1 -> EC-T0043 FROZEN** (43 bundles); no new mathematical coverage |')
print(observed)
