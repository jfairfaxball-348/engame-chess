"""Create S077 records only after observed successful exact-source Gate Z."""
import csv
import io
import json
from pathlib import Path
import subprocess

r=Path(__file__).resolve().parents[3]
e=r/'theorems/frozen/VERIFICATION-S077'
s=json.loads((e/'summary.json').read_text(encoding='utf-8'))
assert s['build_exit']==s['axiom_statement_exit']==0
assert s['complete_runner_matches_own_gate_f'] and s['entire_source_and_dependency_inventories_match_own_gate_f']
sha=s['proof_source']
def write(p,text):
    (r/p).parent.mkdir(parents=True,exist_ok=True)
    (r/p).write_text(text,encoding='utf-8',newline='\n')
def read(p): return (r/p).read_text(encoding='utf-8')
def replace(p,a,b):
    t=read(p)
    assert a in t,(p,a)
    write(p,t.replace(a,b))
original=read('theorems/LEDGER.csv')
assert len(list(csv.DictReader(io.StringIO(original))))==41
manifest=f'''# EC-T0042 v1 — Universal admitted RAW KRK clock-bounded termination

Status: FROZEN (S077, 2026-10-21). Candidate EC-C045.
Full verified OWN proof-source: `{sha}`.
Representative: `EndgameChess.Rules.KRKTermination.krk_clock_cap`.

## Statement, scope and trust

For either strong colour, BOTH turns, ALL flags and EVERY actual legal move,
the existing initial-rooted admitted RawHistoryLayer.State has universal KRK
board-play termination. No strategy, rook safety, noRights, low clock or incoming
repetition restriction is assumed. Legal strong castling is included by two
symbolic canCastle schemas with universally quantified weak-king coordinates.
Weak rook capture gives terminal dead KK, including its reset counter.

Region is exact KRK OR terminal. Typed admitted BoardStep forces parent ongoing;
every step preserves Region and spends at least one fuel, where fuel is
150 minus stored clock on ongoing states and zero on all terminal states.
Every finite typed path satisfies fuel(end)+length<=fuel(root). Hence an ongoing
exact KRK root of clock h has at most150-h board plies; terminal roots have zero.
No successor iff terminal; maximal board endpoints are terminal and some terminal
continuation exists. Arbitrary truncated prefixes need not be terminal. Claims
are separate stopping actions consuming zero board plies. Mate at150 remains
mate-first; terminal fuel zero does not imply draw.

This is RAW termination, NOT complete outcome/holding, full FIDE key/rights/
claim/adjudication correspondence, exact distance or WDL/DTZ parity. Rule edition
is the existing FIDE2023 legal-move kernel and chosen RAW classifier. The model,
core Lean kernel and standard axioms remain the trust boundary. No engine,
tablebase, exhaustive class proof, per-position certificate or novelty claim.

## Paper and audits

[Standalone paper](../../../proofs/EC-C045_KRK_CLOCK_TERMINATION.md),
[separate same-agent paper audit](../../../audits/EC-C045_KRK_CLOCK_TERMINATION_PAPER.md),
[Lean fidelity audit](../../../audits/EC-C045_KRK_CLOCK_TERMINATION_LEAN.md).
Paper/audit preceded Lean in S076; same-agent review is not independent review.
All ten public statements, eleven complete modules and frozen imports are
included. All private helpers and shared Definitions are frozen in full.

## Separate own-source Gate Z

ONE NEW GitHub clone `{s['fresh_clone']}`, exact OWN SHA above;
formal/.lake absent before full build. {s['build_jobs']}-job build exit0 in
{s['build_seconds']}s; COMPLETE matching own AxiomCheck exit0 at
{s['verified_utc']}, {s['total_axiom_reports']} reports. Every declaration uses
only propext/Classical.choice/Quot.sound (or fewer).
ENTIRE own Gate F source/transitive inventories and decoded complete runner
match. Native Windows official Lean4.35.0, source revision
eb6cafb7290e8bd5f2937522d8d804f58f02bafc; original Gate F used Linux.
This platform adaptation is explicit: inherited native environment, no old Linux
ELAN_HOME override, no shim/dependency/TLS/checksum change. Clone core.autocrlf=false
preserves committed bytes. Prior frozen source/records remain byte-identical.
No Lean edits or incremental substitute. Hosted CI unobserved.

[Summary](../VERIFICATION-S077/summary.json),
[full build](../VERIFICATION-S077/lake-build.log),
[complete runner](../VERIFICATION-S077/axioms-statements.log),
[commands/exits/times/UTC](../VERIFICATION-S077/commands.json),
[source inventory](../VERIFICATION-S077/source-sha256.txt),
[transitive inventory](../VERIFICATION-S077/dependency-sha256.txt),
[clean identity](../VERIFICATION-S077/clean-source-identity.json).

## Complete newly frozen source boundary

```text
'''
inventory=read('theorems/frozen/VERIFICATION-S077/source-sha256.txt').splitlines()
manifest+='\n'.join(line for line in inventory if line.split('  ',1)[1] in s['complete_modules'])+'\n```\n\n## Full transitive project source closure\n\n```text\n'+read('theorems/frozen/VERIFICATION-S077/dependency-sha256.txt')+'```\n\n## Verbatim observed public statements\n\n```text\n'
log=read('theorems/frozen/VERIFICATION-S077/axioms-statements.log')
for n in s['bundle_declarations']:
    import re
    m=re.search(r'^@?'+re.escape(n)+r' :.*?(?=^\S|\Z)',log,re.M|re.S)
    assert m,n
    manifest+=m[0].rstrip()+'\n\n'
manifest+='```\n'
write('theorems/frozen/EC-T0042/v1.md',manifest)
fields=list(csv.DictReader(io.StringIO(original)).fieldnames)
row=['EC-T0042','Universal admitted RAW KRK clock-bounded termination','theorems/frozen/EC-T0042/v1.md','proofs/EC-C045_KRK_CLOCK_TERMINATION.md','formal/EndgameChess/Rules/KRKTermination/ClockCap.lean','EndgameChess.Rules.KRKTermination.krk_clock_cap','leanprover/lean4:v4.35.0',sha,s['verified_utc'],'FIDE Laws of Chess 2023 legal-move kernel; RAW admitted histories','theorems/frozen/EC-T0042/v1.md','FROZEN','From EC-C045. Separate own-source native Windows Gate Z; 11 complete modules and 10 declarations; standard-three axioms only. Universal termination; full FIDE outcomes/holding and WDL/DTZ remain open.']
buf=io.StringIO(newline=''); csv.writer(buf,lineterminator='\n').writerow(row)
write('theorems/LEDGER.csv',original+buf.getvalue())
delta='S077 froze universal admitted RAW KRK termination as EC-T0042 after separate own-source Gate Z; 42 bundles. Complete RAW holding/outcomes, full FIDE correspondence and exact WDL/DTZ remain open. Owner resumed consecutive KRK sessions until closure; stop before KQK.'
table=read('docs/SESSION_PROGRESS.md').split('| Endgames / target |',1)[1].split('\n\n',1)[0]
table='| Endgames / target |'+table
table=table.replace('bounds frozen; universal RAW termination formally verified','bounds and universal RAW termination frozen')
progress=read('docs/SESSION_PROGRESS.md')
progress=progress.replace('Current mathematical evidence: through S076. Forty-one theorem bundles are frozen; universal admitted RAW KRK termination is formally verified awaiting freeze.','Current mathematical evidence: through S077. Forty-two theorem bundles are frozen, including universal admitted RAW KRK termination.')
old=read('docs/SESSION_PROGRESS.md').split('| Endgames / target |',1)[1].split('\n\n',1)[0]
progress=progress.replace('| Endgames / target |'+old,table)
import re
progress=re.sub(r'Session change: [^\n]+','Session change: '+delta,progress)
write('docs/SESSION_PROGRESS.md',progress)
prompt='''# NEXT SESSION — S078: All-history RAW KRK holding strategies

Owner instruction 2026-10-21: run next session and keep going until KRK is closed.
S077 resumed the previously paused campaign; stop before KQK. All proof/audit/
Lean/freeze gates remain mandatory. Fetch all remote heads; merge prior work;
start from latest main; commit/push branch, merge/push main, compare identities.
42 frozen bundles after EC-T0042, exact own-source termination freeze complete.

Principal claim EC-C046: on every existing admitted exact KRK history (both
turns/strong colours/all actual flags, every incoming repetition/clock), prove
that absence of the opponent's RuleForceMate is equivalent to existence of an
actual legal holding policy avoiding opponent mate on EVERY compliant play.
Define policy choices as actual admitted board children or correct present/
intended claims. Claims end immediately at zero board plies; every opponent
board reply remains, and opponent claims are terminal draws. Prove policy
legality, all-prefix safety, finite termination/claim endpoints using frozen
fuel and the converse against EVERY finite winning certificate. Do not define
holding to be the complement and then claim its equivalence by definition.

Exact blocked KRK step: universal150-h horizon alone gives neither defensive
choice nor holding. Smallest dependency is saturation of actual RuleMateWithin
at fuel on the KRK-or-terminal region, retaining full move/claim quantifiers;
it gives uniform child budgets needed to extract a losing reply when all
individual children have finite certificates. Exit directly to a legal holding
policy and its all-play proof. No generic finite-game slogan or renamed RW
counts as class closure. First standalone paper, then separate adversarial
same-agent paper audit BEFORE new additive Lean modules and AxiomCheck entries.

Preserve older frozen modules/records. Gate F requires observed new exact
published-source GitHub clone, .lake absent, full build and complete matching
runner; record actual native official toolchain/environment, exact statements,
source/transitive/executable hashes, logs/commands/exits/times/UTC, clean identity,
all failures/retries. Separate Gate Z later. No oracle/tablebase, exhaustive
class proof or per-position certificates. Report claim scope exactly: RAW holding
duality is direct progress, not a geometric all-history outcome characterisation,
full FIDE key/rights/claim/adjudication bridge or exact distance/WDL/DTZ parity.
The 442/443 bounds exceed100; failure of the partial73 histogram proves no draw.

Update candidate/roadmap/completion/README/progress/session ledger and closeout;
copy FULL next prompt and stable progress table with immediate delta. Continue
the next direct KRK obligation after publication while authorised; no promise of
closure before all outcome, correspondence, distance and freeze obligations pass.
'''
write('NEXT_SESSION.md',prompt)
replace('README.md','**After S076.** Forty-one frozen theorem bundles (not forty-one solved material classes).','**After S077.** Forty-two frozen theorem bundles (not forty-two solved material classes).')
with (r/'README.md').open('a',encoding='utf-8',newline='\n') as f: f.write('\nS077: '+delta+' [Freeze](theorems/frozen/EC-T0042/v1.md).\n')
with (r/'theorems/README.md').open('a',encoding='utf-8',newline='\n') as f: f.write('\n- [EC-T0042](frozen/EC-T0042/v1.md): universal admitted RAW KRK termination, every legal move/all flags/both turns; own S076 source, separate native Windows S077 Gate Z. [Evidence](frozen/VERIFICATION-S077/summary.json).\n')
for p in ['docs/ROADMAP.md','docs/KRK_COMPLETION.md']:
    text=read(p)
    # Preserve historical session evidence; add an explicit current override first.
    lines=text.splitlines(keepends=True)
    lines.insert(2,'Current owner direction (2026-10-21): resume consecutive KRK sessions until closure, superseding the S076 pause. Stop before KQK.\n\n')
    write(p,''.join(lines)+'\nS077: '+delta+' [EC-T0042](../theorems/frozen/EC-T0042/v1.md). S078 attacks genuine all-history RAW holding policies.\n')
candidate=read('research/CANDIDATES.md')
lines=candidate.splitlines()
for i,line in enumerate(lines):
    if line.startswith('| EC-C045 |'):
        lines[i]=line.replace('FORMAL_VERIFIED','FROZEN as EC-T0042')+' S077 separate own-source Gate Z observed; see EC-T0042. |' if not line.endswith('|') else line.replace('**FORMAL_VERIFIED**','**FROZEN as EC-T0042**').replace('Gate Z pending','S077 Gate Z passed')
write('research/CANDIDATES.md','\n'.join(lines)+'\n')
write('theorems/frozen/VERIFICATION-S077/README.md','# S077 — observed separate own-source Gate Z\n\n'+delta+'\n\nFresh GitHub clone, exact SHA '+sha+', .lake absent; full '+str(s['build_jobs'])+'-job build exit0 in '+str(s['build_seconds'])+'s, complete runner exit0 with354 permitted reports at '+s['verified_utc']+'. All original source/transitive inventory hashes match; complete decoded runner matches own Gate F. Native official Windows4.35.0, same Lean source revision as original Linux verification. No source/toolchain changes or incremental substitute. Hosted CI unobserved.\n\n[Summary](summary.json), [commands](commands.json), [build](lake-build.log), [runner](axioms-statements.log), [source](source-sha256.txt), [imports](dependency-sha256.txt), [clean identity](clean-source-identity.json).\n')
write('sessions/S077_FREEZE_KRK_TERMINATION.md',f'''# S077 — Freeze universal admitted RAW KRK termination

2026-10-21. Base main95059bd; branch session/s077-freeze-krk-termination.
All remote heads fetched, no unmerged earlier remote work. Owner explicitly
resumed consecutive sessions until KRK closure, superseding S076 pause.

EC-C045 frozen as [EC-T0042](../theorems/frozen/EC-T0042/v1.md), exact own
source `{sha}`. New GitHub clone without .lake, {s['build_jobs']}-job build
exit0 in{s['build_seconds']}s, complete354-report runner exit0 at{s['verified_utc']}.
ENTIRE own Gate F source/transitive inventory hashes and complete decoded runner
match. Ten public types/eleven complete new modules reviewed; standard-three only.
Native official Windows4.35.0 replaces unavailable old Linux path, same compiler
source revision; this adaptation is explicit. No Lean edits, shims, dependencies,
TLS/checksum changes or incremental substitutes. Hosted CI unobserved.
[Evidence](../theorems/frozen/VERIFICATION-S077/README.md).

Both turns/colours/all flags/every actual legal move including castling and
rook capture. Typed admission forces live parent; ongoing fuel150-h, terminal0;
all finite paths bounded, maximal endpoint terminal and continuation exists.
Mate at150 not relabelled draw. Claims stop at zero board plies. No strategy,
safety or incoming-history assumptions. No oracle/enumeration/certificates.
Full FIDE correspondence, complete outcomes/holding and exact WDL/DTZ OPEN.
Exactly one new ledger row, prior41 records/source preserved. Current milestone
C: return directly to actual holding-policy extraction using the frozen horizon.
The four-part dependency admission and exact next obligation are in the prompt.

Actual structural/preservation/link/diff checks are in evidence/S077/checks.log;
these are packaging checks, not new mathematical results. Publication is recorded
by Git: commit/push branch, ordinary merge/push main and exact remote comparison.

{table}

Session change: {delta}

## Full installed next prompt

{prompt}''')
with (r/'sessions/SESSION_LEDGER.md').open('a',encoding='utf-8',newline='\n') as f: f.write('\n| S077 | 2026-10-21 | Freeze universal RAW KRK termination (Gate Z) | Separate exact own-source native Windows fresh build and354-report runner; all source/import inventories match. [Closeout](S077_FREEZE_KRK_TERMINATION.md). Continue S078 holding under owner resumption | **+1 -> EC-T0042 FROZEN** (42 bundles); full closure open |\n')
print('S077 records created after successful Gate Z')
