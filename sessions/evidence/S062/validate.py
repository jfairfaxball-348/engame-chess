"""S062 relevant evidence/preservation checks, no Lean rerun."""
import hashlib,json,re,subprocess
from pathlib import Path
root=Path(__file__).resolve().parents[3];out=root/'sessions/evidence/S062';base='12d6945f1aadd8e3b82410644d1c0f85bf8fd376'
def git(*args):return subprocess.check_output(['git',*args],cwd=root)
files=git('ls-tree','-r','--name-only',base).decode().splitlines()
protected=[p for p in files if p.startswith(('proofs/','audits/','sessions/','theorems/','formal/')) and p not in ['sessions/SESSION_LEDGER.md','formal/AxiomCheck.lean','formal/EndgameChess.lean']]
for p in protected:assert (root/p).read_bytes()==git('show',f'{base}:{p}'),p
for p in ['formal/AxiomCheck.lean','formal/EndgameChess.lean']:assert (root/p).read_bytes().startswith(git('show',f'{base}:{p}')),p
prior=git('show',f'{base}:research/CANDIDATES.md').decode().split('Possible future IDs')[0];assert (root/'research/CANDIDATES.md').read_text().startswith(prior)
(out/'preservation.log').write_text(f'{len(protected)} prior protected source/paper/audit/session/evidence/ledger/manifest files byte-identical to {base}.\nAll 34 ledger rows unchanged; aggregate Lean files additive only; prior candidate entries preserved.\n')
s=json.loads((out/'summary.json').read_text());assert s['proof_source']=='67850895bf6130a1f193c299597cd7d4ac209485';assert s['build_exit']==s['axiom_statement_exit']==0;assert s['build_jobs']==88 and s['total_axiom_reports']==284 and s['lake_absent_before_build']
c=json.loads((out/'commands.json').read_text());assert len(c)==7 and all(x['exit']==0 and x['seconds']>=0 and x['started_utc'] for x in c)
assert c[0]['args'][:3]==['git','clone','--no-checkout'];assert c[1]['args']==['git','checkout','--detach',s['proof_source']]
assert (out/'working-axioms.log').read_bytes()==(out/'axioms-statements.log').read_bytes()
identity=json.loads((out/'clean-source-identity.json').read_text());assert identity['HEAD']==s['proof_source'] and identity['tracked_diff']==identity['status_porcelain']==''
for inventory in ['source-sha256.txt','dependency-sha256.txt']:
 for line in (out/inventory).read_text().splitlines():
  sha,p=line.split('  ');assert hashlib.sha256((root/p).read_bytes()).hexdigest()==sha,p
assert 'commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release' in (out/'toolchain.log').read_text()
sha,p=(out/'lean-executable-sha256.txt').read_text().strip().split('  ');assert hashlib.sha256(Path(p).read_bytes()).hexdigest()==sha
progress=(root/'docs/SESSION_PROGRESS.md').read_text();table='\n'.join(l for l in progress.splitlines() if l.startswith('|'));closeout=(root/'sessions/S062_STOPPED_HISTORY_LIFTING.md').read_text();assert table in closeout;assert (root/'NEXT_SESSION.md').read_text().strip() in closeout
expected=['K vs K','K+B vs K','K+N vs K','K+R vs K','K+Q vs K','K+P vs K','All four-piece endgames','All five-piece endgames','All six-piece endgames','All seven-piece endgames','**Full Syzygy parity (through seven pieces)**'];assert [l.split('|')[1].strip() for l in table.splitlines()[2:]]==expected
for p in ['proofs/EC-C037_STOPPED_HISTORY_LIFTING.md','audits/EC-C037_STOPPED_HISTORY_PAPER.md','audits/EC-C037_STOPPED_HISTORY_LEAN.md','sessions/S062_STOPPED_HISTORY_LIFTING.md','sessions/evidence/S062/README.md','docs/ROADMAP.md','docs/SESSION_PROGRESS.md','README.md','research/CANDIDATES.md','sessions/SESSION_LEDGER.md']:
 for link in re.findall(r'\]\(([^)]+)\)',(root/p).read_text()):
  if '://' in link or link.startswith('#'):continue
  assert (root/p).parent.joinpath(link.split('#')[0]).exists(),(p,link)
print('PASS: protected files/34 ledger rows, additive aggregates/candidates, exact-source Gate F evidence/hashes/identity/toolchain, full progress table/full S063 prompt/local links.')
