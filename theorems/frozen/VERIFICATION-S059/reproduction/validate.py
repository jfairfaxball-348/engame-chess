"""S059 evidence/preservation checks without rerunning Lean. Usage: validate.py REPO_ROOT"""
import csv,hashlib,io,json,re,subprocess,sys
from pathlib import Path
root=Path(sys.argv[1]).resolve();out=root/'theorems/frozen/VERIFICATION-S059'
base='1ff410bb4f2c92f25ca24cf1fab4fc791e28e02a'
def git(*a): return subprocess.check_output(['git',*a],cwd=root)
allowed={'NEXT_SESSION.md','README.md','docs/ROADMAP.md','docs/SESSION_PROGRESS.md','research/CANDIDATES.md','sessions/SESSION_LEDGER.md','theorems/README.md','theorems/LEDGER.csv'}
prior=git('ls-tree','-r','--name-only',base).decode().splitlines()
protected=[p for p in prior if p not in allowed]
for p in protected: assert (root/p).read_bytes()==git('show',f'{base}:{p}'),p
before=git('show',f'{base}:research/CANDIDATES.md').decode().splitlines();after=(root/'research/CANDIDATES.md').read_text().splitlines()
assert [l for l in before if not l.startswith('| EC-C035 |')]==[l for l in after if not l.startswith('| EC-C035 |')]
old=git('show',f'{base}:theorems/LEDGER.csv');new=(root/'theorems/LEDGER.csv').read_bytes()
assert new.startswith(old)
rows=list(csv.DictReader(io.StringIO(new.decode())));assert len(rows)==33 and rows[-1]['theorem_id']=='EC-T0033'
s=json.loads((out/'summary.json').read_text());assert s['build_exit']==s['axiom_statement_exit']==0
assert s['build_jobs']==84 and s['total_axiom_reports']==282 and s['lake_absent_before_build']
assert s['proof_source']=='c75b3760022717e586a789e47c09c03911a43a56'
commands=json.loads((out/'commands.json').read_text());assert len(commands)==6 and all(c['exit']==0 for c in commands)
assert commands[0]['args'][:3]==['git','clone','--no-checkout']
assert commands[1]['args']==['git','checkout','--detach',s['proof_source']]
assert (out/'axioms-statements.log').read_bytes()==(root/'sessions/evidence/S058/axioms-statements.log').read_bytes()
assert not re.search(r'sorryAx|Lean.ofReduceBool|error:|warning:',(out/'axioms-statements.log').read_text())
identity=json.loads((out/'clean-source-identity.json').read_text());assert identity['HEAD']==s['proof_source'] and identity['tracked_diff']==identity['status_porcelain']==''
manifest=(root/'theorems/frozen/EC-T0033/v1.md').read_text()
assert s['proof_source'] in manifest and s['verified_utc'] in manifest
for p in s['complete_modules']: assert (root/p).read_text() in manifest
for inventory in ['source-sha256.txt','dependency-sha256.txt']:
 for line in (out/inventory).read_text().splitlines():
  sha,p=line.split('  ');assert hashlib.sha256((root/p).read_bytes()).hexdigest()==sha,p
assert 'commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release' in (out/'toolchain.log').read_text()
progress=(root/'docs/SESSION_PROGRESS.md').read_text();table='\n'.join(l for l in progress.splitlines() if l.startswith('|'))
closeout=(root/'sessions/S059_FREEZE_EXACT_RAW_THRESHOLD_EXCLUSION.md').read_text();assert table in closeout
assert (root/'NEXT_SESSION.md').read_text().strip() in closeout
assert table.splitlines()[-1].startswith('| **Full Syzygy parity') and len(table.splitlines())==13
for p in ['theorems/frozen/EC-T0033/v1.md','theorems/frozen/VERIFICATION-S059/README.md','sessions/S059_FREEZE_EXACT_RAW_THRESHOLD_EXCLUSION.md','README.md','docs/ROADMAP.md','docs/SESSION_PROGRESS.md','research/CANDIDATES.md','sessions/SESSION_LEDGER.md']:
 for link in re.findall(r'\]\(([^)]+)\)',(root/p).read_text()):
  if '://' in link or link.startswith('#'): continue
  assert (root/p).parent.joinpath(link.split('#')[0]).exists(),(p,link)
(out/'preservation.log').write_text(f'{len(protected)} prior files byte-identical; all formal source unchanged; prior 32 ledger rows preserved, exactly EC-T0033 appended.\n')
print('PASS: exact-source Gate Z evidence, Gate F equality, statements/axioms/hashes, clean identity, immutable boundaries, preservation, ledger, full table/prompt and local links.')
