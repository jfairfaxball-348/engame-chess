"""Check exact-source freeze and preserve all earlier formal/frozen evidence."""
import csv,io,json,re,subprocess
from pathlib import Path
r=Path(__file__).resolve().parents[3]
out=r/'sessions/evidence/S088/checks.log';logs=[]
def run(args):
    p=subprocess.run(args,cwd=r,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    logs.append('$ '+' '.join(args)+'\n'+p.stdout.decode('utf-8',errors='replace').replace('\r\n','\n'))
    out.write_text('\n'.join(logs),encoding='utf-8',newline='\n')
    assert p.returncode==0,args
run(['python','-m','unittest','discover','-s','tests','-p','test_validate_ledger.py'])
run(['python','scripts/validate_ledger.py'])
base='3e08ebead15c4fd9980174d9daa319b12f2fcfad'
files=subprocess.check_output(['git','ls-tree','-r','--name-only',base],cwd=r,text=True).splitlines()
kept=[p for p in files if p.startswith('formal/') or p.startswith('theorems/frozen/')]
batch=subprocess.run(['git','cat-file','--batch'],cwd=r,input=('\n'.join(base+':'+p for p in kept)+'\n').encode(),stdout=subprocess.PIPE,check=True)
stream=io.BytesIO(batch.stdout)
for p in kept:
    header=stream.readline().split();assert header[1]==b'blob',p
    data=stream.read(int(header[2]));assert stream.read(1)==b'\n'
    assert (r/p).read_bytes().replace(b'\r\n',b'\n')==data,p
ledger=(r/'theorems/LEDGER.csv').read_text(encoding='utf-8')
old=subprocess.check_output(['git','show',base+':theorems/LEDGER.csv'],cwd=r).decode('utf-8')
assert ledger.startswith(old)
rows=list(csv.DictReader(io.StringIO(ledger)));assert len(rows)==47
assert rows[-1]['theorem_id']=='EC-T0047' and rows[-1]['proof_commit_sha']=='84161c2650b902e98f37252532a706ec50f40ed4'
e=r/'theorems/frozen/VERIFICATION-S088'
s=json.loads((e/'summary.json').read_text(encoding='utf-8'))
assert s['gate']=='Z' and s['entire_own_gate_f_inventory_and_complete_runner_match']
for p in ['source-sha256.txt','dependency-sha256.txt','declarations.txt','axioms-statements.log']:
    assert (e/p).read_text(encoding='utf-8')==(r/'sessions/evidence/S087/gate-f'/p).read_text(encoding='utf-8'),p
assert len(s['complete_modules'])==6 and len(s['bundle_declarations'])==5 and s['total_axiom_reports']==395
manifest=(r/'theorems/frozen/EC-T0047/v1.md').read_text(encoding='utf-8')
for p in s['complete_modules']+s['bundle_declarations']:
    assert p in manifest,p
assert 'NOT a frozen declaration' in manifest
progress=(r/'docs/SESSION_PROGRESS.md').read_text(encoding='utf-8')
table='| Endgames / target |'+progress.split('| Endgames / target |',1)[1].split('\n\n',1)[0]
close=(r/'sessions/S088_KRK_GUARDED_BOX_FREEZE.md').read_text(encoding='utf-8')
assert table+'\n\nSession change:' in close
assert (r/'NEXT_SESSION.md').read_text(encoding='utf-8') in close
changed=subprocess.check_output(['git','diff','--name-only',base],cwd=r,text=True).splitlines()+subprocess.check_output(['git','ls-files','--others','--exclude-standard'],cwd=r,text=True).splitlines()
for p in set(changed):
    if not p.endswith('.md'):continue
    for target in re.findall(r'\]\(([^)]+)\)',(r/p).read_text(encoding='utf-8')):
        if re.match(r'[a-zA-Z]+:|#',target):continue
        assert ((r/p).parent/target.split('#')[0]).exists(),(p,target)
run(['git','diff','--check'])
message=f'PASS: {len(kept)} prior COMPLETE formal/frozen files unchanged; exact old ledger prefix retained with one new47th row. Own-source separate Gate Z full inventories/395-report runner match Gate F; all6 modules/5 declarations in immutable manifest;32 paper corollary excluded. Stable table/delta/full prompt/local links/diff passed.'
logs.append(message);out.write_text('\n'.join(logs)+'\n',encoding='utf-8',newline='\n');print(message)
