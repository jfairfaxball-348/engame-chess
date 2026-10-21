"""Preserve all frozen/Lean evidence; check honest paper-only session records."""
import csv,hashlib,io,json,re,subprocess,sys
from pathlib import Path
r=Path(__file__).resolve().parents[3]
out=Path(sys.argv[1]) if len(sys.argv)>1 else r/'sessions/evidence/S089/checks.log'
logs=[]
def run(args):
    p=subprocess.run(args,cwd=r,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    logs.append('$ '+' '.join(args)+'\n'+p.stdout.decode('utf-8',errors='replace').replace('\r\n','\n'))
    out.write_text('\n'.join(logs),encoding='utf-8',newline='\n')
    assert p.returncode==0,args
run(['python','-m','unittest','discover','-s','tests','-p','test_validate_ledger.py'])
run(['python','scripts/validate_ledger.py'])
base='e76dc645e8e1cd1d71dab9761e829e1704f28990'
files=subprocess.check_output(['git','ls-tree','-r','--name-only',base],cwd=r,text=True).splitlines()
kept=[p for p in files if p.startswith('formal/') or p.startswith('theorems/frozen/') or p=='theorems/LEDGER.csv']
batch=subprocess.run(['git','cat-file','--batch'],cwd=r,input=('\n'.join(base+':'+p for p in kept)+'\n').encode(),stdout=subprocess.PIPE,check=True)
stream=io.BytesIO(batch.stdout)
for p in kept:
    header=stream.readline().split();assert header[1]==b'blob',p
    data=stream.read(int(header[2]));assert stream.read(1)==b'\n'
    assert (r/p).read_bytes().replace(b'\r\n',b'\n')==data,p
assert len(list(csv.DictReader((r/'theorems/LEDGER.csv').open(encoding='utf-8'))))==47
for p in ['source-sha256.txt','dependency-sha256.txt','declarations.txt','axioms-statements.log']:
    assert (r/'theorems/frozen/VERIFICATION-S088'/p).read_text(encoding='utf-8')==(r/'sessions/evidence/S087/gate-f'/p).read_text(encoding='utf-8'),p
d=json.loads((r/'sessions/evidence/S089/small-box.json').read_text(encoding='utf-8'))
assert d['corner_terminal_lengths']==[5,7] and len(d['corner_distinct_edges'])==9
assert len(d['check_restore_cycle'])==8 and d['independent_direct_edge_replay']
assert not d['universal_class_or_RAW_history_certificate']
command=json.loads((r/'sessions/evidence/S089/commands.json').read_text(encoding='utf-8'))
assert command['exit']==0
for p,h in d['source_hashes'].items():
    canon=(r/p).read_bytes().replace(b'\r\n',b'\n')
    assert h in [hashlib.sha256(v).hexdigest() for v in [canon,canon.replace(b'\n',b'\r\n')]],p
progress=(r/'docs/SESSION_PROGRESS.md').read_text(encoding='utf-8')
table='| Endgames / target |'+progress.split('| Endgames / target |',1)[1].split('\n\n',1)[0]
close=(r/'sessions/S089_KRK_SMALL_BOX.md').read_text(encoding='utf-8')
assert table+'\n\nSession change:' in close
assert (r/'NEXT_SESSION.md').read_text(encoding='utf-8') in close
assert 'NOT Lean verified' in (r/'proofs/KRK_SMALL_BOX_S089.md').read_text(encoding='utf-8')
changed=subprocess.check_output(['git','diff','--name-only',base],cwd=r,text=True).splitlines()+subprocess.check_output(['git','ls-files','--others','--exclude-standard'],cwd=r,text=True).splitlines()
for p in set(changed):
    if not p.endswith('.md'):continue
    for target in re.findall(r'\]\(([^)]+)\)',(r/p).read_text(encoding='utf-8')):
        if re.match(r'[a-zA-Z]+:|#',target):continue
        assert ((r/p).parent/target.split('#')[0]).exists(),(p,target)
run(['git','diff','--check'])
message=f'PASS: {len(kept)} prior COMPLETE formal/config/runner/frozen/ledger files unchanged.47 rows; original separate Gate F/Z full inventories/runner still match. Selected corner5/7-ply mates9 edges and8-cycle independently replayed; actual command exit0/source hashes retained. Paper-only proof boundary/full table/delta/prompt/local links/diff passed; full KRK remains open.'
logs.append(message);out.write_text('\n'.join(logs)+'\n',encoding='utf-8',newline='\n');print(message)
