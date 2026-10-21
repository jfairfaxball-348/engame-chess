"""Narrow preservation, evidence and closeout checks; no mathematical upgrade."""
import csv,hashlib,io,json,re,subprocess
from pathlib import Path
r=Path(__file__).resolve().parents[3]
out=r/'sessions/evidence/S087/checks.log'
logs=[]
def run(args):
    p=subprocess.run(args,cwd=r,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    logs.append('$ '+' '.join(args)+'\n'+p.stdout.decode('utf-8',errors='replace').replace('\r\n','\n'))
    out.write_text('\n'.join(logs),encoding='utf-8',newline='\n')
    assert p.returncode==0,args
run(['python','-m','unittest','discover','-s','tests','-p','test_validate_ledger.py'])
run(['python','scripts/validate_ledger.py'])
base='a58d6be5bb3109385c5bba2e4a743f0c164958a0'
files=subprocess.check_output(['git','ls-tree','-r','--name-only',base],cwd=r,text=True).splitlines()
kept=[p for p in files if (p.startswith('formal/') and p not in ['formal/EndgameChess.lean','formal/AxiomCheck.lean']) or p.startswith('theorems/frozen/') or p=='theorems/LEDGER.csv']
batch=subprocess.run(['git','cat-file','--batch'],cwd=r,input=('\n'.join(base+':'+p for p in kept)+'\n').encode(),stdout=subprocess.PIPE,check=True)
stream=io.BytesIO(batch.stdout)
for p in kept:
    header=stream.readline().split();assert header[1]==b'blob',p
    data=stream.read(int(header[2]));assert stream.read(1)==b'\n'
    assert (r/p).read_bytes().replace(b'\r\n',b'\n')==data,p
assert len(list(csv.DictReader((r/'theorems/LEDGER.csv').open(encoding='utf-8'))))==46
s=json.loads((r/'sessions/evidence/S087/gate-f/summary.json').read_text(encoding='utf-8'))
assert s['total_axiom_reports']==395 and len(s['complete_modules'])==6 and len(s['bundle_declarations'])==5
for p in s['complete_modules']:
    assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by|extern)\b',(r/p).read_text(encoding='utf-8')),p
    original=subprocess.check_output(['git','show',s['proof_source']+':'+p],cwd=r)
    assert (r/p).read_bytes().replace(b'\r\n',b'\n')==original,p
d=json.loads((r/'sessions/evidence/S087/guarded-box.json').read_text(encoding='utf-8'))
assert len(d['results'])==6 and len(d['width_four_cycle'])==16 and d['independent_direct_edge_replay']
assert sum(v['weak_edges'] for v in d['results'])==261
assert sum(v['weak_nodes'] for v in d['results'])==57
for p,h in d['source_hashes'].items():
    blob=subprocess.check_output(['git','show',s['proof_source']+':'+p.replace('\\','/')],cwd=r)
    assert h in [hashlib.sha256(v).hexdigest() for v in [blob,blob.replace(b'\n',b'\r\n')]],p
progress=(r/'docs/SESSION_PROGRESS.md').read_text(encoding='utf-8')
table='| Endgames / target |'+progress.split('| Endgames / target |',1)[1].split('\n\n',1)[0]
close=(r/'sessions/S087_KRK_GUARDED_BOX.md').read_text(encoding='utf-8')
assert table+'\n\nSession change:' in close
assert (r/'NEXT_SESSION.md').read_text(encoding='utf-8') in close
changed=subprocess.check_output(['git','diff','--name-only',base],cwd=r,text=True).splitlines()+subprocess.check_output(['git','ls-files','--others','--exclude-standard'],cwd=r,text=True).splitlines()
for p in set(changed):
    if not p.endswith('.md'):continue
    for target in re.findall(r'\]\(([^)]+)\)',(r/p).read_text(encoding='utf-8')):
        if re.match(r'[a-zA-Z]+:|#',target):continue
        assert ((r/p).parent/target.split('#')[0]).exists(),(p,target)
run(['git','diff','--check'])
message=f'PASS: {len(kept)} prior source/config/frozen/ledger files unchanged as canonical Git bytes.46 ledger rows unchanged; six own-source modules/five exact main types/395 reports; selected diagnostics57 nodes/261 weak edges and16-ply cycle; original runtime source hashes match published LF/CRLF encodings; full table/delta/prompt/local links/diff passed.'
logs.append(message)
out.write_text('\n'.join(logs)+'\n',encoding='utf-8',newline='\n')
print(message)
