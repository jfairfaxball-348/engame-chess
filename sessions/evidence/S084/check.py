import csv,io,json,re,subprocess
from pathlib import Path
r=Path(__file__).resolve().parents[3];out=r/'sessions/evidence/S084/checks.log';logs=[]
def run(args):
    p=subprocess.run(args,cwd=r,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    logs.append('$ '+' '.join(args)+'\n'+p.stdout.decode('utf-8',errors='replace'))
    out.write_text('\n'.join(logs),encoding='utf-8');assert p.returncode==0,args
run(['python','-m','unittest','discover','-s','tests','-p','test_validate_ledger.py'])
run(['python','scripts/validate_ledger.py'])
base='83da892f7a082328873e4dafc174cde559569936'
files=subprocess.check_output(['git','ls-tree','-r','--name-only',base],cwd=r,text=True).splitlines()
kept=[p for p in files if (p.startswith('formal/') and p not in ['formal/EndgameChess.lean','formal/AxiomCheck.lean']) or p.startswith('theorems/frozen/') or p=='theorems/LEDGER.csv']
batch=subprocess.run(['git','cat-file','--batch'],cwd=r,input=('\n'.join(base+':'+p for p in kept)+'\n').encode(),stdout=subprocess.PIPE,check=True)
stream=io.BytesIO(batch.stdout)
for p in kept:
    header=stream.readline().split();assert header[1]==b'blob',p
    data=stream.read(int(header[2]));assert stream.read(1)==b'\n'
    assert (r/p).read_bytes().replace(b'\r\n',b'\n')==data,p
assert len(list(csv.DictReader((r/'theorems/LEDGER.csv').open(encoding='utf-8'))))==45
s=json.loads((r/'sessions/evidence/S084/gate-f/summary.json').read_text(encoding='utf-8'))
assert s['total_axiom_reports']==390 and len(s['complete_modules'])==9 and len(s['bundle_declarations'])==8
for p in s['complete_modules']:
    assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by|extern)\b',(r/p).read_text(encoding='utf-8')),p
progress=(r/'docs/SESSION_PROGRESS.md').read_text(encoding='utf-8');table='| Endgames / target |'+progress.split('| Endgames / target |',1)[1].split('\n\n',1)[0]
close=(r/'sessions/S084_KRK_FRESH_HISTORY.md').read_text(encoding='utf-8')
assert table+'\n\nSession change:' in close
assert (r/'NEXT_SESSION.md').read_text(encoding='utf-8') in close
changed=subprocess.check_output(['git','diff','--name-only',base],cwd=r,text=True).splitlines()+subprocess.check_output(['git','ls-files','--others','--exclude-standard'],cwd=r,text=True).splitlines()
for p in changed:
    if not p.endswith('.md'):continue
    for target in re.findall(r'\]\(([^)]+)\)',(r/p).read_text(encoding='utf-8')):
        if re.match(r'[a-zA-Z]+:|#',target):continue
        assert ((r/p).parent/target.split('#')[0]).exists(),(p,target)
run(['git','diff','--check'])
logs.append(f'PASS: {len(kept)} prior source/config/frozen/ledger files preserved as canonical Git bytes using one git cat-file batch; only aggregate importer/runner changed.45 rows unchanged; observed390 permitted reports/9 complete modules/8 main types; no forbidden proof tokens; stable table/immediate delta/full prompt; local links/diff. Packaging checks add no mathematical claims.')
out.write_text('\n'.join(logs)+'\n',encoding='utf-8');print(logs[-1])
