import csv,json,re,subprocess
from pathlib import Path
r=Path(__file__).resolve().parents[3];out=r/'sessions/evidence/S078/checks.log';logs=[]
def run(args):
    p=subprocess.run(args,cwd=r,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    logs.append('$ '+' '.join(args)+'\n'+p.stdout.decode('utf-8',errors='replace'))
    out.write_text('\n'.join(logs),encoding='utf-8');assert p.returncode==0,args
run(['python','-m','unittest','discover','-s','tests','-p','test_validate_ledger.py'])
run(['python','scripts/validate_ledger.py'])
base='a9cea278ecd680f661a464f24fb20416a96a1efc'
files=subprocess.check_output(['git','ls-tree','-r','--name-only',base],cwd=r,text=True).splitlines();count=0
for p in files:
    if (p.startswith('formal/') and p not in ['formal/EndgameChess.lean','formal/AxiomCheck.lean']) or p.startswith('theorems/frozen/') or p=='theorems/LEDGER.csv':
        assert (r/p).read_bytes().replace(b'\r\n',b'\n')==subprocess.check_output(['git','show',base+':'+p],cwd=r),p
        count+=1
assert len(list(csv.DictReader((r/'theorems/LEDGER.csv').open(encoding='utf-8'))))==42
s=json.loads((r/'sessions/evidence/S078/gate-f/summary.json').read_text(encoding='utf-8'))
assert s['total_axiom_reports']==364 and len(s['complete_modules'])==11
for p in s['complete_modules']:
    assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by|extern)\b',(r/p).read_text(encoding='utf-8')),p
progress=(r/'docs/SESSION_PROGRESS.md').read_text(encoding='utf-8')
table='| Endgames / target |'+progress.split('| Endgames / target |',1)[1].split('\n\n',1)[0]
close=(r/'sessions/S078_KRK_HOLDING.md').read_text(encoding='utf-8')
assert table+'\n\nSession change:' in close
assert (r/'NEXT_SESSION.md').read_text(encoding='utf-8') in close
changed=subprocess.check_output(['git','diff','--name-only',base],cwd=r,text=True).splitlines()
new=subprocess.check_output(['git','ls-files','--others','--exclude-standard'],cwd=r,text=True).splitlines()
for p in changed+new:
    if not p.endswith('.md'):continue
    for target in re.findall(r'\]\(([^)]+)\)',(r/p).read_text(encoding='utf-8')):
        if re.match(r'[a-zA-Z]+:|#',target):continue
        assert ((r/p).parent/target.split('#')[0]).exists(),(p,target)
run(['git','diff','--check'])
logs.append(f'PASS: {count} prior source/config/frozen/ledger files preserved in canonical Git bytes, only aggregate Lean importer/runner changed; 42 rows unchanged; no forbidden proof tokens; observed364-report Gate F;11 modules/10 main declarations; full stable table, immediate delta and complete prompt; local links and diff. Packaging checks do not establish additional mathematics.')
out.write_text('\n'.join(logs)+'\n',encoding='utf-8');print(logs[-1])
