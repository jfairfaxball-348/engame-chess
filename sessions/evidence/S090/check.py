"""S090 exact-source Gate F closeout and earlier frozen-source preservation."""
import csv,io,json,re,subprocess
from pathlib import Path
r=Path(__file__).resolve().parents[3]
base='7802897decb8a5d6e9e618f0e5f176ce6e0e0516'
sha='2311abe71bc1a4eed47026feccd5ba5a0760d5bb'
e=r/'sessions/evidence/S090/gate-f93'
s=json.loads((e/'summary.json').read_text(encoding='utf-8'))
assert s['proof_source']==sha and s['build_exit']==s['axiom_statement_exit']==0
assert s['lake_absent_before_build'] and s['complete_runner_matches_working']
assert s['source_matches_published_git_bytes']
assert len(s['complete_modules'])==29 and len(s['bundle_declarations'])==26
assert s['total_axiom_reports']==421 and s['build_jobs']==243
assert all(set(v.split(', ')) <= {'propext','Classical.choice','Quot.sound'} for v in s['bundle_axioms'].values())
files=subprocess.check_output(['git','ls-tree','-r','--name-only',base],cwd=r,text=True).splitlines()
kept=[p for p in files if (p.startswith('formal/') and p not in ['formal/AxiomCheck.lean','formal/EndgameChess.lean']) or p.startswith('theorems/frozen/')]
data=subprocess.check_output(['git','cat-file','--batch'],cwd=r,input=('\n'.join(base+':'+p for p in kept)+'\n').encode())
stream=io.BytesIO(data)
for p in kept:
    header=stream.readline().split();assert header[1]==b'blob',p
    old=stream.read(int(header[2]));assert stream.read(1)==b'\n'
    assert (r/p).read_bytes().replace(b'\r\n',b'\n')==old,p
old=subprocess.check_output(['git','show',base+':theorems/LEDGER.csv'],cwd=r)
assert (r/'theorems/LEDGER.csv').read_bytes().replace(b'\r\n',b'\n')==old
assert len(list(csv.DictReader(io.StringIO(old.decode()))))==47
for p in s['complete_modules']+['formal/AxiomCheck.lean','formal/EndgameChess.lean']:
    own=subprocess.check_output(['git','show',sha+':'+p],cwd=r)
    assert (r/p).read_bytes().replace(b'\r\n',b'\n')==own,p
progress=(r/'docs/SESSION_PROGRESS.md').read_text(encoding='utf-8')
table='| Endgames / target |'+progress.split('| Endgames / target |',1)[1].split('\n\n',1)[0]
close=(r/'sessions/S090_KRK_DIRECT_OBLIGATIONS.md').read_text(encoding='utf-8')
assert table in close
assert (r/'NEXT_SESSION.md').read_text(encoding='utf-8') in close
logs=[]
for args in [['python','scripts/validate_ledger.py'],['git','diff','--check']]:
    p=subprocess.run(args,cwd=r,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    logs.append('$ '+' '.join(args)+'\n'+p.stdout.decode('utf-8',errors='replace'))
    assert p.returncode==0,args
changed=subprocess.check_output(['git','diff','--name-only',base],cwd=r,text=True).splitlines()
changed+=subprocess.check_output(['git','ls-files','--others','--exclude-standard'],cwd=r,text=True).splitlines()
for p in set(changed):
    if not p.endswith('.md'):continue
    for target in re.findall(r'\]\(([^)]+)\)',(r/p).read_text(encoding='utf-8')):
        if re.match(r'[a-zA-Z]+:|#',target):continue
        assert ((r/p).parent/target.split('#')[0]).exists(),(p,target)
message=f'PASS: own-source93 Gate F243 jobs/421 reports;29 complete modules/26 exact main types. {len(kept)} earlier complete formal/frozen files preserved; ledger exactly47 unchanged. New formal source matches published2311abe. Full stable table, installed next prompt, local links and diff pass. Separate Gate Z pending; KRK NOT CLOSED.'
logs.append(message)
(r/'sessions/evidence/S090/checks.log').write_text('\n'.join(logs)+'\n',encoding='utf-8',newline='\n')
print(message)
