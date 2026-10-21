"""Check C052 freeze against exact Gate F/Z and preserve every older record."""
import csv,io,json,re,subprocess
from pathlib import Path
r=Path(__file__).resolve().parents[3]
base='c97102fbd253bbde9bbf20e6f525c630a5bc4950'
sha='2311abe71bc1a4eed47026feccd5ba5a0760d5bb'
e=r/'theorems/frozen/VERIFICATION-S091'
s=json.loads((e/'summary.json').read_text(encoding='utf-8'))
assert s['gate']=='Z' and s['entire_own_gate_f_inventory_and_complete_runner_match']
assert s['proof_source']==sha and s['build_exit']==s['axiom_statement_exit']==0
assert s['lake_absent_before_build'] and s['source_matches_published_git_bytes']
assert len(s['complete_modules'])==29 and len(s['bundle_declarations'])==26
assert s['total_axiom_reports']==421 and s['build_jobs']==243
for p in ['source-sha256.txt','dependency-sha256.txt','declarations.txt','axioms-statements.log']:
    assert (e/p).read_text(encoding='utf-8')==(r/'sessions/evidence/S090/gate-f93'/p).read_text(encoding='utf-8'),p
files=subprocess.check_output(['git','ls-tree','-r','--name-only',base],cwd=r,text=True).splitlines()
kept=[p for p in files if p.startswith('formal/') or p.startswith('theorems/frozen/')]
data=subprocess.check_output(['git','cat-file','--batch'],cwd=r,input=('\n'.join(base+':'+p for p in kept)+'\n').encode())
stream=io.BytesIO(data)
for p in kept:
    header=stream.readline().split();assert header[1]==b'blob',p
    old=stream.read(int(header[2]));assert stream.read(1)==b'\n'
    assert (r/p).read_bytes().replace(b'\r\n',b'\n')==old,p
old=subprocess.check_output(['git','show',base+':theorems/LEDGER.csv'],cwd=r).decode()
ledger=(r/'theorems/LEDGER.csv').read_text(encoding='utf-8');assert ledger.startswith(old)
rows=list(csv.DictReader(io.StringIO(ledger)))
assert len(rows)==48 and rows[-1]['theorem_id']=='EC-T0048'
assert rows[-1]['proof_commit_sha']==sha and rows[-1]['verified_utc']==s['verified_utc']
manifest=(r/'theorems/frozen/EC-T0048/v1.md').read_text(encoding='utf-8')
for item in s['complete_modules']+s['bundle_declarations']:assert item in manifest,item
assert 'KRK remains OPEN' in manifest and 'Positive' not in rows[-1]['title']
progress=(r/'docs/SESSION_PROGRESS.md').read_text(encoding='utf-8')
table='| Endgames / target |'+progress.split('| Endgames / target |',1)[1].split('\n\n',1)[0]
close=(r/'sessions/S091_KRK_CENTRAL_FREEZE.md').read_text(encoding='utf-8')
assert table in close and (r/'NEXT_SESSION.md').read_text(encoding='utf-8') in close
logs=[]
for args in [['python','-m','unittest','discover','-s','tests','-p','test_validate_ledger.py'],['python','scripts/validate_ledger.py'],['git','diff','--check']]:
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
message=f'PASS: separate own-source Gate Z243 jobs/421 reports; entire Gate F inventories/runner match.29 complete modules/26 exact types frozen as EC-T0048. {len(kept)} prior COMPLETE formal/frozen files unchanged; old47-row ledger prefix retained plus exactly one48th row. Full stable table, next prompt, links and diff pass. KRK NOT CLOSED.'
logs.append(message);(r/'sessions/evidence/S091/checks.log').write_text('\n'.join(logs)+'\n',encoding='utf-8',newline='\n')
print(message)
