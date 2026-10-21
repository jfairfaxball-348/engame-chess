"""Relevant ledger, preservation, exact manifest/types, links and closeout checks."""
import csv
import hashlib
import json
from pathlib import Path
import re
import subprocess

r=Path(__file__).resolve().parents[3]
out=r/'sessions/evidence/S079/checks.log'
lines=[]
def run(args):
    p=subprocess.run(args,cwd=r,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    lines.append('$ '+' '.join(args)+'\n'+p.stdout.decode('utf-8',errors='replace'))
    out.write_text('\n'.join(lines),encoding='utf-8')
    assert p.returncode==0,args
run(['python','-m','unittest','discover','-s','tests','-p','test_validate_ledger.py'])
run(['python','scripts/validate_ledger.py'])
base='9af2a6f0ff72cab56bab5c38bf3e029aee6b6dae'
files=subprocess.check_output(['git','ls-tree','-r','--name-only',base],cwd=r,text=True).splitlines()
count=0
for p in files:
    if p.startswith('formal/') or p.startswith('theorems/frozen/'):
        original=subprocess.check_output(['git','show',base+':'+p],cwd=r)
        current=(r/p).read_bytes()
        # Main worktree follows Windows core.autocrlf; compare canonical Git bytes.
        assert current.replace(b'\r\n',b'\n')==original,p
        count+=1
old=subprocess.check_output(['git','show',base+':theorems/LEDGER.csv'],cwd=r)
assert (r/'theorems/LEDGER.csv').read_bytes().replace(b'\r\n',b'\n').startswith(old)
rows=list(csv.DictReader((r/'theorems/LEDGER.csv').open(encoding='utf-8',newline='')))
assert len(rows)==43 and rows[-1]['theorem_id']=='EC-T0043'
summary=json.loads((r/'theorems/frozen/VERIFICATION-S079/summary.json').read_text(encoding='utf-8'))
manifest=(r/'theorems/frozen/EC-T0043/v1.md').read_text(encoding='utf-8')
log=(r/'theorems/frozen/VERIFICATION-S079/axioms-statements.log').read_text(encoding='utf-8')
for name in summary['bundle_declarations']:
    stmt=re.search(r'^@?'+re.escape(name)+r' :.*?(?=^\S|\Z)',log,re.M|re.S)[0].rstrip()
    assert stmt in manifest,name
for relative in summary['complete_modules']:
    assert relative in manifest,relative
    data=subprocess.check_output(['git','show',summary['proof_source']+':'+relative],cwd=r)
    assert hashlib.sha256(data).hexdigest() in manifest
progress=(r/'docs/SESSION_PROGRESS.md').read_text(encoding='utf-8')
table='| Endgames / target |'+progress.split('| Endgames / target |',1)[1].split('\n\n',1)[0]
closeout=(r/'sessions/S079_FREEZE_KRK_HOLDING.md').read_text(encoding='utf-8')
assert table in closeout
assert (r/'NEXT_SESSION.md').read_text(encoding='utf-8') in closeout
assert re.search(re.escape(table)+r'\n\nSession change:',closeout)
changed=subprocess.check_output(['git','diff','--name-only'],cwd=r,text=True).splitlines()
new=subprocess.check_output(['git','ls-files','--others','--exclude-standard'],cwd=r,text=True).splitlines()
for p in changed+new:
    if not p.endswith('.md'): continue
    content=(r/p).read_text(encoding='utf-8')
    for target in re.findall(r'\]\(([^)]+)\)',content):
        if re.match(r'[a-zA-Z]+:|#',target): continue
        target=target.split('#')[0]
        assert ((r/p).parent/target).exists(),(p,target)
run(['git','diff','--check'])
lines.append(f'PASS: {count} prior formal/config/frozen files preserved as canonical Git bytes; prior42 ledger rows unchanged; exactly43 rows; all10 exact public types and11 complete modules in manifest; source hashes; full stable table and full next prompt; local links; diff. No mathematical validity inferred from packaging checks.')
out.write_text('\n'.join(lines)+'\n',encoding='utf-8')
print(lines[-1])
