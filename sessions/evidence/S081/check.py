import csv,hashlib,io,json,re,subprocess
from pathlib import Path
r=Path(__file__).resolve().parents[3];out=r/'sessions/evidence/S081/checks.log';logs=[]
def run(args):
    p=subprocess.run(args,cwd=r,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    logs.append('$ '+' '.join(args)+'\n'+p.stdout.decode('utf-8',errors='replace'))
    out.write_text('\n'.join(logs),encoding='utf-8');assert p.returncode==0,args
run(['python','-m','unittest','discover','-s','tests','-p','test_validate_ledger.py'])
run(['python','scripts/validate_ledger.py'])
base='a5bce9bc7377a28dc786f5977af33601c9ba9207'
files=subprocess.check_output(['git','ls-tree','-r','--name-only',base],cwd=r,text=True).splitlines()
kept=[p for p in files if p.startswith('formal/') or p.startswith('theorems/frozen/') or p=='theorems/LEDGER.csv']
batch=subprocess.run(['git','cat-file','--batch'],cwd=r,input=('\n'.join(base+':'+p for p in kept)+'\n').encode(),stdout=subprocess.PIPE,check=True)
stream=io.BytesIO(batch.stdout)
for p in kept:
    header=stream.readline().split();assert header[1]==b'blob',p
    data=stream.read(int(header[2]));assert stream.read(1)==b'\n'
    current=(r/p).read_bytes().replace(b'\r\n',b'\n')
    assert current.startswith(data) if p=='theorems/LEDGER.csv' else current==data,p
rows=list(csv.DictReader((r/'theorems/LEDGER.csv').open(encoding='utf-8')));assert len(rows)==44 and rows[-1]['theorem_id']=='EC-T0044'
s=json.loads((r/'theorems/frozen/VERIFICATION-S081/summary.json').read_text(encoding='utf-8'))
assert s['gate']=='Z' and s['entire_own_gate_f_inventory_and_complete_runner_match']
manifest=(r/'theorems/frozen/EC-T0044/v1.md').read_text(encoding='utf-8');log=(r/'theorems/frozen/VERIFICATION-S081/axioms-statements.log').read_text(encoding='utf-8')
for name in s['bundle_declarations']:
    assert re.search(r'^@?'+re.escape(name)+r' :.*?(?=^\S|\Z)',log,re.M|re.S)[0].rstrip() in manifest,name
inventory=dict(line.split('  ',1)[::-1] for line in (r/'theorems/frozen/VERIFICATION-S081/source-sha256.txt').read_text(encoding='utf-8').splitlines())
for p in s['complete_modules']:assert p in manifest and inventory[p] in manifest,p
progress=(r/'docs/SESSION_PROGRESS.md').read_text(encoding='utf-8');table='| Endgames / target |'+progress.split('| Endgames / target |',1)[1].split('\n\n',1)[0]
close=(r/'sessions/S081_FREEZE_KRK_HIGH_CLOCK.md').read_text(encoding='utf-8');assert table+'\n\nSession change:' in close
assert (r/'NEXT_SESSION.md').read_text(encoding='utf-8') in close
changed=subprocess.check_output(['git','diff','--name-only',base],cwd=r,text=True).splitlines()+subprocess.check_output(['git','ls-files','--others','--exclude-standard'],cwd=r,text=True).splitlines()
for p in changed:
    if not p.endswith('.md'):continue
    for target in re.findall(r'\]\(([^)]+)\)',(r/p).read_text(encoding='utf-8')):
        if re.match(r'[a-zA-Z]+:|#',target):continue
        assert ((r/p).parent/target.split('#')[0]).exists(),(p,target)
run(['git','diff','--check'])
logs.append(f'PASS: {len(kept)} prior formal/config/frozen/ledger files preserved as canonical Git bytes (ledger adds exactly one row);44 rows; all10 exact types/11 complete module hashes in manifest; separate own-source Gate Z equality; full table/immediate delta/full next prompt, links/diff. Packaging checks add no mathematical claims.')
out.write_text('\n'.join(logs)+'\n',encoding='utf-8');print(logs[-1])
