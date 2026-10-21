import csv,hashlib,io,json,re,subprocess
from pathlib import Path
r=Path(__file__).resolve().parents[3];out=r/'sessions/evidence/S086/checks.log';logs=[]
def run(args):
    p=subprocess.run(args,cwd=r,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    logs.append('$ '+' '.join(args)+'\n'+p.stdout.decode('utf-8',errors='replace').replace('\r\n','\n'))
    out.write_text('\n'.join(logs),encoding='utf-8',newline='\n');assert p.returncode==0,args
run(['python','-m','unittest','discover','-s','tests','-p','test_validate_ledger.py'])
run(['python','scripts/validate_ledger.py'])
base='c13324f4e34217dc51c1a755d02cb37519770902'
files=subprocess.check_output(['git','ls-tree','-r','--name-only',base],cwd=r,text=True).splitlines()
kept=[p for p in files if p.startswith(('formal/','theorems/','scripts/'))]
batch=subprocess.run(['git','cat-file','--batch'],cwd=r,input=('\n'.join(base+':'+p for p in kept)+'\n').encode(),stdout=subprocess.PIPE,check=True)
stream=io.BytesIO(batch.stdout)
for p in kept:
    header=stream.readline().split();assert header[1]==b'blob',p
    data=stream.read(int(header[2]));assert stream.read(1)==b'\n'
    assert (r/p).read_bytes().replace(b'\r\n',b'\n')==data,p
assert len(list(csv.DictReader((r/'theorems/LEDGER.csv').open(encoding='utf-8'))))==46
d=json.loads((r/'sessions/evidence/S086/selected-policy.json').read_text(encoding='utf-8'))
assert d['result']['plies']==109 and d['replayed_legal_edges']==109 and d['failure'] is None and d['ends_in_model_mate']
assert len(d['moves'])==109 and len(d['trace'])==110
assert [x['ply'] for x in d['moves']]==list(range(1,110))
assert [x['ply'] for x in d['trace']]==list(range(110))
for p,digest in d['source_sha256'].items():
    actual=Path(p).read_bytes()
    if hashlib.sha256(actual).hexdigest()!=digest:
        relative=Path(p).relative_to(r).as_posix()
        blob=subprocess.check_output(['git','show','b1385f8495fd244d7448cbbd5372cdd1607933e0:'+relative],cwd=r)
        assert actual.replace(b'\r\n',b'\n')==blob,p
        assert digest in {hashlib.sha256(blob).hexdigest(),hashlib.sha256(blob.replace(b'\n',b'\r\n')).hexdigest()},p
        logs.append('Observed checkout-only LF/CRLF variation; original runtime hash retained and matched exact first-publication Git source variant: '+relative)
assert d['raw_history_compatibility'].startswith('NOT ASSERTED')
progress=(r/'docs/SESSION_PROGRESS.md').read_text(encoding='utf-8');table='| Endgames / target |'+progress.split('| Endgames / target |',1)[1].split('\n\n',1)[0]
close=(r/'sessions/S086_KRK_GLOBAL_GEOMETRY.md').read_text(encoding='utf-8');assert table+'\n\nSession change:' in close
assert (r/'NEXT_SESSION.md').read_text(encoding='utf-8') in close
assert 'KRK NOT CLOSED' in close and 'no new mathematical progress' in close
changed=subprocess.check_output(['git','diff','--name-only',base],cwd=r,text=True).splitlines()+subprocess.check_output(['git','ls-files','--others','--exclude-standard'],cwd=r,text=True).splitlines()
assert not any(p.startswith(('formal/','theorems/','scripts/')) for p in changed)
for p in changed:
    if not p.endswith('.md'):continue
    for target in re.findall(r'\]\(([^)]+)\)',(r/p).read_text(encoding='utf-8')):
        if re.match(r'[a-zA-Z]+:|#',target):continue
        assert ((r/p).parent/target.split('#')[0]).exists(),(p,target)
run(['git','diff','--check'])
logs.append(f'PASS: {len(kept)} prior formal/theorem/diagnostic-source files unchanged as canonical Git bytes; all46 rows/frozen records preserved, no formal/theorem edits or new Lean. Single109-edge model diagnostic record/source hashes intact; full stable table, explicit unchanged mathematical delta, complete next prompt/links/diff. Packaging and model diagnostic do not prove KRK closure or optimal95.')
out.write_text('\n'.join(logs)+'\n',encoding='utf-8',newline='\n');print(logs[-1])
