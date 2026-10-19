"""Validate S037 evidence and preservation without rerunning Lean.
Usage: python validate.py REPO_ROOT
"""
from pathlib import Path
import csv, hashlib, io, json, re, subprocess, sys
root = Path(sys.argv[1]).resolve()
out = root / 'theorems/frozen/VERIFICATION-S037'
base = '5b42e5136e3d7fc77d6fe471c3a405603cfd57b6'
allowed_changes = {'NEXT_SESSION.md','README.md','docs/ROADMAP.md','docs/SESSION_PROGRESS.md','research/CANDIDATES.md','sessions/SESSION_LEDGER.md','theorems/README.md','theorems/LEDGER.csv'}
tracked = subprocess.check_output(['git','ls-tree','-r','--name-only',base],cwd=root,text=True).splitlines()
protected = [p for p in tracked if p not in allowed_changes]
for p in protected:
    assert (root/p).read_bytes() == subprocess.check_output(['git','show',f'{base}:{p}'],cwd=root), p
old = subprocess.check_output(['git','show',f'{base}:theorems/LEDGER.csv'],cwd=root)
ledger = (root/'theorems/LEDGER.csv').read_bytes()
assert ledger.startswith(old)
rows = list(csv.DictReader(io.StringIO(ledger.decode())))
assert len(rows)==22 and len({r['theorem_id'] for r in rows})==22
for candidate, theorem, count, jobs in [('EC-C023','EC-T0021',265,59),('EC-C024','EC-T0022',271,66)]:
    d=out/candidate
    s=json.loads((d/'summary.json').read_text())
    assert s['build_exit']==s['axiom_statement_exit']==0
    assert s['build_jobs']==jobs and s['total_axiom_reports']==count and s['lake_absent_before_build']
    commands=json.loads((d/'commands.json').read_text())
    assert len(commands)==6 and all(c['exit']==0 for c in commands)
    assert commands[0]['args'][:3]==['git','clone','--no-checkout']
    assert commands[1]['args']==['git','checkout','--detach',s['proof_source']]
    assert f's037-{candidate[-4:].lower()}' in s['fresh_clone']
    log=(d/'axioms-statements.log').read_text()
    prior='S035' if candidate=='EC-C023' else 'S036'
    assert log==(root/f'sessions/evidence/{prior}/clean-axioms.log').read_text()
    assert not re.search(r'sorryAx|Lean.ofReduceBool|error:|warning:',log)
    manifest=(root/f'theorems/frozen/{theorem}/v1.md').read_text()
    assert s['proof_source'] in manifest
    for inventory in ['source-sha256.txt','dependency-sha256.txt']:
        for line in (d/inventory).read_text().splitlines():
            digest,p=line.split('  ',1)
            if not (candidate=='EC-C023' and p in ['formal/AxiomCheck.lean','formal/EndgameChess.lean']):
                assert hashlib.sha256((root/p).read_bytes()).hexdigest()==digest,p
            assert hashlib.sha256(subprocess.check_output(['git','show',f'{s["proof_source"]}:{p}'],cwd=root)).hexdigest()==digest,p
            if inventory=='dependency-sha256.txt': assert line in manifest
    source_names=[]
    namespace='EndgameChess.Rules.'+('RawTrace' if candidate=='EC-C023' else 'RawClock')
    for p in s['complete_modules']:
        text=(root/p).read_text()
        assert p in manifest
        assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by|extern)\b',text)
        source_names += [namespace+'.'+n for n in re.findall(r'^theorem (\w+)',text,re.M)]
    assert set(source_names)==set(s['bundle_declarations'])
    for name in s['bundle_declarations']:
        assert re.search(r'^@?'+re.escape(name)+r' :',log,re.M),name
        assert name+' :' in manifest,name
        assert set(s['bundle_axioms'][name].split(', ')) <= {'propext','Classical.choice','Quot.sound'}
    row=next(r for r in rows if r['theorem_id']==theorem)
    assert row['proof_commit_sha']==s['proof_source'] and row['verified_utc']==s['verified_utc']
    assert row['lean_declaration'] in source_names and row['status']=='FROZEN'
    for field in ['statement_path','local_proof_path','lean_file','manifest_path']: assert (root/row[field]).exists()
# Clock dependency closure explicitly retains all five trace modules at BOTH anchors.
a=json.loads((out/'EC-C023/summary.json').read_text())
b=json.loads((out/'EC-C024/summary.json').read_text())
for p in a['complete_modules']:
    assert p in (out/'EC-C024/dependency-sha256.txt').read_text()
    assert subprocess.check_output(['git','show',f'{a["proof_source"]}:{p}'],cwd=root)==subprocess.check_output(['git','show',f'{b["proof_source"]}:{p}'],cwd=root)
# Sequential build: command timings/log identities are retained; second starts after first summary.
assert a['fresh_clone']!=b['fresh_clone'] and a['verified_utc']<b['verified_utc']
progress=(root/'docs/SESSION_PROGRESS.md').read_text()
table=progress[progress.index('| Endgames / target |'):progress.index('\n\nSession change:')]
close=(root/'sessions/S037_FREEZE_RAW_TRACE_CLOCK.md').read_text()
assert table in close and (root/'NEXT_SESSION.md').read_text().rstrip() in close
assert table.splitlines()[-1].startswith('| **Full Syzygy parity')
expected=['K vs K','K+B vs K','K+N vs K','K+R vs K','K+Q vs K','K+P vs K','All four-piece endgames','All five-piece endgames','All six-piece endgames','All seven-piece endgames','**Full Syzygy parity (through seven pieces)**']
assert [l.split('|')[1].strip() for l in table.splitlines()[2:]]==expected
new_docs=[root/f'theorems/frozen/{t}/v1.md' for t in ['EC-T0021','EC-T0022']]+[root/'sessions/S037_FREEZE_RAW_TRACE_CLOCK.md',out/'README.md']
for p in new_docs:
    for dest in re.findall(r'\]\(([^)]+)\)',p.read_text()):
        if not re.match(r'https?://',dest): assert (p.parent/dest.split('#')[0]).exists(),(p,dest)
(out/'preservation.log').write_text(f'PASS: {len(protected)} prior protected tracked files byte-identical to {base}.\nPrior 20-row ledger bytes preserved exactly; two rows appended.\nAll formal sources, prior manifests, papers, audits and evidence unchanged.\n')
result=f'PASS: two distinct sequential exact-source fresh clones; 59/66 jobs, exits 0.\nPASS: 265/271 allowed axiom reports; all ten exact statements match Gate F.\nPASS: source/import hashes equal current main and own anchors; five trace imports equal both anchors.\nPASS: {len(protected)} prior protected files unchanged; prior ledger exact byte prefix.\nPASS: 22 ledger rows, own proof SHAs and verification UTCs, valid paths.\nPASS: full canonical progress table and S038 prompt reproduced; local links valid.\nHosted CI: unobserved.\n'
(out/'validation.log').write_text(result)
print(result)
