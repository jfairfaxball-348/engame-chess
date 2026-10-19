import sys, subprocess, pathlib, os, time, hashlib, json, re, datetime
session, sha = sys.argv[1:]
root = pathlib.Path('/workspace/engame-chess')
out = root / 'theorems/frozen/VERIFICATION-S031' / session
out.mkdir(parents=True, exist_ok=False)
clone = pathlib.Path('/workspace/work/s031') / (session + '-gate-z' + os.environ.get('S031_CLONE_SUFFIX',''))
env = os.environ.copy()
env['ELAN_HOME'] = '/workspace/.tools/elan'
env['PATH'] = env['ELAN_HOME'] + '/bin:' + env['PATH']
def run(args, cwd, logfile):
    start = time.monotonic()
    with (out/logfile).open('w') as f:
        p = subprocess.run(args, cwd=cwd, env=env, stdout=f, stderr=subprocess.STDOUT)
    assert p.returncode == 0, (args, p.returncode, logfile)
    return round(time.monotonic()-start, 3)
run(['git','clone','https://github.com/jfairfaxball-348/engame-chess.git',str(clone)],root,'clone.log')
run(['git','checkout','--detach',sha],clone,'checkout.log')
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=clone,text=True).strip() == sha
assert not (clone/'formal/.lake').exists()
(out/'pre-build.log').write_text(f'Fresh GitHub clone: {clone}\nHEAD: {sha}\nformal/.lake absent before lake build: true\n')
formal = clone/'formal'
run(['bash','-c','lean --version; lake --version; cat lean-toolchain lakefile.toml lake-manifest.json'],formal,'toolchain.log')
seconds = run(['lake','build'],formal,'lake-build.log')
(out/'build-result.json').write_text(json.dumps({'exit':0,'seconds':seconds})+'\n')
run(['lake','env','lean','AxiomCheck.lean'],formal,'axioms-statements.log')
log = (out/'axioms-statements.log').read_text()
assert 'sorryAx' not in log and 'Lean.ofReduceBool' not in log
axioms = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log)
free = re.findall(r"'([^']+)' does not depend on any axioms",log)
allowed = {'propext','Classical.choice','Quot.sound'}
assert all(set(a.split(', ')) <= allowed for _, a in axioms)
source = (formal/'AxiomCheck.lean').read_text().split('-- '+session+':',1)[1]
source = source.split('-- S0',1)[0]
names = re.findall(r'^#check @([^\s]+)',source,re.M)
reports = dict(axioms)
reports.update({name:'' for name in free})
assert len(names) == {'S028':15,'S029':23,'S030':24}[session]
for name in names:
    assert name in reports
    assert re.search(r'^@?'+re.escape(name)+r' :',log,re.M), name
(out/'declarations.txt').write_text('\n'.join(names)+'\n')
files = [p for p in clone.rglob('*.lean') if '.lake' not in p.parts and '.git' not in p.parts]
files += [formal/'lean-toolchain',formal/'lakefile.toml',formal/'lake-manifest.json']
inventory=[]
for p in sorted(files):
    relative=p.relative_to(clone)
    if str(relative) not in {'formal/AxiomCheck.lean','formal/EndgameChess.lean'}:
        assert (root/relative).read_bytes() == p.read_bytes(), relative
    inventory.append(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+str(relative))
(out/'source-sha256.txt').write_text('\n'.join(inventory)+'\n')
newfiles=[line.split('  ',1)[1] for line in (root/f'sessions/evidence/{session}/source-sha256.txt').read_text().splitlines()]
hits=[]
for path in newfiles:
    for n,line in enumerate((clone/path).read_text().splitlines(),1):
        if re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by|extern)\b',line): hits.append(f'{path}:{n}:{line}')
assert not hits, hits
(out/'forbidden-tokens.log').write_text('Pattern: \\b(sorry|admit|axiom|unsafe|native_decide|implemented_by|extern)\\b\nNew modules scanned:\n'+'\n'.join(newfiles)+'\nMatches: 0\n')
counts={}
for _,a in axioms: counts[a]=counts.get(a,0)+1
summary={'proof_source':sha,'verified_utc':datetime.datetime.now(datetime.timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ'),'build_seconds':seconds,'build_exit':0,'axiom_statement_exit':0,'total_axiom_reports':len(axioms)+len(free),'axiom_counts':counts,'axiom_free':len(free),'bundle_declarations':len(names),'fresh_clone':str(clone),'lake_absent_before_build':True,'source_files_hashed':len(files),'new_modules_scanned':len(newfiles),'forbidden_matches':0,'hosted_ci':'unobserved'}
(out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary),flush=True)
