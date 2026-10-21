"""Native Windows Gate Z; exact Git bytes, own-source inventories and complete runner.
Run from repository: python sessions/evidence/S077/verify.py NEW_CLONE_DIRECTORY
No source or toolchain modifications; inherited native ELAN_HOME and PATH.
"""
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

root = Path(__file__).resolve().parents[3]
out = root / 'theorems/frozen/VERIFICATION-S077'
clone = Path(sys.argv[1]).resolve()
sha = 'e7508e103b3515dc138ed21e2ea5d3adda255add'
assert not clone.exists()
assert not out.exists()
out.mkdir(parents=True)
commands = []

def run(args, cwd, logfile):
    start = time.monotonic()
    utc = datetime.datetime.now(datetime.timezone.utc).isoformat()
    with (out / logfile).open('wb') as stream:
        result = subprocess.run(args, cwd=cwd, stdout=stream, stderr=subprocess.STDOUT)
    commands.append(dict(args=args, cwd=str(cwd), logfile=logfile,
                         exit=result.returncode, seconds=round(time.monotonic()-start,3),
                         started_utc=utc))
    (out/'commands.json').write_text(json.dumps(commands, indent=2)+'\n', encoding='utf-8')
    assert result.returncode == 0, (args, result.returncode, logfile)
    return commands[-1]['seconds']

def git(*args):
    return subprocess.check_output(['git', *args], cwd=clone)

run(['git','-c','core.autocrlf=false','clone','--no-checkout',
     'https://github.com/jfairfaxball-348/engame-chess.git',str(clone)],root,'clone.log')
run(['git','config','core.autocrlf','false'],clone,'clone-config.log')
run(['git','checkout','--detach',sha],clone,'checkout.log')
assert git('rev-parse','HEAD').decode().strip() == sha
formal = clone/'formal'
assert not (formal/'.lake').exists()
(out/'pre-build.log').write_text(f'NEW GitHub clone: {clone}\nExact HEAD: {sha}\nformal/.lake absent before build: true\nNative Windows; inherited ELAN_HOME={os.environ.get("ELAN_HOME", "(default)")}\ncore.autocrlf=false preserves exact committed LF bytes.\n',encoding='utf-8')
lake = shutil.which('lake')
assert lake
run([lake,'env','lean','--version'],formal,'toolchain.log')
run([lake,'--version'],formal,'lake-version.log')
version = (out/'toolchain.log').read_text(encoding='utf-8')
assert 'version 4.35.0,' in version and 'eb6cafb7290e8bd5f2937522d8d804f58f02bafc' in version
run([shutil.which('elan'),'which','lean'],formal,'lean-executable.txt')
executable=Path((out/'lean-executable.txt').read_text(encoding='utf-8').strip())
(out/'lean-executable-sha256.txt').write_text(hashlib.sha256(executable.read_bytes()).hexdigest()+'  '+str(executable)+'\n',encoding='utf-8')
seconds=run([lake,'build'],formal,'lake-build.log')
run([lake,'env','lean','AxiomCheck.lean'],formal,'axioms-statements.log')
log=(out/'axioms-statements.log').read_text(encoding='utf-8')
assert not re.search(r'sorryAx|Lean.ofReduceBool|error:|warning:',log)
reports=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log)
free=re.findall(r"'([^']+)' does not depend on any axioms",log)
assert len(reports)+len(free)==354
assert all(set(re.split(r',\s*',a)) <= {'propext','Classical.choice','Quot.sound'} for _,a in reports)
own=root/'sessions/evidence/S076'
assert log == (own/'working-axioms.log').read_text(encoding='utf-8')
names=(own/'declarations.txt').read_text(encoding='utf-8').splitlines()
assert len(names)==10
for name in names:
    assert name in dict(reports) or name in free
    assert re.search(r'^@?'+re.escape(name)+r' :',log,re.M)
(out/'declarations.txt').write_text('\n'.join(names)+'\n',encoding='utf-8')
for inventory in ['source-sha256.txt','dependency-sha256.txt']:
    content=(own/inventory).read_text(encoding='utf-8')
    for line in content.splitlines():
        digest, relative=line.split('  ',1)
        assert hashlib.sha256((clone/relative).read_bytes()).hexdigest()==digest,relative
    (out/inventory).write_text(content,encoding='utf-8')
modules=json.loads((own/'summary.json').read_text(encoding='utf-8'))['complete_modules']
for relative in modules:
    assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by|extern)\b', (clone/relative).read_text(encoding='utf-8'))
identity=dict(HEAD=git('rev-parse','HEAD').decode().strip(),tree=git('rev-parse','HEAD^{tree}').decode().strip(),status=git('status','--porcelain').decode(),tracked_diff=git('diff','HEAD','--').decode())
assert identity['status']==identity['tracked_diff']==''
(out/'clean-source-identity.json').write_text(json.dumps(identity,indent=2)+'\n',encoding='utf-8')
summary=dict(proof_source=sha,verified_utc=datetime.datetime.now(datetime.timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ'),fresh_clone=str(clone),lake_absent_before_build=True,build_exit=0,build_seconds=seconds,build_jobs=int(re.search(r'Build completed successfully \((\d+) jobs\)',(out/'lake-build.log').read_text(encoding='utf-8'))[1]),axiom_statement_exit=0,total_axiom_reports=len(reports)+len(free),bundle_declarations=names,bundle_axioms={n:dict(reports).get(n,'none') for n in names},complete_modules=modules,complete_runner_matches_own_gate_f=True,entire_source_and_dependency_inventories_match_own_gate_f=True,platform='native Windows x86_64-w64-windows-gnu; official same Lean source revision',hosted_ci='unobserved')
(out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n',encoding='utf-8')
print(json.dumps(summary,indent=2))
