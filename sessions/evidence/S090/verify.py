"""Gate F in a NEW GitHub clone at published OWN SHA, no .lake before build.
Usage: python sessions/evidence/S090/verify.py OWN_SHA NEW_CLONE NEW_OUTPUT
"""
import datetime,hashlib,json,os,re,shutil,subprocess,sys,time
from pathlib import Path
sys.stdout.reconfigure(encoding='utf-8')
root=Path(__file__).resolve().parents[3]
sha=sys.argv[1]; clone=Path(sys.argv[2]).resolve(); out=Path(sys.argv[3]).resolve()
assert re.fullmatch('[0-9a-f]{40}',sha) and not clone.exists() and not out.exists()
out.mkdir(parents=True); commands=[]
def run(args,cwd,logfile):
    start=time.monotonic();utc=datetime.datetime.now(datetime.timezone.utc).isoformat()
    with (out/logfile).open('wb') as stream:p=subprocess.run(args,cwd=cwd,stdout=stream,stderr=subprocess.STDOUT,timeout=1200)
    commands.append(dict(args=args,cwd=str(cwd),logfile=logfile,exit=p.returncode,seconds=round(time.monotonic()-start,3),started_utc=utc))
    (out/'commands.json').write_text(json.dumps(commands,indent=2)+'\n',encoding='utf-8')
    assert p.returncode==0,(args,logfile,p.returncode)
    return commands[-1]['seconds']
run(['git','-c','core.autocrlf=false','clone','--no-checkout','https://github.com/jfairfaxball-348/engame-chess.git',str(clone)],root,'clone.log')
run(['git','config','core.autocrlf','false'],clone,'clone-config.log')
run(['git','checkout','--detach',sha],clone,'checkout.log')
def git(*args):return subprocess.check_output(['git',*args],cwd=clone)
assert git('rev-parse','HEAD').decode().strip()==sha
formal=clone/'formal';assert not (formal/'.lake').exists()
(out/'pre-build.log').write_text(f'NEW GitHub clone: {clone}\nHEAD: {sha}\nformal/.lake absent before full build: true\nNative Windows; official installed toolchain; inherited ELAN_HOME={os.environ.get("ELAN_HOME","(default)")}\ncore.autocrlf=false\n',encoding='utf-8')
lake=shutil.which('lake');assert lake
run([lake,'env','lean','--version'],formal,'toolchain.log')
assert 'version 4.35.0,' in (out/'toolchain.log').read_text(encoding='utf-8')
run([lake,'--version'],formal,'lake-version.log')
run([shutil.which('elan'),'which','lean'],formal,'lean-executable.txt')
executable=Path((out/'lean-executable.txt').read_text(encoding='utf-8').strip())
(out/'lean-executable-sha256.txt').write_text(hashlib.sha256(executable.read_bytes()).hexdigest()+'  '+str(executable)+'\n',encoding='utf-8')
seconds=run([lake,'build'],formal,'lake-build.log')
run([lake,'env','lean','AxiomCheck.lean'],formal,'axioms-statements.log')
log=(out/'axioms-statements.log').read_text(encoding='utf-8')
assert not re.search(r'sorryAx|Lean.ofReduceBool|error:|warning:',log)
reports=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",log)
free=re.findall(r"'([^']+)' does not depend on any axioms",log)
assert len(reports)+len(free)==419
assert all(set(re.split(r',\s*',a)) <= {'propext','Classical.choice','Quot.sound'} for _,a in reports)
assert log==(root/'sessions/evidence/S090/working-035.log').read_text(encoding='utf-8')
names=['EndgameChess.Rules.KRKCentral.arrival99', 'EndgameChess.Rules.KRKCentral.back_bound', 'EndgameChess.Rules.KRKCentral.back_even_bound', 'EndgameChess.Rules.KRKCentral.central_bound', 'EndgameChess.Rules.KRKCentral.column_bound', 'EndgameChess.Rules.KRKCentral.column_wall_bound', 'EndgameChess.Rules.KRKCentral.exit_step_bound', 'EndgameChess.Rules.KRKCentral.fresh_arrival99', 'EndgameChess.Rules.KRKCentral.full_bound', 'EndgameChess.Rules.KRKCentral.full_cut_bound', 'EndgameChess.Rules.KRKCentral.guarded_bound', 'EndgameChess.Rules.KRKCentral.king_below_pair', 'EndgameChess.Rules.KRKCentral.pivot_bound', 'EndgameChess.Rules.KRKCentral.positive_bound', 'EndgameChess.Rules.KRKCentral.prep_bound', 'EndgameChess.Rules.KRKCentral.prep_pair', 'EndgameChess.Rules.KRKCentral.rank_two_pair', 'EndgameChess.Rules.KRKCentral.ready_bound', 'EndgameChess.Rules.KRKCentral.ready_cut_bound', 'EndgameChess.Rules.KRKCentral.restoration_bound', 'EndgameChess.Rules.KRKCentral.small_central_bound', 'EndgameChess.Rules.KRKCentral.wait_even_bound', 'EndgameChess.Rules.KRKCentral.wall95', 'EndgameChess.Rules.KRKCentral.weak100']
for name in names:
    assert name in dict(reports) or name in free
    assert re.search(r'^@?'+re.escape(name)+r' :',log,re.M)
(out/'declarations.txt').write_text('\n'.join(names)+'\n',encoding='utf-8')
modules=sorted(p.relative_to(clone).as_posix() for p in (formal/'EndgameChess/Rules/KRKCentral').glob('*.lean'))
assert len(modules)==27
for p in modules:assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by|extern)\b',(clone/p).read_text(encoding='utf-8'))
files=sorted(p for p in formal.rglob('*.lean') if '.lake' not in p.parts)+[formal/p for p in ['lean-toolchain','lakefile.toml','lake-manifest.json']]
for p in files:
    rel=p.relative_to(clone).as_posix()
    own=subprocess.check_output(['git','show',sha+':'+rel],cwd=root)
    assert p.read_bytes()==own,rel
(out/'source-sha256.txt').write_text(''.join(hashlib.sha256(p.read_bytes()).hexdigest()+'  '+p.relative_to(clone).as_posix()+'\n' for p in sorted(files)),encoding='utf-8')
closure=set()
def visit(p):
    if p in closure:return
    closure.add(p)
    for name in re.findall(r'^import\s+(EndgameChess[.\w]*)',(clone/p).read_text(encoding='utf-8'),re.M):visit('formal/'+name.replace('.','/')+'.lean')
for p in modules:visit(p)
(out/'dependency-sha256.txt').write_text(''.join(hashlib.sha256((clone/p).read_bytes()).hexdigest()+'  '+p+'\n' for p in sorted(closure)),encoding='utf-8')
identity=dict(HEAD=sha,tree=git('rev-parse','HEAD^{tree}').decode().strip(),status=git('status','--porcelain').decode(),tracked_diff=git('diff','HEAD','--').decode())
assert identity['status']==identity['tracked_diff']==''
(out/'clean-source-identity.json').write_text(json.dumps(identity,indent=2)+'\n',encoding='utf-8')
summary=dict(proof_source=sha,verified_utc=datetime.datetime.now(datetime.timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ'),fresh_clone=str(clone),lake_absent_before_build=True,build_exit=0,build_seconds=seconds,build_jobs=int(re.search(r'Build completed successfully \((\d+) jobs\)',(out/'lake-build.log').read_text(encoding='utf-8'))[1]),axiom_statement_exit=0,total_axiom_reports=len(reports)+len(free),bundle_declarations=names,bundle_axioms={n:dict(reports).get(n,'none') for n in names},complete_modules=modules,dependency_modules=len(closure),source_files_hashed=len(files),complete_runner_matches_working=True,source_matches_published_git_bytes=True,platform='official native Windows Lean4.35.0; inherited environment',hosted_ci='unobserved')
(out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n',encoding='utf-8');print(json.dumps(summary,indent=2))
