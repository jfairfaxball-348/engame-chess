"""Reproduce this one Gate Z run in a NEW clone/output directory.
Usage: python verify.py REPO_ROOT OUTPUT_DIRECTORY NEW_CLONE_DIRECTORY PROOF_SOURCE_SHA
"""
import collections
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

root, out, clone = map(lambda s: Path(s).resolve(), sys.argv[1:4])
sha = sys.argv[4]
assert not clone.exists(), 'Gate Z clone must be new'
assert not (out / 'summary.json').exists(), 'Do not overwrite completed evidence'
out.mkdir(parents=True, exist_ok=True)
env = os.environ.copy()
env['ELAN_HOME'] = '/workspace/.tools/elan'
env['PATH'] = env['ELAN_HOME'] + '/bin:' + env['PATH']
commands = []

def run(args, cwd, logfile):
    start = time.monotonic()
    started_utc = datetime.datetime.now(datetime.timezone.utc).isoformat()
    with (out / logfile).open('w') as stream:
        result = subprocess.run(args, cwd=cwd, env=env, stdout=stream, stderr=subprocess.STDOUT)
    seconds = round(time.monotonic() - start, 3)
    commands.append(dict(args=args, cwd=str(cwd), logfile=logfile, exit=result.returncode, seconds=seconds, started_utc=started_utc))
    (out / 'commands.json').write_text(json.dumps(commands, indent=2) + '\n')
    assert result.returncode == 0, (args, result.returncode, logfile)
    return seconds

run(['git', 'clone', '--no-checkout', 'https://github.com/jfairfaxball-348/engame-chess.git', str(clone)], root, 'clone.log')
run(['git', 'checkout', '--detach', sha], clone, 'checkout.log')
assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=clone, text=True).strip() == sha
assert not (clone / 'formal/.lake').exists()
(out / 'pre-build.log').write_text(f'NEW GitHub clone: {clone}\nExact HEAD: {sha}\nformal/.lake absent before build: true\n')
formal = clone / 'formal'
run(['lake', 'env', 'lean', '--version'], formal, 'toolchain.log')
run(['lake', '--version'], formal, 'lake-version.log')
run(['lake','env','which','lean'], formal, 'lean-executable.txt')
executable = Path((out/'lean-executable.txt').read_text().strip()).resolve()
(out/'lean-executable-sha256.txt').write_text(hashlib.sha256(executable.read_bytes()).hexdigest() + '  ' + str(executable) + '\n')
seconds = run(['lake', 'build'], formal, 'lake-build.log')
run(['lake', 'env', 'lean', 'AxiomCheck.lean'], formal, 'axioms-statements.log')
log = (out / 'axioms-statements.log').read_text()
assert not re.search(r'sorryAx|Lean.ofReduceBool|error:|warning:', log)
reports = dict(re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log))
free = re.findall(r"'([^']+)' does not depend on any axioms", log)
assert len(reports) + len(free) == 284
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
assert all(set(a.split(', ')) <= allowed for a in reports.values())
names = ['EndgameChess.Rules.StoppedHistory.append_and_reply_lifting']
for name in names:
    assert name in reports and re.search(r'^@?' + re.escape(name) + r' :', log, re.M)
assert log == (root / 'sessions/evidence/S062/working-axioms.log').read_text()
(out / 'declarations.txt').write_text('\n'.join(names) + '\n')
new_modules = ['formal/EndgameChess/Rules/StoppedHistory/Definitions.lean', 'formal/EndgameChess/Rules/StoppedHistory/AppendLifting.lean']
pattern = r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by|extern)\b'
for relative in new_modules:
    assert not re.search(pattern, (clone / relative).read_text()), relative
(out / 'forbidden-tokens.log').write_text(f'Pattern: {pattern}\nModules:\n' + '\n'.join(new_modules) + '\nMatches: 0\n')
files = sorted(p for p in formal.rglob('*.lean') if '.lake' not in p.parts)
files += [formal / p for p in ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json']]
for p in files:
    relative = str(p.relative_to(clone))
    assert p.read_bytes() == (root / p.relative_to(clone)).read_bytes(), p
(out / 'source-sha256.txt').write_text(''.join(f'{hashlib.sha256(p.read_bytes()).hexdigest()}  {p.relative_to(clone)}\n' for p in sorted(files)))
closure = set()
def visit(relative):
    if relative in closure:
        return
    closure.add(relative)
    for name in re.findall(r'^import\s+(EndgameChess[.\w]*)', (clone / relative).read_text(), re.M):
        visit('formal/' + name.replace('.', '/') + '.lean')
for relative in new_modules:
    visit(relative)
(out / 'dependency-sha256.txt').write_text(''.join(f'{hashlib.sha256((clone / p).read_bytes()).hexdigest()}  {p}\n' for p in sorted(closure)))
counts = collections.Counter(reports.values())
jobs = int(re.search(r'Build completed successfully \((\d+) jobs\)', (out / 'lake-build.log').read_text())[1])
summary = dict(proof_source=sha, verified_utc=datetime.datetime.now(datetime.timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ'), fresh_clone=str(clone), lake_absent_before_build=True, build_exit=0, build_seconds=seconds, build_jobs=jobs, axiom_statement_exit=0, total_axiom_reports=len(reports)+len(free), axiom_counts=dict(counts), axiom_free=len(free), bundle_declarations=names, bundle_axioms={name: reports[name] for name in names}, complete_modules=new_modules, dependency_modules=len(closure), source_files_hashed=len(files), working_report_byte_identical=True, hosted_ci='unobserved')
(out / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
identity = dict(HEAD=sha, tree=subprocess.check_output(['git','rev-parse','HEAD^{tree}'],cwd=clone,text=True).strip(), tracked_diff=subprocess.check_output(['git','diff','HEAD','--'],cwd=clone,text=True), status_porcelain=subprocess.check_output(['git','status','--porcelain'],cwd=clone,text=True))
assert identity['tracked_diff'] == identity['status_porcelain'] == ''
(out / 'clean-source-identity.json').write_text(json.dumps(identity,indent=2)+'\n')
print(json.dumps(summary, indent=2))
