"""S042 preservation/evidence checks; does not rerun Lean or diagnose chess."""
import hashlib, json, re, subprocess
from pathlib import Path
root = Path(__file__).resolve().parents[3]
base = '62052f4d87c0fac3e224cb964408dd315ea60fea'
out = root / 'sessions/evidence/S042'
def git(*args):
    return subprocess.check_output(['git',*args],cwd=root)
files = git('ls-tree','-r','--name-only',base).decode().splitlines()
protected = [p for p in files if p.startswith(('proofs/','audits/','sessions/','theorems/','formal/')) and p not in ['sessions/SESSION_LEDGER.md','formal/AxiomCheck.lean','formal/EndgameChess.lean']]
for p in protected:
    assert (root/p).read_bytes() == git('show',f'{base}:{p}'), p
for p in ['formal/AxiomCheck.lean','formal/EndgameChess.lean']:
    assert (root/p).read_bytes().startswith(git('show',f'{base}:{p}')), p
prior = git('show',f'{base}:research/CANDIDATES.md').decode().split('Possible future IDs')[0]
assert (root/'research/CANDIDATES.md').read_text().startswith(prior)
(out/'preservation.log').write_text(f'{len(protected)} prior source/paper/audit/session/evidence/ledger/manifest files byte-identical to {base}.\nAggregate Lean files additive only; every prior candidate entry preserved.\n')
s = json.loads((out/'summary.json').read_text())
assert s['proof_source'] == '04bd8d03bf09056eff74c5fae1c399a841b170cb'
assert s['build_exit'] == s['axiom_statement_exit'] == 0
assert s['build_jobs'] == 71 and s['total_axiom_reports'] == 274
assert s['lake_absent_before_build']
commands=json.loads((out/'commands.json').read_text())
assert len(commands)==6 and all(c['exit']==0 for c in commands)
assert commands[0]['args'][:3]==['git','clone','--no-checkout']
assert commands[1]['args']==['git','checkout','--detach',s['proof_source']]
assert (out/'working-axioms.log').read_bytes() == (out/'axioms-statements.log').read_bytes()
assert json.loads((out/'clean-source-identity.json').read_text())['status_porcelain'] == ''
for inventory in ['source-sha256.txt','dependency-sha256.txt']:
    for line in (out/inventory).read_text().splitlines():
        sha,p = line.split('  ')
        assert hashlib.sha256((root/p).read_bytes()).hexdigest() == sha, p
assert 'commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release' in (out/'toolchain.log').read_text()
progress = (root/'docs/SESSION_PROGRESS.md').read_text()
table = '\n'.join(l for l in progress.splitlines() if l.startswith('|'))
closeout = (root/'sessions/S042_RAW_KEY_OCCURRENCES.md').read_text()
assert table in closeout
assert (root/'NEXT_SESSION.md').read_text().strip() in closeout
expected = ['K vs K','K+B vs K','K+N vs K','K+R vs K','K+Q vs K','K+P vs K','All four-piece endgames','All five-piece endgames','All six-piece endgames','All seven-piece endgames','**Full Syzygy parity (through seven pieces)**']
assert [l.split('|')[1].strip() for l in table.splitlines()[2:]] == expected
for p in ['proofs/EC-C027_RAW_KEY_OCCURRENCES.md','audits/EC-C027_RAW_KEY_OCCURRENCES_PAPER.md','audits/EC-C027_RAW_KEY_OCCURRENCES_LEAN.md','sessions/S042_RAW_KEY_OCCURRENCES.md','sessions/evidence/S042/README.md','docs/ROADMAP.md','docs/SESSION_PROGRESS.md','README.md','research/CANDIDATES.md','sessions/SESSION_LEDGER.md']:
    for link in re.findall(r'\]\(([^)]+)\)',(root/p).read_text()):
        if '://' in link or link.startswith('#'): continue
        assert (root/p).parent.joinpath(link.split('#')[0]).exists(), (p,link)
print('PASS: protected files, additive aggregates/candidates, exact-source Gate F evidence/hashes, toolchain, full progress table, full S043 prompt and local document links.')
