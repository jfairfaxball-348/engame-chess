"""Validate the S034 records and preservation without rerunning Lean.
Usage: python validate.py REPO_ROOT
"""
from pathlib import Path
import csv
import hashlib
import io
import json
import re
import subprocess
import sys

root = Path(sys.argv[1]).resolve()
out = root / 'theorems/frozen/VERIFICATION-S034'
base = '7d36b8f8a94576e906ec5f50e9fc025e6df2c238'
sha = '55affd0a7a3f2e77335f4964ae4fbc1edbe19e05'
s = json.loads((out / 'summary.json').read_text())
assert s['proof_source'] == sha and s['build_exit'] == s['axiom_statement_exit'] == 0
assert s['lake_absent_before_build'] and s['build_jobs'] == 54 and s['total_axiom_reports'] == 261
commands = json.loads((out / 'commands.json').read_text())
assert len(commands) == 6 and all(c['exit'] == 0 for c in commands)
assert commands[0]['args'][0:3] == ['git', 'clone', '--no-checkout']
assert commands[1]['args'] == ['git', 'checkout', '--detach', sha]
assert 's034-gate-z' in s['fresh_clone'] and 's033-gate-f' not in s['fresh_clone']
manifest = (root / 'theorems/frozen/EC-T0020/v1.md').read_text()
log = (out / 'axioms-statements.log').read_text()
assert log == (root / 'sessions/evidence/S033/clean-axioms.log').read_text()
assert not re.search(r'sorryAx|Lean.ofReduceBool|error:|warning:', log)
for inventory in ['source-sha256.txt', 'dependency-sha256.txt']:
    for line in (out / inventory).read_text().splitlines():
        digest, p = line.split('  ', 1)
        assert hashlib.sha256((root / p).read_bytes()).hexdigest() == digest, p
        anchor = subprocess.check_output(['git', 'show', f'{sha}:{p}'], cwd=root)
        assert hashlib.sha256(anchor).hexdigest() == digest, p
        if inventory == 'dependency-sha256.txt':
            assert line in manifest, p
names = (out / 'declarations.txt').read_text().splitlines()
assert len(names) == 2 and names == s['bundle_declarations']
source_names = []
for p in s['complete_modules']:
    text = (root / p).read_text()
    assert p in manifest
    assert not re.search(r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by|extern)\b', text)
    source_names += ['EndgameChess.Rules.HistoryLayer.' + name for name in re.findall(r'^theorem (\w+)', text, re.M)]
assert set(source_names) == set(names)
for name in names:
    assert re.search(r'^@' + re.escape(name) + r' :', log, re.M), name
    assert '@' + name + ' :' in manifest
    assert s['bundle_axioms'][name] == 'propext, Classical.choice, Quot.sound'
ledger = (root / 'theorems/LEDGER.csv').read_bytes()
old = subprocess.check_output(['git', 'show', f'{base}:theorems/LEDGER.csv'], cwd=root)
assert ledger.startswith(old)
rows = list(csv.DictReader(io.StringIO(ledger.decode())))
assert len(rows) == 20 and len({r['theorem_id'] for r in rows}) == 20
row = rows[-1]
assert row['theorem_id'] == 'EC-T0020' and row['proof_commit_sha'] == sha and row['status'] == 'FROZEN'
assert row['lean_declaration'] in names and row['verified_utc'] == s['verified_utc']
for field in ['statement_path', 'local_proof_path', 'lean_file', 'manifest_path']:
    assert (root / row[field]).exists(), row[field]
allowed = {'NEXT_SESSION.md', 'README.md', 'docs/ROADMAP.md', 'docs/SESSION_PROGRESS.md', 'research/CANDIDATES.md', 'sessions/SESSION_LEDGER.md', 'theorems/README.md', 'theorems/LEDGER.csv'}
tracked = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', base], cwd=root, text=True).splitlines()
protected = [p for p in tracked if p not in allowed]
for p in protected:
    assert (root / p).read_bytes() == subprocess.check_output(['git', 'show', f'{base}:{p}'], cwd=root), p
(out / 'preservation.log').write_text(f'PASS: {len(protected)} prior tracked files byte-identical to {base}.\nAll earlier formal/proof/audit/frozen/evidence files preserved.\nPrior 19-row ledger bytes remain an exact prefix; exactly one row appended.\n')
progress = (root / 'docs/SESSION_PROGRESS.md').read_text()
table = progress[progress.index('| Endgames / target |'):progress.index('\n\nSession change:')]
close = (root / 'sessions/S034_FREEZE_RULE_LAYER_PROJECTION.md').read_text()
assert table in close and (root / 'NEXT_SESSION.md').read_text().rstrip() in close
assert table.splitlines()[-1].startswith('| **Full Syzygy parity')
expected = ['K vs K', 'K+B vs K', 'K+N vs K', 'K+R vs K', 'K+Q vs K', 'K+P vs K', 'All four-piece endgames', 'All five-piece endgames', 'All six-piece endgames', 'All seven-piece endgames', '**Full Syzygy parity (through seven pieces)**']
assert [line.split('|')[1].strip() for line in table.splitlines()[2:]] == expected
for p in [root/'theorems/frozen/EC-T0020/v1.md', root/'sessions/S034_FREEZE_RULE_LAYER_PROJECTION.md']:
    for dest in re.findall(r'\]\(([^)]+)\)', p.read_text()):
        if not re.match(r'https?://', dest):
            assert (p.parent / dest.split('#')[0]).exists(), (p, dest)
result = f'PASS: exact source/commands/new clone and 54-job Gate Z evidence.\nPASS: all 261 axiom reports allowed; both exact statements covered once.\nPASS: all three complete modules and transitive source hashes pinned.\nPASS: Gate F/Gate Z reports byte-identical; forbidden tokens zero.\nPASS: {len(protected)} protected prior tracked files unchanged; prior ledger byte prefix retained.\nPASS: exactly EC-T0020 appended; 20 rows; fields/paths valid.\nPASS: complete canonical table and S035 prompt reproduced, local links valid.\nHosted CI: unobserved.\n'
(out / 'validation.log').write_text(result)
print(result)
