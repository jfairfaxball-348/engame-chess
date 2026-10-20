from pathlib import Path
import re,subprocess
base='98367d75b868596a64c76bcd672bb65ff02710b2';root=Path('.')
def git(*args):return subprocess.check_output(['git',*args],text=True)
allowed={'AGENTS.md','NEXT_SESSION.md','README.md','docs/ROADMAP.md','docs/KRK_COMPLETION.md','docs/SESSION_PROGRESS.md','sessions/SESSION_LEDGER.md','sessions/S066_KRK_ROADMAP_ADDENDUM.md','sessions/evidence/S066-roadmap/validate.py','sessions/evidence/S066-roadmap/validation.log'}
changed=set(git('diff','--name-only',base).splitlines());assert changed<=allowed,changed-allowed
for scope in ['formal','theorems','proofs','audits']:
 assert git('diff',base,'--',scope)=='',scope
old_sessions=git('ls-tree','-r','--name-only',base,'sessions').splitlines()
for p in old_sessions:
 if p=='sessions/SESSION_LEDGER.md':continue
 assert (root/p).read_bytes()==subprocess.check_output(['git','show',f'{base}:{p}']),p
for p in ['theorems/LEDGER.csv','research/CANDIDATES.md']:
 assert (root/p).read_bytes()==subprocess.check_output(['git','show',f'{base}:{p}']),p
progress=(root/'docs/SESSION_PROGRESS.md').read_text();table='\n'.join(l for l in progress.splitlines() if l.startswith('|'));assert table=='\n'.join(l for l in git('show',f'{base}:docs/SESSION_PROGRESS.md').splitlines() if l.startswith('|'))
closeout=(root/'sessions/S066_KRK_ROADMAP_ADDENDUM.md').read_text();prompt=(root/'NEXT_SESSION.md').read_text();plan=(root/'docs/KRK_COMPLETION.md').read_text()
assert table in closeout and prompt.strip() in closeout
assert 'PAUSED' in prompt and 'S067 has NOT started.' in prompt
assert 'Direct quantitative attack' in prompt and 'freeze-only' in prompt
assert all(term in plan for term in ['A — Quantitative','B — Strategy','C — Complete','D — Correct','E — Freeze'])
assert 'Prerequisite admission' in plan and 'Research is PAUSED' in (root/'AGENTS.md').read_text()
files=[p for p in allowed if p.endswith('.md')]
for p in files:
 for link in re.findall(r'\]\(([^)]+)\)',(root/p).read_text()):
  if '://' in link or link.startswith('#'):continue
  assert (root/p).parent.joinpath(link.split('#')[0]).exists(),(p,link)
print('PASS: authorised documentation changes only; all prior formal/proof/audit/frozen/ledger/candidate/session evidence unchanged.')
print('PASS: mathematical progress table byte-identical; full table and paused S067 prompt reproduced in planning addendum.')
print('PASS: direct KRK milestones, prerequisite admission, paused execution, and local links.')
print('NOT RUN: Lean builds, axiom audit, Gate Z or any S067 research; documentation-only update.')
