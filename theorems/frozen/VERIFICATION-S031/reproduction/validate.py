from pathlib import Path
import subprocess,hashlib,json,re,csv,collections
root=Path('/workspace/engame-chess');base=root/'theorems/frozen/VERIFICATION-S031'
anchor='07ff6c0c459562870a6468b383872e8882385421'
def git(*args):return subprocess.check_output(['git',*args],cwd=root)
protected=[p for p in git('ls-tree','-r','--name-only',anchor).decode().splitlines() if p.startswith(('formal/','theorems/frozen/','proofs/','audits/','sessions/evidence/'))]
for p in protected:assert (root/p).read_bytes()==git('show',anchor+':'+p),p
old=git('show',anchor+':theorems/LEDGER.csv')
assert (root/'theorems/LEDGER.csv').read_bytes().startswith(old)
(base/'preservation.log').write_text(f'{len(protected)} prior Lean/build configuration, frozen artifact, proof, audit and Gate F evidence files byte-identical to base main {anchor}.\nOriginal eleven-row ledger bytes retained exactly as a prefix.\nNo existing Lean or Python source changed.\n')
bundles=json.loads((base/'bundle-map.json').read_text());names=[];owned=[]
rows=list(csv.DictReader((root/'theorems/LEDGER.csv').open()))
assert len(rows)==19
checks=[]
for b in bundles:
 manifest=root/f"theorems/frozen/{b['id']}/v1.md";text=manifest.read_text()
 summary=json.loads((base/b['session']/'summary.json').read_text())
 assert summary['proof_source'] in text
 assert summary['build_exit']==summary['axiom_statement_exit']==summary['forbidden_matches']==0
 assert summary['lake_absent_before_build']
 source=summary['proof_source']
 inv={p:h for h,p in (line.split('  ',1) for line in (base/b['session']/'source-sha256.txt').read_text().splitlines())}
 for m in b['modules']:
  path='formal/EndgameChess/Rules/KRKForcing/'+m+'.lean';owned.append(path)
  assert inv[path] in text
  assert inv[path]==hashlib.sha256(git('show',source+':'+path)).hexdigest()
  ns=['EndgameChess.Rules.'+n for n in re.findall(r'^theorem (\w+)',(root/path).read_text(),re.M)]
  for n in ns:
   assert re.search(r'^@?'+re.escape(n)+r' :',text,re.M),n
   assert "'"+n+"' depends on axioms:" in text or "'"+n+"' does not depend on any axioms" in text
  names+=ns
 row=next(r for r in rows if r['theorem_id']==b['id'])
 assert row['proof_commit_sha']==source
 assert row['lean_declaration']=='EndgameChess.Rules.'+b['rep']
 assert row['verified_utc']==summary['verified_utc']
 checks.append(f"{b['id']}: source/module hashes, exact statement+axiom coverage and ledger identity pass")
assert len(names)==len(set(names))==62
assert len(owned)==len(set(owned))==22
for session in ['S028','S029','S030']:
 log=(base/session/'axioms-statements.log').read_bytes()
 assert log==(root/f'sessions/evidence/{session}/clean-axioms.log').read_bytes(),session
 checks.append(session+': fresh statement/axiom output byte-identical to exact-source Gate F report (new run, not reused)')
progress=(root/'docs/SESSION_PROGRESS.md').read_text()
table=progress[progress.index('| Endgames / target'):progress.index('\n\nPiece counts')]
close=(root/'sessions/S031_FREEZE_KRK_FORCING.md').read_text()
assert table in close
assert (root/'NEXT_SESSION.md').read_text().rstrip() in close
expected=['K vs K','K+B vs K','K+N vs K','K+R vs K','K+Q vs K','K+P vs K','All four-piece endgames','All five-piece endgames','All six-piece endgames','All seven-piece endgames','**Full Syzygy parity (through seven pieces)**']
actual=[l.split('|')[1].strip() for l in table.splitlines()[2:] if l.startswith('|')]
assert actual==expected,actual
paths=[root/'README.md',root/'docs/ROADMAP.md',root/'docs/SESSION_PROGRESS.md',root/'research/CANDIDATES.md',root/'theorems/README.md',root/'sessions/S031_FREEZE_KRK_FORCING.md',base/'README.md']+[root/f"theorems/frozen/{b['id']}/v1.md" for b in bundles]
for path in paths:
 for link in re.findall(r'\[[^\]]+\]\(([^)]+)\)',path.read_text()):
  if '://' in link:continue
  target=link.split('#')[0]
  assert (path.parent/target).exists(),(path,link)
checks+=['62 public declarations partitioned once; all 22 new complete modules assigned once.','Complete stable progress table and full installed S032 prompt copied exactly.','All inspected local Markdown links resolve.','All 19 ledger records have manifests; prior records unchanged.']
(base/'validation.log').write_text('\n'.join(checks)+'\n')
print('\n'.join(checks))
