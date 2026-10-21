"""Separate fresh C052 Gate Z; execute only after tightened OWN Gate F passed."""
import json,runpy,sys
from pathlib import Path
r=Path(__file__).resolve().parents[3]
sha='2311abe71bc1a4eed47026feccd5ba5a0760d5bb'
own=r/'sessions/evidence/S090/gate-f93'
f=json.loads((own/'summary.json').read_text(encoding='utf-8'))
assert f['proof_source']==sha and f['build_exit']==f['axiom_statement_exit']==0
assert f['total_axiom_reports']==421 and len(f['complete_modules'])==29
out=r/'theorems/frozen/VERIFICATION-S091'
sys.argv=[str(r/'sessions/evidence/S090/verify.py'),sha,sys.argv[1],str(out)]
runpy.run_path(sys.argv[0],run_name='__main__')
for p in ['source-sha256.txt','dependency-sha256.txt','declarations.txt','axioms-statements.log']:
    assert (out/p).read_text(encoding='utf-8')==(own/p).read_text(encoding='utf-8'),p
s=json.loads((out/'summary.json').read_text(encoding='utf-8'))
assert s['fresh_clone']!=f['fresh_clone']
s.update(gate='Z',entire_own_gate_f_inventory_and_complete_runner_match=True)
(out/'summary.json').write_text(json.dumps(s,indent=2)+'\n',encoding='utf-8',newline='\n')
print('Gate Z observed: entire tightened own-source Gate F inventories and complete runner match')
