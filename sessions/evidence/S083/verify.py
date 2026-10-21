"""Separate own-source C048 Gate Z; original complete inventories and runner."""
import json,runpy,sys
from pathlib import Path
r=Path(__file__).resolve().parents[3];sha='028364a700afb7d94d13d3b7e7a9ddce628cf5ec'
out=r/'theorems/frozen/VERIFICATION-S083'
sys.argv=[str(r/'sessions/evidence/S082/verify.py'),sha,sys.argv[1],str(out)]
runpy.run_path(sys.argv[0],run_name='__main__')
own=r/'sessions/evidence/S082/gate-f'
for p in ['source-sha256.txt','dependency-sha256.txt','declarations.txt','axioms-statements.log']:
    assert (out/p).read_text(encoding='utf-8')==(own/p).read_text(encoding='utf-8'),p
s=json.loads((out/'summary.json').read_text(encoding='utf-8'))
s.update(gate='Z',entire_own_gate_f_inventory_and_complete_runner_match=True)
(out/'summary.json').write_text(json.dumps(s,indent=2)+'\n',encoding='utf-8')
print('Gate Z observed: ENTIRE own Gate F inventories and complete runner match')
