"""Separate own-source Gate Z, using original complete runner and inventories."""
import json,runpy,sys
from pathlib import Path
r=Path(__file__).resolve().parents[3]
sha='d8a77d1b785da39d0a644169750283f4ade935fe'
out=r/'theorems/frozen/VERIFICATION-S079'
sys.argv=[str(r/'sessions/evidence/S078/verify.py'),sha,sys.argv[1],str(out)]
runpy.run_path(sys.argv[0],run_name='__main__')
own=r/'sessions/evidence/S078/gate-f'
for p in ['source-sha256.txt','dependency-sha256.txt','declarations.txt','axioms-statements.log']:
    assert (out/p).read_text(encoding='utf-8')==(own/p).read_text(encoding='utf-8'),p
summary=json.loads((out/'summary.json').read_text(encoding='utf-8'))
summary['gate']='Z'
summary['entire_own_gate_f_inventory_and_complete_runner_match']=True
(out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n',encoding='utf-8')
print('Gate Z observed: entire OWN Gate F inventories and complete runner match')
