"""Finalize an already successful build/runner after evidence-script interruption.
Never invokes a build, clone or runner. Preserves original command evidence.
Usage: python finalize.py REPO_ROOT OUTPUT_DIRECTORY NEW_CLONE_DIRECTORY EC-C023|EC-C024
"""
import collections, datetime, hashlib, json, os
from pathlib import Path
import re, sys
root,out,clone=map(lambda s:Path(s).resolve(),sys.argv[1:4])
candidate=sys.argv[4]
trace=candidate=='EC-C023'
assert candidate in ['EC-C023','EC-C024']
sha='526a298b80ef04541e518a3dcc62f861c8f51c5c' if trace else '2d2b40ddaaff2a962bb9f573e8de799b1427d5f8'
prior='S035' if trace else 'S036'
commands=json.loads((out/'commands.json').read_text())
assert len(commands)==6 and all(c['exit']==0 for c in commands)
assert commands[-2]['args']==['lake','build']
assert commands[-1]['args']==['lake','env','lean','AxiomCheck.lean']
assert not (out/'summary.json').exists()
seconds=commands[-2]['seconds'];formal=clone/'formal'
script=(root/'theorems/frozen/VERIFICATION-S037/reproduction/verify.py').read_text()
# Re-execute only pure evidence inspection/output, using existing successful logs.
exec(script[script.index("log = (out / 'axioms-statements.log').read_text()"):])
