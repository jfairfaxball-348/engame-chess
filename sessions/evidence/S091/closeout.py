"""Create EC-T0048 only after the observed separate exact-source Gate Z."""
import csv,io,json
from pathlib import Path
r=Path(__file__).resolve().parents[3]
e=r/'theorems/frozen/VERIFICATION-S091'
s=json.loads((e/'summary.json').read_text(encoding='utf-8'))
assert s['gate']=='Z' and s['entire_own_gate_f_inventory_and_complete_runner_match']
assert s['proof_source']=='2311abe71bc1a4eed47026feccd5ba5a0760d5bb'
assert s['build_exit']==s['axiom_statement_exit']==0 and s['total_axiom_reports']==421
assert len(s['bundle_declarations'])==26 and len(s['complete_modules'])==29
assert not (r/'theorems/frozen/EC-T0048').exists()
identity=json.loads((e/'clean-source-identity.json').read_text(encoding='utf-8'))
assert identity['status']==identity['tracked_diff']==''
own=r/'sessions/evidence/S090/gate-f93'
for p in ['source-sha256.txt','dependency-sha256.txt','declarations.txt','axioms-statements.log']:
    assert (e/p).read_text(encoding='utf-8')==(own/p).read_text(encoding='utf-8'),p
old=(r/'theorems/LEDGER.csv').read_text(encoding='utf-8')
assert len(list(csv.DictReader(io.StringIO(old))))==47
sha=s['proof_source']
observed=f"Own published proof source `{sha}`; SEPARATE NEW GitHub clone `{s['fresh_clone']}`, .lake absent before full{s['build_jobs']}-job build exit0 in{s['build_seconds']}s. Complete421-report axiom/type runner exit0 at{s['verified_utc']}; all26 exact main declarations use only standard axioms. Entire own Gate F source/transitive/declaration inventories and full runner match. Official native Windows Lean4.35.0/inherited environment; executable/source/import hashes, commands/exits/times/UTC and clean identity retained. Hosted CI unobserved."
scope='''For either strong colour sigma, EVERY exact strong-turn kernel KRK rank wall
S.y<R.y<W.y has MateWithin sigma93, arbitrary flags and ALL actual defensive
replies. Parametric safe setup gives every exact strong-turn legal arrival97.
Weak forcing98 retains its ForceMate premise; it does not declare capturable
or stalemated weak roots winning. These are board-ply upper bounds, not optima.

On EVERY admitted RAW KRK history at clock0, both turns and colours, the strong
side's independent actual bounded winning-policy predicate holds EXACTLY when:
strong turn OR already board mate OR (safe rook AND a legal reply exists).
The safe rook predicate is distance>=2 OR king protection, as in the frozen
weak geometric classification. All opponent moves and current/intended claims
remain in the actual RAW semantics.97/98 fit the strict<100 clock0 lift with
NO incoming count/histogram premise. Strong incoming-edge compatibility is
derived from the actual initial-rooted trace, not assumed for a local sample.

The integrated proof costs every action: even/back/central pursuit, margin2
rank advance, full six-ply restoration, protected width2/3 cuts, noncircular
small-height continuation and initial simultaneous centralisation including
the final repair. Ready/full endpoints are distinct; no threatened-rook reply,
capture, empty weak node, null rook tempo or favourable defence is discarded.
Transport uses canonical noRights geometric sources, not a history symmetry.

This strengthens EC-T0041's442/443 ceilings and extends EC-T0046's partial
clock0 wall domain to the complete BOTH-turn clock0 winning criterion. Their
earlier source/manifest/ledger entries remain unchanged. It DOES NOT close
positive-clock/arbitrary-history outcomes, full FIDE correspondence, exact
minimax distances or global WDL/DTZ. KRK remains OPEN. Kernel legal-move scope
uses FIDE2023; RAW is not silently called complete FIDE board/claim semantics.
Classical geometry, no novelty claim. No tablebases, engine oracles, exhaustive
class proof or stored per-position values. Selected36 diagnostic trajectories
are supplementary error checks only. No external independent audit is claimed.
'''
manifest=f'''# EC-T0048 v1 - Uniform KRK wall93 and complete clock0 winning criterion

FROZEN (S091,2026-10-21), candidate EC-C052.
Representative: EndgameChess.Rules.KRKCentral.fresh_outcome.
Full verified proof source `{sha}`. Core Lean only; NO external packages.
Toolchain leanprover/lean4:v4.35.0; exact config bytes in source inventory.

## Exact scope and trust

{scope}
## Audits and observed verification

[Paper](../../../proofs/EC-C052_KRK_CENTRAL_WALL_95.md),
[separate same-agent paper audit](../../../audits/EC-C052_KRK_CENTRAL_WALL_PAPER.md),
[separate same-agent Lean fidelity audit](../../../audits/EC-C052_KRK_CENTRAL_WALL_LEAN.md).
The historical paper filename retains95; the exact frozen result is93/97/98
and the explicit clock0 criterion at the verified proof source. The earlier
published95-source Gate F is retained separately and is NOT a separate bundle.
Paper proof and separate audit preceded Lean; a margin3 overstatement was
replaced by the simpler audited margin2 escort before final integrated source.

{observed}

[Gate Z summary](../VERIFICATION-S091/summary.json),
[complete build](../VERIFICATION-S091/lake-build.log),
[full runner](../VERIFICATION-S091/axioms-statements.log),
[commands](../VERIFICATION-S091/commands.json),
[source inventory](../VERIFICATION-S091/source-sha256.txt),
[transitive imports](../VERIFICATION-S091/dependency-sha256.txt),
[clean identity](../VERIFICATION-S091/clean-source-identity.json).

## Immutable complete module boundary

ALL29 COMPLETE modules, shared definitions and private pivot helper are frozen
at the above SHA. Future strengthening/corrections require new modules/IDs.

```text
'''+ '\n'.join(s['complete_modules'])+'\n```\n\n## Exact new types and axioms\n\n```text\n'
runner=(e/'axioms-statements.log').read_text(encoding='utf-8')
manifest+=runner[runner.index("'EndgameChess.Rules.KRKCentral.arrival97'"):]+'\n```\n\n## Exact transitive inventory\n\n```text\n'
manifest+=(e/'dependency-sha256.txt').read_text(encoding='utf-8')+'```\n'
p=r/'theorems/frozen/EC-T0048/v1.md';p.parent.mkdir();p.write_text(manifest,encoding='utf-8',newline='\n')
row=['EC-T0048','Uniform KRK wall93 and complete clock-zero winning criterion','theorems/frozen/EC-T0048/v1.md','proofs/EC-C052_KRK_CENTRAL_WALL_95.md','formal/EndgameChess/Rules/KRKCentral/FreshOutcome.lean','EndgameChess.Rules.KRKCentral.fresh_outcome','leanprover/lean4:v4.35.0',sha,s['verified_utc'],'FIDE Laws of Chess 2023 legal-move kernel; actual RAW clock-zero history scope','theorems/frozen/EC-T0048/v1.md','FROZEN','From EC-C052. All-wall93; strong legal arrivals97 and weak forcing98. Explicit BOTH-turn actual RAW clock0 winning criterion; no incoming counts. Separate own-source Gate F/Z;29 complete modules/26 main types. Positive-clock/full FIDE/exact global WDL-DTZ remain open.']
buf=io.StringIO(newline='');csv.writer(buf,lineterminator='\n').writerow(row)
(r/'theorems/LEDGER.csv').write_text(old+buf.getvalue(),encoding='utf-8',newline='\n')
print(observed)
