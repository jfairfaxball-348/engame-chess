"""Record an honest blocked geometric attempt; no theorem/ledger promotion."""
import json,re
from pathlib import Path
r=Path(__file__).resolve().parents[3]
def read(p):return (r/p).read_text(encoding='utf-8')
def write(p,t):(r/p).write_text(t,encoding='utf-8',newline='\n')
def append(p,t):write(p,read(p)+'\n'+t+'\n')
d=json.loads(read('sessions/evidence/S086/selected-policy.json'))
assert d['result']['plies']==109 and d['replayed_legal_edges']==109 and d['failure'] is None
delta='S086 made no new mathematical progress: the global sub100 geometric proof remains open after budget, amortisation, box-shrink and no-wait attacks; a single109-ply clock-free model trajectory defeats the tested policy only.46 frozen bundles unchanged; KRK NOT CLOSED.'
prompt='''# NEXT SESSION — S087: New safe nonstalemating KRK geometric strategy

Owner2026-10-21: continue until KRK closure; stop before KQK. This direction
persists, with no inferred pause or new approval gate. Fetch ALL heads/reconcile
unmerged work/latest main; commit/push branch, ordinary main merge/push and exact
remote identity comparison.46 frozen bundles remain, no source/record rewrites.

S086 FAILED TO CLOSE the principal global geometric claim EC-C050 (PROPOSED,
not rejected and not LOCAL_VERIFIED). Read its complete attempt, adversarial
audit and exact selected-policy diagnostic. Existing wall438/arrival442/443
remain the certified global ceilings. The95 wall route is SUFFICIENT for strong
entry clock0 coverage via B+4<=99 and EC-T0046, not necessary for every solution.
Weak B+5=100 at B95 does not satisfy the strict<100 fresh lift.

Do NOT recycle failed routes as a proof. Scalar envelope arithmetic is not a
new chess bound. Global pursuit credit lacks actual successor file/orientation
relations. A protected box can stalemate (frozen Kf6/Ra7, Kh8, Rg7). Removing
waits permits the frozen Kb2/Rh3,Kc4 four-ply chase cycle. One disclosed local
coordinate policy took109 clock-free plies from Ka1/Rh2,Kb3 under an immediate
low/away/interior selector; all109 edges replayed in SAME ray model. This is
not a class/value search, independent/Lean certificate, RAW admitted history
after draw thresholds, exact distance or counterexample to a better95 strategy.
No compatible initial history is supplied by that board trajectory.

Exact next proof step: specify a genuine geometric phase with a closed invariant
and numeric global potential. A box/confinement candidate must offer an actual
legal shrink OR paid king approach OR immediate mate, retain EVERY defensive
reply, protect the rook, prevent nonchecking one-square stalemate traps, account
for blocked rook rays and weak crossings, and prove phase cost+Phi(child)<=Phi(root).
Coordinate/frame changes need their proved kernel interfaces, not generic full
history symmetry or free orientation reset. Alternatively prove another actual
global strong-arrival N<100 strategy. Choose one exact principal statement and
carry its all-branch proof, not another generic bookkeeping/strategy-equivalence
detour. A classical numeric maximum cannot be assumed without kernel proof.

Paper and separate adversarial audit BEFORE new Lean. No promotion until all
geometry/cost/legality/turn/nonempty/terminal branches close. Additive one-main-
theorem modules/all AxiomCheck entries, new own published-source clean Gate F
and separate Gate Z as required. Native official pinned4.35.0/inherited environment;
full logs/commands/exits/times/UTC, source/import/executable hashes, clean identity
and failures retained. No deps/shims/TLS/checksum change or fake hosted CI result.

Complete low-clock arbitrary-history outcome characterisation, full FIDE rights/
key/current-and-intended-claim/adjudication correspondence and exact global WDL/
DTZ conventions/optimality remain additional closure obligations. See current
live checklist in docs/KRK_COMPLETION.md. Termination, actual holding/winning
semantics, high-clock tests and fresh73 walls do not close KRK. No oracle/
tablebase/exhaustive class proof or stored per-position certificates. Selected
local counterexample diagnostics only, explicitly scoped. Full stable progress
table/immediate mathematical delta/full next prompt and honest session closeout;
publish/merge and compare remote main. Stop before KQK.
'''
write('NEXT_SESSION.md',prompt)
progress=read('docs/SESSION_PROGRESS.md').replace('through S085','through S086')
progress=re.sub(r'Session change: [^\n]+','Session change: '+delta,progress);write('docs/SESSION_PROGRESS.md',progress)
table='| Endgames / target |'+progress.split('| Endgames / target |',1)[1].split('\n\n',1)[0]
candidate='| EC-C050 | Global all-defence wall budget<=95 or equivalent sub100 strong-arrival strategy | PROPOSED; S086 geometric proof blocked, NOT rejected | [Attempt](../proofs/EC-C050_KRK_GLOBAL_GEOMETRY_ATTACK.md), [adversarial audit](../audits/EC-C050_KRK_GLOBAL_GEOMETRY_PAPER.md) | Scalar and amortised accounting incomplete; naive box/no-wait rules fail frozen controls; one109-ply CLOCK-FREE ray-model trajectory defeats tested coordinate policy only. No new Lean/Gate F/freeze or class outcome.46 frozen bundles unchanged. |'
append('research/CANDIDATES.md',candidate)
write('research/CANDIDATES.md',read('research/CANDIDATES.md').replace('Possible future IDs `EC-C050` onwards','Possible future IDs `EC-C051` onwards'))
checklist='''## Live closure audit after S086 — KRK NOT CLOSED

Owner's continue-until-closure direction persists. No publication/merge changes
the following proof boundary;46 bundles are not46 solved material classes.

| KRK obligation | Actual evidence | Remaining |
|---|---|---|
| Dead/live and clock-free forcing | Frozen kernel classification; global nonoptimal442/443 ceilings | Faster geometry if needed for clock-safe coverage |
| All-branch RAW termination | EC-T0042, all turns/flags/legal moves,150-h horizon | Full FIDE correspondence remains separate |
| Actual holding and winning strategies | EC-T0043/0045, independent legal policies, all move/claim branches, finite cap | Evaluate complete geometric/history outcome domain |
| Strong nonloss and high-clock tests | EC-T0044, all-history strong holding, weak h>=99/strong h>=98 criteria, optimal1 on those wins | Lower-clock arbitrary histories |
| Clock-zero incoming history | EC-T0046: supplied N<100 lift with no incoming count premises; framed73 wall family | Supplied global sub100 geometry is NOT proved |
| Complete all-history outcome formula | OPEN; generic F/policy equivalence does not evaluate it | Necessary and sufficient coverage of every admissible KRK input |
| Full FIDE model correspondence | OPEN: rights, normalized key, claims, adjudication/history bridges | Exact board/correct-claim model fidelity |
| Exact global distances/WDL-DTZ | OPEN; local1 and upper bounds only | Pinned conventions, minimax optimality and full covered-domain comparison |

S086's95 sufficient route is unproved, not falsified. The tested concrete
coordinate policy has a109-ply clock-free model line; naive protected-box shrink
stalemates, and naive no-wait king chase cycles. The precise next obligation is
an all-reply safe nonstalemating geometric phase with a closed global cost/potential
inequality. No fresh theorem was certified in S086. Stop before KQK.

'''
completion=read('docs/KRK_COMPLETION.md');anchor='## Evidence and completion standard'
assert anchor in completion;completion=completion.replace(anchor,checklist+anchor,1)
write('docs/KRK_COMPLETION.md',completion+'\n'+delta+' [Attempt](../proofs/EC-C050_KRK_GLOBAL_GEOMETRY_ATTACK.md).\n')
append('docs/ROADMAP.md',delta+' Direct next obligation: safe nonstalemating global geometric progress; see the live closure checklist. The continue instruction persists, no KQK.')
readme=read('README.md').replace('**After S085.**','**After S086.**')
write('README.md',readme+'\n'+delta+' [Live closure audit](docs/KRK_COMPLETION.md).\n')
write('sessions/S086_KRK_GLOBAL_GEOMETRY.md',f'''# S086 — Direct global KRK geometric attack remains open

2026-10-21, base mainc13324f4e34217dc51c1a755d02cb37519770902. All heads
fetched/no unmerged work; S085 exact local/main/remote branch identities matched.
Branch session/s086-krk-global-geometry. Owner's continue-until-closure direction
persists; no inferred pause, KQK, outreach or unrelated prerequisite work.

Principal EC-C050 global wall<=95/sub100 arrival proof NOT CLOSED, remains
PROPOSED. [Full attempt](../proofs/EC-C050_KRK_GLOBAL_GEOMETRY_ATTACK.md),
[separate same-agent audit](../audits/EC-C050_KRK_GLOBAL_GEOMETRY_PAPER.md).
No95 theorem was falsified or promoted. Actual attempts: scalar phase envelope
misses target; global file-progress amortisation lacks an actual successor
relation; protected-box shrink hits frozen Rg7 stalemate; dropping waits permits
frozen four-ply king-chase cycle. Exact missing all-reply phase/Phi inequality
recorded. A claim of complete KRK outcomes would be unsupported.

ONE selected disclosed CLOCK-FREE ordinary coordinate-policy trajectory from
White Ka1/Rh2 versus Black Kb3 took109 plies to model mate (7 waits,6 normalizes,
31 king-file chases,5 catch-ups,6 checks). All109 edges replayed in the SAME ray
generator; no class graph, game-value search, tablebase, engine or exhaustive
entrypoint called. Full boards/moves/source hashes/commands/exit0/timing/UTC
retained in [evidence](evidence/S086/README.md). This is neither independent/Lean
verification, a full initial-history witness, an admitted RAW trace through
draw thresholds, an optimal distance nor a counterexample to a better95 strategy.

No new mathematical theorem, Lean source/build, Gate F/Z, ledger row or freeze.
Prior46 frozen bundles unchanged. Relevant ledger/structure/preservation/diagnostic-
record/link/table/full prompt/diff checks in evidence/S086/checks.log are NOT
mathematical results. Full low-clock/arbitrary-history outcomes, full FIDE and
global exact WDL/DTZ remain OPEN; current live checklist in KRK_COMPLETION.
Publication recorded by Git branch commit/push, ordinary main merge/push and
exact remote comparison. S087 retains the explicit new geometric phase obligation.

{table}

Session change: {delta}

## Full installed next prompt

{prompt}''')
append('sessions/SESSION_LEDGER.md','| S086 | 2026-10-21 | Direct global KRK geometry (blocked paper attack) | EC-C050 PROPOSED: four routes do not close95; single109-ply selected CLOCK-FREE policy diagnostic only. [Closeout](S086_KRK_GLOBAL_GEOMETRY.md). Full live closure audit and exact next geometry obligation retained | None —46 bundles unchanged, KRK NOT CLOSED |')
print(delta)
