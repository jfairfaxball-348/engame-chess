"""Record the direct small-box attack honestly; no new Lean or ledger row."""
from pathlib import Path
import subprocess
r=Path(__file__).resolve().parents[3]
def read(p):
    return subprocess.check_output(['git','show','e76dc645e8e1cd1d71dab9761e829e1704f28990:'+p],cwd=r).decode('utf-8')
def write(p,t):
    (r/p).parent.mkdir(parents=True,exist_ok=True)
    (r/p).write_text(t,encoding='utf-8',newline='\n')
progress=read('docs/SESSION_PROGRESS.md').replace('through S088.','through S089.')
progress=progress.replace('normalized guarded large-box phase frozen |','normalized guarded large-box phase frozen; guarded1x1 finish<=7 plies on paper |')
start=progress.index('Session change:');end=progress.index('\n\n',start)
delta='Session change: S089 closes the guarded1x1 corner finish within7 plies ON PAPER and audits both replies; a selected8-ply cycle defeats the check-and-restore repair. A sufficiently short full <=4x4 finish, arbitrary entry and global sub100 remain OPEN. No new Lean/Gate F/Z or ledger row;47 bundles unchanged; KRK NOT CLOSED.'
progress=progress[:start]+delta+progress[end:]
write('docs/SESSION_PROGRESS.md',progress)
road=read('docs/KRK_COMPLETION.md')
note='''## S089 direct small-box frontier — KRK NOT CLOSED

[Small-box attempt](../proofs/KRK_SMALL_BOX_S089.md) and
[separate same-agent audit](../audits/KRK_SMALL_BOX_S089_PAPER.md): a constructive
guarded1x1 corner finish has a PAPER7-ply cap, every legal weak reply included.
It temporarily reopens the box, avoiding the known stalemate trap. It is NOT
Lean verified/frozen. A selected8-ply legal cycle refutes a check-and-restore
repair for the wider small-box phase. The old frozen wall theorem already supplies a finite292 ceiling here; a sufficiently short guarded <=4x4 finish F, costed
arbitrary entry E, the necessary phase transports and integrated sub100 bound
remain unproved.47 frozen bundles, all earlier sources/records unchanged.

'''
road=road.replace('## S088 verification update',note+'## S088 verification update',1)
write('docs/KRK_COMPLETION.md',road)
candidate=read('research/CANDIDATES.md')
candidate=candidate.replace('PROPOSED; S086 geometric proof blocked, NOT rejected','PROPOSED; global proof open through S089, NOT rejected')
candidate=candidate.replace('Possible future IDs `EC-C051` onwards','Possible future IDs `EC-C052` onwards')
candidate+='''

S089 EC-C050 continuation: [small-box paper](../proofs/KRK_SMALL_BOX_S089.md)
and [separate same-agent audit](../audits/KRK_SMALL_BOX_S089_PAPER.md) close ONLY
the guarded1x1 terminal case within7 plies on paper. No full <=4x4 cap; a selected
8-ply cycle rejects a check-and-restore repair. No new Lean/Gate F/Z or ledger
row.47 bundles frozen after S088; global sub100 and KRK closure remain open.
'''
write('research/CANDIDATES.md',candidate)
prompt='''# NEXT SESSION — S090: Finish the actual guarded small-box mating strategy

Owner2026-10-21: continue consecutive KRK sessions until closure; no inferred
pause/new approval gate; stop before KQK. Fetch ALL heads/reconcile unmerged
work/latest main; commit/push branch, ordinary main merge/push and exact remote
identity comparison.47 frozen bundles; preserve all frozen sources/records.

Principal EC-C050 remains PROPOSED/open. Read S089 full small-box paper and
separate audit, selected corner branches and check-and-restore cycle. Positive
PAPER result: guarded1x1 S=f6,R=g7,W=h8 has all-reply clock-free mate<=7:
Ra7 Kg8, Rb7 [Kf8 Rb8# OR Kh8 Kg6 Kg8 Rb8#]. All reply completeness/mates
are proved on paper and checked locally; NOT Lean verified/Gate F/Z/frozen.
No compatible full initial history is inferred. Do not promote this to the
whole guarded <=4x4 domain or stop at formalising only this terminal example.

New failed repair: S=c3,R=d4,W=f5; Kd3 Ke5 Re4 Kd5 Rd4 Ke5 Kc3 Kf5 is a
selected legal8-ply board/turn cycle, independently replayed in a direct move
checker. It rejects that check-and-restore rule and any strict board-only
potential along it; not a global mate lower bound or admitted RAW loop.
Also retain EC-T0047's16-ply width4 escort cycle and the older protected-corner
stalemate/no-wait chase controls. Quiet shrink, occupied/adjacent king steps
and one-file checks still require genuine legal alternatives.

Exact next obligation: a sufficiently SHORT all-defence guarded <=4x4 mating policy with
DERIVED uniform ply cap F fitting the combined clock-safe budget. The frozen wall theorem already proves a finite292 ceiling for these inputs; finite mating is settled. Normal input S=(a-1,b-1),R=(a,b),W NE,3<=a,b<=6,
strong turn, both colours/all flags; signed/axis variants need actual proved
transport. Every nonterminal weak node needs a legal witness and every reply
retained, rook safety, blocked rays, terminal mate/stalemate and paid tempos.
Specify a closed invariant and numeric phase-cost/potential inequality; a named
room/critical-distance measure alone is not a proof. Integrate the paper7
terminal case into that WHOLE proof. No unrelated generic strategy-equivalence
or count lemma in place of the missing geometric phase.

EC-T0047's actual FORMAL normalized NE widths5/6 contraction<=8 plies/cost
inequalities and fixed16-ply cycle are frozen at own source
84161c2650b902e98f37252532a706ec50f40ed4. Own S087 Gate F and separate S088
Gate Z each passed214 jobs/complete395 permitted axiom/type reports. The paper
<=32 repeated/reflected/axis result is SMALL-BOX ENTRY ONLY and is NOT a frozen
declaration. Arbitrary guarded entry E, all needed transports and an integrated
bound such as E+32+F<=95 remain separate actual proof obligations. Existing
442/443 remain the only global certified arrival ceilings. Strong wall B<=95
would give B+4<=99 for fresh clock0 lifting; weak B+5=100 at B95 is NOT N<100.

Complete arbitrary-clock/incoming-history outcomes, full FIDE rights/key/current-
and-intended-claim/adjudication correspondence, exact global WDL/DTZ conventions/
optimality remain OPEN. No material-class completion from theorem counts,
partial upper bounds, local diagnostics or semantic equivalences.

Standalone paper/separate adversarial audit BEFORE Lean; additive one-main-
theorem modules/all AxiomCheck entries; own published-source NEW clean Gate F
then SEPARATE NEW Gate Z. Official native pinned4.35.0/inherited environment;
full logs/commands/exits/times/UTC, source/import/executable hashes, clean identity
and failures retained. No deps/shims/TLS/checksum change, proof escapes, invented
hosted CI success, tablebases/oracles/exhaustive class proof or stored position
value certificates. Selected local diagnostics only, explicitly scoped. Full
stable progress table/immediate delta/full next prompt/honest closeout; publish/
merge/check remote main. Continue toward KRK closure; KQK remains unexecuted.
'''
write('NEXT_SESSION.md',prompt)
table='| Endgames / target |'+progress.split('| Endgames / target |',1)[1].split('\n\n',1)[0]
close=f'''# S089 — Small-box finish: terminal case closed on paper, whole phase open

2026-10-21. Base main e76dc645e8e1cd1d71dab9761e829e1704f28990, clean and
equal to origin/main and prior session branch after fetch; no unmerged remote
heads. Branch session/s089-krk-small-box. Owner's continue-until-closure direction
persists, no KQK or inferred pause.

[Paper](../proofs/KRK_SMALL_BOX_S089.md),
[separate same-agent paper audit](../audits/KRK_SMALL_BOX_S089_PAPER.md).
The guarded1x1 trap has a derived7-ply PAPER finish, with both5/7-ply branches
and every actual weak move accounted for. It deliberately reopens the box before
mate. It is not Lean checked/frozen or a complete <=4x4 result.

A different selected8-ply check-and-restore cycle from Kc3/Rd4,Kf5 rejects that
repair. Quiet shrink can expose the rook; king approach may be blocked/adjacent;
one-file opposed checks may be capturable. None of these gives a full-domain
sufficiently short cap F, entry E or integrated global sub100. The old frozen wall theorem already gives this normalized domain a finite292 ceiling; that existence result is settled. EC-C050 remains PROPOSED/open.

Observed [selected diagnostic](evidence/S089/small-box.json) uses only local
ordinary move generation at TWO disclosed roots. All corner weak replies for
<=7 plies,9 distinct edges, both mates; and8 prescribed cycle edges checked by
an independently written direct KRK edge validator. It never calls the imported
module's class-enumeration entrypoint. No oracle, game values, class proof,
position-value certificates or full initial RAW-history witness. Complete
command/output/exit/time/UTC/source hashes retained in evidence/S089.

No new Lean, Gate F/Z or ledger change;47 frozen bundles remain. All existing
formal sources/configs/runners/frozen manifests and ledger unchanged. No fresh
Lean check required for unchanged sources; observed prior Gate F/Z remain exact.
S089 structural/preservation checks and local diagnostics add no class claim.
Audit is same-agent, not independent external review; hosted CI unobserved.

Everything is committed/pushed/ordinarily merged to main; final remote identities
are compared after publication. The next session carries the WHOLE small-box
obligation with this terminal case and failed rule, rather than replacing it
with an easier generic prerequisite. KRK NOT CLOSED.

## Required progress table

{table}

{delta}

## Full installed next-session prompt

```text
{prompt}```
'''
write('sessions/S089_KRK_SMALL_BOX.md',close)
write('sessions/evidence/S089/README.md','''# S089 local small-box diagnostics

Two disclosed clock-free roots only. Guarded1x1 policy retains every weak reply
through5/7-ply mates (9 distinct tree edges). Separate8-ply check-and-restore
cycle returns its root. All edges independently replayed by direct geometry.
These supplement the paper and are not universal/class/RAW certificates.
No new Lean or freeze. Full output/command/exit/time/UTC/source hashes retained.
''')
print(delta)
