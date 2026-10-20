"""Finalize conditional lifting only after observed own-source Gate F."""
import json
from pathlib import Path
root=Path(__file__).resolve().parents[3];out=root/'sessions/evidence/S066';s=json.loads((out/'summary.json').read_text());sha=s['proof_source'];assert sha=='7155c3424a5e315ea758f916d939b6696e0da261' and s['build_exit']==s['axiom_statement_exit']==0
result=f"Own proof source `{sha}`; NEW GitHub clone `{s['fresh_clone']}`, .lake absent before build. Full {s['build_jobs']}-job build exit 0 ({s['build_seconds']}s); complete AxiomCheck exit 0 at {s['verified_utc']}, {s['total_axiom_reports']} allowed reports. Exact main AND helper inspected, standard-three only; entire working/clean runner and all formal bytes identical."
scope='''For EVERY admitted raw s/colour/n, clock-free MateWithin at n plus strict
clock(s.val.trace)+n<100 and count<3 on EVERY actual raw prefix through n imply
raw-layer RuleMateWithin at SAME n. New actual-step prepend helper retains exact
raw traces and depth. Induction: zero/early mate Goal; otherwise nondead/legal
successor/root bounds give ongoing, ALL intended children below100/3 exclude all
raw thresholds, child clock/count certificates descend by append bound/prepend,
strong chosen child and ALL weak replies/nonempty retained. No child-ongoing
filter. Recursive witnesses used directly, no extra tree extraction assumed.'''
limits='''Conservative SUFFICIENT all-raw-prefix certificate, not necessity or a certificate
on any general KRK history. It bounds continuations outside the chosen strategy,
including raw paths after terminals; strategy-specific repetition certificates
and numerical KRK bounds still needed. Failure gives no draw theorem. No full
FIDE key/rights/history/adjudication/real claim correspondence or complete KRK
outcome/strategy/distance/WDL/DTZ/initial value. Transparent same-agent separate
paper/Lean audit, not independent external review. Symbolic zero/early mate,
99/100,2/3,current/intended/new-child-key,zeroing,adverse capture-to-KK,exact history,
all colours/promotions/raw flags; no full-game run/enumeration/oracle/per-position
certificates/novelty. Latest owner instruction: finish/close S066, then STOP before S067. KRK remains incomplete.'''
checks='''Standalone precise paper/separate adversarial audit BEFORE Lean, then LOCAL_VERIFIED.
Initial Prepend authoring failure retained: induction generalised the leading
step proof, so use ih step rather than ih. Statement/model unchanged. Failure
log/commands/exits/times/UTC retained; working incremental build/full runner then
passed. One new fresh Gate F build, no fresh-build failure/interruption/retry.
Full logs/commands/exits/times/UTC, executable/toolchain, clean HEAD/tree/status,
all source/transitive SHA256 retained. Official core Lean4.35.0 release
eb6cafb7290e8bd5f2937522d8d804f58f02bafc; no dependency/shim/TLS/checksum changes.
Inherited proxy/CA, current unrestricted/enforced policy. Hosted CI unobserved.
Relevant ledger tests/structure/evidence/preservation/full-table/full-prompt/
local-link/diff checks passed, prior protected files/36 ledger rows unchanged,
aggregates/runner additive. No unrelated diagnostics/trivial tests. Gate Z separate.'''
p=root/'research/CANDIDATES.md';p.write_text(p.read_text().replace('LOCAL_VERIFIED (S066, 2026-10-20); Gate F pending','FORMAL_VERIFIED (S066, 2026-10-20); Gate Z pending').replace('Actual-step prepend helper; explicit strong sufficient certificate,',result+' [Evidence](../sessions/evidence/S066/README.md). Actual-step prepend helper; explicit strong sufficient certificate,'))
p=root/'audits/EC-C039_BUDGET_LIFTING_LEAN.md';p.write_text(p.read_text().replace('No fresh build attempted yet; Gate F pending.','Gate F passed after the retained authoring fix.\n\n'+result+'\n\n'+checks))
p=root/'docs/SESSION_PROGRESS.md';t=p.read_text().replace('through S065.','through S066.');lines=t.splitlines();lines=[('| K+R vs K | Dead/live and clock-free forcing frozen; raw history/rule prerequisites frozen; conditional budget lifting formally verified | Concrete FIDE integration, complete rule-aware outcomes and distance |' if l.startswith('| K+R vs K |') else l) for l in lines];t='\n'.join(lines)+'\n';delta='Session change: S066 formally verified same-budget raw lifting under explicit clock/full-prefix repetition hypotheses; 36 bundles remain frozen and material-class coverage is unchanged.';t=t.replace(next(l for l in t.splitlines() if l.startswith('Session change:')),delta);p.write_text(t)
p=root/'README.md';t=p.read_text().replace('**After S065.**','**After S066.**').replace('Complete FIDE histories/claims/repetition, sufficient-budget lifting and numerical KRK distances remain open.','Concrete FIDE correspondence, strategy-specific repetition certificates and numerical KRK/outcome/distance coverage remain open.').replace('- Next: S066, same-budget raw lifting under explicit clock/full-prefix repetition bounds.','- Next (paused by owner after S066): S067, separate own-source freeze of conditional raw sufficient-budget lifting.');t+='\n- S066: EC-C039 **FORMAL_VERIFIED**, same-budget raw rule-mate lifting under clock+n<100 and count<3 on EVERY actual raw prefix through n. [Paper](proofs/EC-C039_RAW_SUFFICIENT_BUDGET_LIFTING.md), [evidence](sessions/evidence/S066/README.md). Strong sufficient certificate only; no general KRK history/numeric witness or full outcome coverage.\n';p.write_text(t)
p=root/'docs/ROADMAP.md';p.write_text(p.read_text().replace('No FIDE repetition key is claimed; no numerical KRK bound, repetition certificate or sufficient-budget lifting follows. Concrete FIDE instantiation, sufficient-budget lifting, history invariants, holding/determinacy and numerical KRK distances remain open.','No FIDE repetition-key correspondence is claimed; no numerical KRK bound or strategy-specific repetition certificate follows. Concrete FIDE correspondence, strategy-specific safety certificates, remaining history invariants, holding/determinacy and numerical KRK distances remain open.').replace('Owner instruction 2026-10-20: continue KRK until entirely finished/frozen; stop before KQK.','Latest owner instruction 2026-10-20: finish/close S066, then STOP. Further sessions are paused pending explicit resumption; do not start S067 or KQK automatically.').replace('S066 targets conditional same-budget raw lifting under explicit safety bounds.','S066 formally verified EC-C039, conditional same-budget raw lifting under explicit clock/full-prefix repetition bounds ([paper](../proofs/EC-C039_RAW_SUFFICIENT_BUDGET_LIFTING.md), [evidence](../sessions/evidence/S066/README.md)); S067 separate freeze is paused by the latest owner instruction to stop after S066.'))
p=root/'docs/KRK_COMPLETION.md';t=p.read_text().replace('Owner 2026-10-20: continue until KRK entirely finished and frozen; stop before KQK.','Latest owner instruction 2026-10-20: finish and close S066, then STOP. Prior continuation until KRK completion is paused; do not start S067 or KQK automatically.').replace('2. Same-budget lifting under explicit claim-safe prefix conditions. Use actual','2. Conditional all-raw-prefix budget lifting FORMAL_VERIFIED S066 (EC-C039), S067 freeze pending. Strong sufficient clock/count hypotheses only, no general KRK witness. Strategy-specific repetition certificates remain needed. Use actual');p.write_text(t)
p=root/'NEXT_SESSION.md';p.write_text(p.read_text().replace('Read actual S066 evidence/closeout for FULL OWN proof-source SHA and success.','OWN S066 full proof-source SHA: '+sha+'.\nRead actual S066 evidence/closeout for FULL OWN proof-source SHA and success.'))
(out/'README.md').write_text(f'''# S066 — Conditional sufficient-budget raw lifting Gate F

{result}

{scope}

{checks}

{limits}

Reproduce: `python sessions/evidence/S066/verify.py REPO_ROOT NEW_OUTPUT NEW_CLONE {sha}`.
Validate: `python sessions/evidence/S066/validate.py`.
''')
table='\n'.join(l for l in (root/'docs/SESSION_PROGRESS.md').read_text().splitlines() if l.startswith('|'));prompt=(root/'NEXT_SESSION.md').read_text().strip()
(root/'sessions/S066_RAW_SUFFICIENT_BUDGET_LIFTING.md').write_text(f'''# S066 — Clock/full-prefix repetition sufficient-budget lifting

2026-10-20. Base main 5728f9f6637166b65baa5ae3d12c969350fe629b,
branch session/s066-raw-sufficient-budget-lifting. ALL-heads fetch, no prior
unmerged heads, existing checkout. Latest owner instruction: finish/close S066, then DO NOT start S067 or any later
session. Earlier KRK-completion continuation is paused. EC-C039 FORMAL_VERIFIED;
Gate Z pending; KRK incomplete.

{scope}

[Paper](../proofs/EC-C039_RAW_SUFFICIENT_BUDGET_LIFTING.md),
[paper audit](../audits/EC-C039_BUDGET_LIFTING_PAPER.md),
[Lean audit](../audits/EC-C039_BUDGET_LIFTING_LEAN.md).

{limits}

## Observed verification and publication

{result}

{checks}

[Evidence](evidence/S066/README.md). Own proof source committed/pushed before new
GitHub clone; closeout committed/pushed branch, merged/pushed main, matching remote
identities observed at publication. Local work/ contains scratch clones/drafts,
ignored through .git/info/exclude; no uncommitted project source remains after
publication. STOP after this closeout; S067 prompt retained for explicit future resumption only. Ledger unchanged.

## Required progress table

{table}

{delta}

## Full installed S067 prompt

{prompt}
''')
p=root/'sessions/SESSION_LEDGER.md';p.write_text(p.read_text().replace('Full session closeouts live','| S066 | 2026-10-20 | EC-C039 conditional raw sufficient-budget lifting (Gate L/F) | Same n under strict clock/full-prefix count hypotheses; exact prepend helper. [Closeout](S066_RAW_SUFFICIENT_BUDGET_LIFTING.md) | None — 36 frozen bundles |\n\nFull session closeouts live'))
print(result)
