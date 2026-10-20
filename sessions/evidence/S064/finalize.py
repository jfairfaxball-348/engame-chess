"""Finalize concrete raw Layer only after observed Gate F success."""
import json
from pathlib import Path
root=Path(__file__).resolve().parents[3];out=root/'sessions/evidence/S064';s=json.loads((out/'summary.json').read_text());sha=s['proof_source'];assert sha=='e346ebccd93971887cb3017487ecd1efff1bf51e' and s['build_exit']==s['axiom_statement_exit']==0
result=f"Own proof source `{sha}`; NEW GitHub clone `{s['fresh_clone']}`, .lake absent before build. Full {s['build_jobs']}-job build exit 0 ({s['build_seconds']}s); complete AxiomCheck exit 0 at {s['verified_utc']}, {s['total_axiom_reports']} allowed reports. Exact main inspected, standard-three only; entire working/clean runner output and all formal bytes identical."
scope='''NEW RawHistoryLayer.State retains actual raw state/entire indexed trace and
StoppedHistory.Admissible proof. Erase underlying endpoint, BoardStep actual
RawBoardStep, Ongoing raw classify=ongoing, CanClaim raw AvailableThreshold.
Concrete Layer soundness from raw_step_sound; EVERY Legal reply lifted using
admissible ongoing parent and EC-T0035, retaining terminal children; nondeadness
from ongoing_iff. Main raw_ruleMateWithin_project instantiates frozen generic
projection with EXACT SAME s/colour/n. No certificate existence or converse.'''
limits='''Concrete RAW Layer only; no full FIDE key/rights-history/adjudication/real claim
protocol correspondence. No rule-aware KRK outcome/strategy, numeric bound,
holding/determinacy, WDL/DTZ or initial value. Same-agent separate paper/Lean audit,
not independent external review. Start/current terminal/parent terminal/terminal
child, subtype witness and all legal moves/colours/promotions/raw flags and zero
budget reviewed symbolically. Optional claim opportunities separate; no successful/
invalid claim/procedural phase in traces. No full-game run/enumeration/oracle/
per-position certificates/novelty. Owner scope remains finish KRK/freeze, stop KQK.'''
checks='''Standalone paper and separate adversarial audit completed before Lean, then
LOCAL_VERIFIED. New shared definitions and one main module, additive aggregates/
runner, all prior frozen sources untouched. Working incremental build and complete
runner passed first attempt. One new GitHub Gate F build, no failure/interruption/
retry. Full logs/commands/exits/times/UTC, executable/toolchain identity, all source/
transitive SHA256 and clean HEAD/tree/status retained. Official core Lean4.35.0
release eb6cafb7290e8bd5f2937522d8d804f58f02bafc; no dependency/shim/TLS/checksum
changes. Inherited proxy/CA, current unrestricted/enforced network policy.
Hosted CI unobserved. Relevant ledger tests/structure/evidence/preservation/full
progress table/prompt/local-link/diff checks passed; prior protected files and35
ledger rows unchanged. No unrelated diagnostics/trivial tests. Gate Z separate.'''
p=root/'research/CANDIDATES.md';p.write_text(p.read_text().replace('LOCAL_VERIFIED (S064, 2026-10-20); Gate F pending','FORMAL_VERIFIED (S064, 2026-10-20); Gate Z pending').replace('Full actual trace retained, EVERY legal reply including terminal children;',result+' [Evidence](../sessions/evidence/S064/README.md). Full actual trace retained, EVERY legal reply including terminal children;'))
p=root/'audits/EC-C038_RAW_LAYER_LEAN.md';p.write_text(p.read_text().replace('Gate F pending.','Gate F passed.\n\n'+result+'\n\n'+checks))
p=root/'docs/SESSION_PROGRESS.md';t=p.read_text().replace('through S063.','through S064.').replace('endpoint classifier and stopped-history append/reply prerequisites frozen |','endpoint classifier and stopped-history append/reply prerequisites frozen; concrete RAW Layer formally verified |');delta='Session change: S064 formally verified the concrete RAW stopped-history Layer and same-budget projection; 35 bundles remain frozen and material-class coverage is unchanged.';t=t.replace(next(l for l in t.splitlines() if l.startswith('Session change:')),delta);p.write_text(t)
p=root/'README.md';t=p.read_text().replace('**After S063.**','**After S064.**').replace('- Next: S064, concrete RAW Layer on admissible stopped histories.','- Next: S065, separate own-source freeze of the concrete RAW stopped-history Layer.');t+='\n- S064: EC-C038 **FORMAL_VERIFIED**, concrete RAW stopped-history Layer with EVERY legal reply, including terminal children, and same-budget certificate projection. [Paper](proofs/EC-C038_RAW_STOPPED_HISTORY_LAYER.md), [evidence](sessions/evidence/S064/README.md). [KRK completion obligations](docs/KRK_COMPLETION.md) remain explicit; stop before KQK.\n';p.write_text(t)
p=root/'docs/ROADMAP.md';t=p.read_text().replace('S064 targets a concrete RAW Layer on admissible stopped histories.','S064 formally verified EC-C038, concrete RAW stopped-history Layer and same-budget certificate projection ([paper](../proofs/EC-C038_RAW_STOPPED_HISTORY_LAYER.md), [evidence](../sessions/evidence/S064/README.md)); S065 separate freeze next.');t+='\nOwner instruction 2026-10-20: continue KRK until entirely finished/frozen; stop before KQK. Track remaining obligations in [KRK completion](KRK_COMPLETION.md).\n';p.write_text(t)
p=root/'docs/KRK_COMPLETION.md';p.write_text(p.read_text().replace('1. Concrete RAW Layer on admitted stopped histories (S064, then separate freeze).','1. Concrete RAW Layer on admitted stopped histories: FORMAL_VERIFIED S064 (EC-C038); separate S065 freeze pending.'))
p=root/'NEXT_SESSION.md';p.write_text(p.read_text().replace('Read actual S064 evidence/closeout for FULL OWN proof-source SHA and success,','OWN S064 proof-source SHA: '+sha+'.\nRead actual S064 evidence/closeout for FULL OWN proof-source SHA and success,'))
(out/'README.md').write_text(f'''# S064 — Concrete RAW stopped-history Layer Gate F

{result}

{scope}

{checks}

{limits}

Reproduce: `python sessions/evidence/S064/verify.py REPO_ROOT NEW_OUTPUT NEW_CLONE {sha}`.
Validate: `python sessions/evidence/S064/validate.py`.
''')
table='\n'.join(l for l in (root/'docs/SESSION_PROGRESS.md').read_text().splitlines() if l.startswith('|'));prompt=(root/'NEXT_SESSION.md').read_text().strip()
(root/'sessions/S064_RAW_STOPPED_HISTORY_LAYER.md').write_text(f'''# S064 — Concrete RAW stopped-history Layer

2026-10-20. Base main f810f4bb6c4afdef539352e538e3ca2aca7a8c99,
branch session/s064-raw-stopped-history-layer. ALL-heads fetch, no prior unmerged
heads, existing checkout. Owner authorises continuing to complete/freeze KRK,
stopping BEFORE KQK. EC-C038 FORMAL_VERIFIED; Gate Z pending, ledger unchanged.

{scope}

[Paper](../proofs/EC-C038_RAW_STOPPED_HISTORY_LAYER.md),
[paper audit](../audits/EC-C038_RAW_LAYER_PAPER.md),
[Lean audit](../audits/EC-C038_RAW_LAYER_LEAN.md).

{limits}

## Observed verification and publication

{result}

{checks}

[Evidence](evidence/S064/README.md). Proof source committed/pushed before clone;
closeout committed/pushed, merged/pushed main, matching remote identities observed
at publication. Continue installed S065. Completion tracker added to avoid
confusing raw prerequisites with full material-class coverage.

## Required progress table

{table}

{delta}

## Full installed S065 prompt

{prompt}
''')
p=root/'sessions/SESSION_LEDGER.md';p.write_text(p.read_text().replace('Full session closeouts live','| S064 | 2026-10-20 | EC-C038 concrete RAW stopped-history Layer (Gate L/F) | All interface fields, full legal replies and same-budget projection. [Closeout](S064_RAW_STOPPED_HISTORY_LAYER.md) | None — 35 frozen bundles |\n\nFull session closeouts live'))
print(result)
