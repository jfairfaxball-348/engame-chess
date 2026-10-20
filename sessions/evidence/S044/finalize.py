"""Finalize S044 only after successful own exact-source Gate F evidence."""
import json
from pathlib import Path
root=Path(__file__).resolve().parents[3];out=root/'sessions/evidence/S044'
s=json.loads((out/'summary.json').read_text());assert s['build_exit']==s['axiom_statement_exit']==0
sha=s['proof_source'];assert sha=='28bdacfa34995ed3d778bfb2dab1654e46999f0c'
utc=s['verified_utc'];sec=s['build_seconds']
p=root/'research/CANDIDATES.md';t=p.read_text().replace('LOCAL_VERIFIED (S044, 2026-10-20); Gate F pending','FORMAL_VERIFIED (S044, 2026-10-20); Gate Z pending').replace('Target consistency proved; no full repetition key/FIDE claim semantics.',f'Own source `{sha}`; fresh 73-job build, 275 allowed reports. [Evidence](../sessions/evidence/S044/README.md). Target consistency proved; no full repetition key/FIDE claim semantics.');p.write_text(t)
p=root/'audits/EC-C028_EFFECTIVE_EP_LEAN.md';p.write_text(p.read_text()+f"""
## Completed Gate F

Own published source `{sha}`; ONE NEW GitHub clone with no .lake
before build. Full 73-job lake build exit 0, {sec}s; COMPLETE AxiomCheck
exit 0 at {utc}, 275 allowed reports, main standard-three only.
Definitions/combined statement inspected; working/clean outputs identical.
Every formal source matches own exact anchor, all source/transitive hashes and
clean HEAD/tree/status retained. Two new modules forbidden scan zero. Official
core Lean4.35.0 release eb6cafb7290e8bd5f2937522d8d804f58f02bafc; no dependency/
shim. Initial local failed log retained; fresh build passed without warning or
failure. Gate F complete, Gate Z pending. Hosted CI unobserved.
""")
p=root/'docs/SESSION_PROGRESS.md';t=p.read_text().replace('through S043.', 'through S044.').replace('generic key counting frozen |','generic key counting frozen; effective-ep target formally verified |');delta='Session change: S044 formally verified legality-filtered en-passant availability and its effective-target specification; 25 bundles remain frozen and material-class coverage is unchanged.';t=t.replace(next(l for l in t.splitlines() if l.startswith('Session change:')),delta);p.write_text(t)
p=root/'README.md';t=p.read_text().replace('**After S043.**','**After S044.**').replace('- Next: S044, legality-filtered en-passant availability/effective target specification.', '- S044: **EC-C028 FORMAL_VERIFIED**: actual legal ep event and noncomputable effective target, none iff no legal witness and some dst iff a witness targets dst. [Paper](proofs/EC-C028_EFFECTIVE_EP_TARGET.md), [evidence](sessions/evidence/S044/README.md). Gate Z pending; no complete FIDE repetition-key result.\n- Next: S045, separate exact-source Gate Z review of EC-C028.');p.write_text(t)
p=root/'docs/ROADMAP.md';t=p.read_text().replace('S044 targets legality-filtered en-passant availability/effective target before key composition.', 'S044 formally verifies **EC-C028**, legality-filtered en-passant availability/effective-target specification ([paper](../proofs/EC-C028_EFFECTIVE_EP_TARGET.md), [evidence](../sessions/evidence/S044/README.md)); S045 Gate Z pending before further kernel fidelity/key composition.');p.write_text(t)
(out/'README.md').write_text(f"""# S044 — EC-C028 effective ep target Gate F evidence

Own published SHA `{sha}`, ONE NEW GitHub clone
`{s['fresh_clone']}`, formal/.lake absent before build. Full **73-job lake
build exit 0, {sec}s**; COMPLETE **AxiomCheck exit 0**, **275 allowed reports**,
UTC **{utc}**, main standard-three only. Exact definitions/main inspected;
whole clean/working report identical. All formal bytes match own anchor; full
source/transitive hashes and clean HEAD/tree/status retained. Official core
Lean4.35.0 release eb6cafb7290e8bd5f2937522d8d804f58f02bafc, no dependency/shim.

Full clone/checkout/prebuild/build/axiom/toolchain/lake logs, commands/exits/
timings, runtime identity, hashes, summary/declaration list retained. Initial
LOCAL compile failed because unpacking an existential removed a reused hypothesis;
actual witness reconstructed, redundant simp warning resolved, no mathematical
weakening. Full initial log retained. Final incremental and fresh runs passed.
Forbidden-token, preservation, ledger and document checks retained separately.
All prior source/papers/audits/evidence/manifests and 25 ledger rows unchanged;
aggregate Lean files additive only. No unrelated diagnostics/trivial tests or
concrete pinned/full promotion/ep/castling/threshold game. Hosted CI unobserved.

```sh
python sessions/evidence/S044/verify.py REPO_ROOT NEW_OUTPUT NEW_CLONE {sha}
python sessions/evidence/S044/validate.py
```

Actual isLegal-filtered NONCOMPUTABLE target only, not pseudo-legal search, FIDE
key correspondence, low repetition, claim/adjudication, KRK distance or class gain.
""")
table='\n'.join(l for l in (root/'docs/SESSION_PROGRESS.md').read_text().splitlines() if l.startswith('|'));prompt=(root/'NEXT_SESSION.md').read_text().strip()
(root/'sessions/S044_EFFECTIVE_EP_TARGET.md').write_text(f"""# S044 — Legality-filtered en-passant availability and effective target

2026-10-20, base main 52f28df8cc60c91f9c5c27712fb072983476e33e;
branch session/s044-effective-ep-target. Explicit all-heads fetch, no earlier
unmerged session, existing checkout. Publication/consecutive execution authorised.

## Result and exact scope

**EC-C028 FORMAL_VERIFIED, Gate Z pending.** Shared RawRepetition/Definitions
and one main EffectiveEP/effectiveEP_spec. LegalEP requires actual isLegal,
frozen Pawn, q.ep=some m.dst, distinct files, empty destination and opposing
flank pawn. It is the existing CaptureEvent EP event with legality; play's
epCapture remains a LOCAL let, not an exported predicate. effectiveEP is explicitly
NONCOMPUTABLE classical existence-filtered q.ep, no enumeration/search claim.

For EVERY raw q the combined main gives none iff no legal event, and some dst
iff an actual legal witness targets dst. Witness flag consistency proves the
available branch cannot be none or wrong-target; some injectivity identifies
all witness destinations. No independent target/count/clock seed, endpoint
hypothesis, pseudo-legal substitute or terminal/material/colour/strategy filter.
Arbitrary raw flags covered without asserting lawful preceding FIDE history.

[Paper](../proofs/EC-C028_EFFECTIVE_EP_TARGET.md) and
[adversarial audit](../audits/EC-C028_EFFECTIVE_EP_PAPER.md) saved BEFORE Lean;
[Lean fidelity](../audits/EC-C028_EFFECTIVE_EP_LEAN.md). Same-agent review, not
independent external audit. Symbolic absent flag/no eligible pawn/only pseudo-
legal self-check/multiple-source/occupied/wrong-kind-colour-flank/ordinary-move
controls found no local gap. No concrete pinned board or full compatible
promotion/ep/castling/threshold game run. Classical construction, no novelty,
tablebase/engine/enumeration or stored-position certificate.

## Observed verification

OWN source **{sha}** published BEFORE ONE NEW GitHub clone
**{s['fresh_clone']}**, detached FULL exact SHA; no .lake before build.
Full **73-job lake build exit 0, {sec}s**, COMPLETE **AxiomCheck exit 0**,
UTC **{utc}**, **275 allowed reports** (243 standard-three,
18 propext/Quot.sound, 9 propext, 5 axiom-free); main standard-three only.
Definitions/main exact output inspected. Whole clean/working report identical;
every formal source matches exact anchor, full source/transitive hashes and
clean HEAD/tree/status retained. Two new modules forbidden scan zero.

First local compile failed because existential unpacking cleared `available`
while subsequent proof steps reused it. Reconstructing the actual witness
fixed the proof; a redundant simpa warning removed by direct contradiction
simplification. Full initial failure retained; mathematical definitions/statement
unchanged. Final incremental build/runner and fresh build/runner passed with no
warning. No repeated clean run. Official unmodified core Lean4.35.0 release
 eb6cafb7290e8bd5f2937522d8d804f58f02bafc, no dependency/shim. Existing elan/
Git proxy/network policy sufficient, TLS/checksums unchanged, no setup change.
Hosted CI unobserved. [Evidence](evidence/S044/README.md). Relevant preservation,
ledger structure, evidence/full table/prompt/local-link/diff checks passed;
no unrelated diagnostics/trivial tests. Prior source/papers/audits/session/
evidence/manifests and 25 rows unchanged; aggregates additive only.

## Limits and next session

No full repetition key or Article9.2.3/rights-history correspondence, low-count
certificate, claims/admissibility/adjudication/mate precedence, full Layer/
strategy extraction/lifting, numerical KRK mate bound, holding/outcomes,
DTM/DTZ/WDL/Syzygy or initial-position value. Frozen generic counts do not
upgrade this target spec to FIDE claims. S045 installs separate exact-source
freeze; a later precise kernel-fidelity EP characterization may precede any
normalization/key composition. Commit/push branch, merge/push main and compare
remote SHAs; final identity in Git history/observed publication checks. Continue S045.

## Required progress table

{table}

{delta}

## Full installed S045 prompt

{prompt}
""")
p=root/'sessions/SESSION_LEDGER.md';t=p.read_text().replace('Full session closeouts live',f'| S044 | 2026-10-20 | EC-C028 effective legal-ep target (Gate L/F) | Actual LegalEP event, classical effective target, none/no-witness and some/exact-witness spec. Source `{sha}`; fresh 73-job build, 275 allowed reports. No full FIDE key. S045 freeze installed. [Closeout](S044_EFFECTIVE_EP_TARGET.md) | None — 25 frozen bundles |\n\nFull session closeouts live');p.write_text(t)
print('Created S044 complete evidence-backed records and S045 handover.')
