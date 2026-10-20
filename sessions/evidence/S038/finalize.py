"""Write S038 closeout from observed completed Gate F summary, without rerunning Lean."""
import json
from pathlib import Path
root=Path(__file__).resolve().parents[3]
out=root/'sessions/evidence/S038'
s=json.loads((out/'summary.json').read_text())
assert s['build_exit']==s['axiom_statement_exit']==0
sha=s['proof_source']; utc=s['verified_utc']; seconds=s['build_seconds']
p=root/'research/CANDIDATES.md'
t=p.read_text().replace('LOCAL_VERIFIED (S038, 2026-10-20); Gate F pending','FORMAL_VERIFIED (S038, 2026-10-20); Gate Z pending').replace('Universal raw bound includes resets and earlier raw draws; no sufficient-budget lifting, numeric KRK bound, repetition or FIDE adjudication.',f'Universal raw bound includes resets and earlier raw draws. Exact source `{sha}`; fresh 68-job build, 272 allowed reports. [Evidence](../sessions/evidence/S038/README.md). No sufficient-budget lifting, numeric KRK bound, repetition or FIDE adjudication.')
p.write_text(t)
p=root/'audits/EC-C025_RAW_CLOCK_EXTENSION_LEAN.md'
p.write_text(p.read_text()+f"""
## Completed Gate F

Published proof-source `{sha}` before ONE NEW GitHub clone,
detached at that exact SHA, formal/.lake absent before full build. Full lake
build: 68 jobs, exit 0, {seconds}s; COMPLETE AxiomCheck exit 0 at {utc}.
272 allowed reports, including 5 axiom-free; new main standard-three only.
Exact statement/constructors printed; full working/clean runner outputs
byte-identical. All Lean source/import bytes match; complete source/transitive
hashes and clean-source identities retained. Two new modules forbidden scan
zero. Official core Lean4.35.0 release eb6cafb7290e8bd5f2937522d8d804f58f02bafc;
executable hash matches preceding freeze evidence. No dependencies or shim.
Gate F passed, Gate Z pending. Hosted CI unobserved. Evidence: sessions/evidence/S038/.
""")
readme=f"""# S038 — EC-C025 exact-source Gate F evidence

Published source `{sha}`, ONE NEW GitHub clone
`{s['fresh_clone']}`, detached at exact SHA. formal/.lake absent before build.
Full lake build **68 jobs, exit 0, {seconds}s**; complete AxiomCheck **exit 0**,
verified UTC **{utc}**. **272** allowed reports; new main
EndgameChess.Rules.RawClock.clock_le_extension uses standard three only.
Official core Lean 4.35.0 release eb6cafb7290e8bd5f2937522d8d804f58f02bafc,
no dependencies; executable hash matches preceding S037 official identity.

- commands.json: actual commands, exits and elapsed times.
- clone.log, checkout.log, pre-build.log: fresh exact-source identity before build.
- toolchain.log, lake-version.log, runtime-identity.json: official runtime identity.
- lake-build.log, axioms-statements.log: full fresh build and complete statements/axioms.
- working-build.log, working-axioms.log: successful incremental authoring checks.
- initial-build-failure.log: retained syntax failure before correction.
- source-sha256.txt, dependency-sha256.txt: full source and transitive closure.
- clean-source-identity.json: exact commit/tree and clean tracked/untracked state.
- summary.json: completed result and declaration-specific axioms.
- forbidden-tokens.log, preservation.log, ledger-validation.log, validation.log:
  source/record/evidence/document checks, separate from Lean verification.

Complete runner output byte-identical to working report; every Lean source
matches exact fresh source. All prior source/papers/audits/evidence/ledger bytes
preserved; aggregate imports/runner only add entries. No new frozen row/manifest.
No unrelated diagnostic suite or trivial tests. Controls are symbolic, with no
fixed promotion/ep/castling full game prefix run. Hosted CI **unobserved**.

Reproduce only for a new obligation using NEW output/clone paths:

```sh
python sessions/evidence/S038/verify.py REPO_ROOT NEW_OUTPUT NEW_CLONE {sha}
python sessions/evidence/S038/validate.py
```

The verifier's post-launch comparison path was generalized for NEW output
locations; see reproducer-note.md. No Lean source or actual commands changed.
This is raw counter growth, not sufficient-budget lifting, a numerical KRK
mate bound, repetition/FIDE adjudication or a new solved material class.
"""
(out/'README.md').write_text(readme)
progress=(root/'docs/SESSION_PROGRESS.md').read_text()
table='\n'.join(l for l in progress.splitlines() if l.startswith('|'))
delta=next(l for l in progress.splitlines() if l.startswith('Session change:'))
prompt=(root/'NEXT_SESSION.md').read_text().strip()
closeout=f"""# S038 — Raw multi-step clock bound along actual trace extensions

2026-10-20. Base main `0721c7f`; branch `session/s038-clock-extension` in the
existing checkout. Advanced main to latest origin/main. Initial all-remotes
fetch inherited a main-only refspec; explicit subsequent all-heads fetch
confirmed every earlier session branch was already merged. Only active S038
was unmerged. Publication authorised; details in evidence/S038/branch-review.log.

## Result and scope

**EC-C025 FORMAL_VERIFIED, Gate Z pending.** One new main theorem:

`RawTrace.Extends n s t → RawClock.clock t.trace ≤ RawClock.clock s.trace + n`.

New shared RawTrace/ExtensionDefinitions defines an indexed finite relation on
full raw states. Its zero case is exactly s; successor uses frozen RawBoardStep
with actual Move, source legality and exact append equality. New theorem module
RawClock/ExtensionBound inducts on this extension and uses frozen append_clock_le,
transitivity and additive monotonicity. Every legal resetting/quiet ply is
included; counter data are derived from full initial-rooted traces, never seeded.
No endpoint-clock hypothesis, erased-board surrogate or terminal filter.
Full prior trace is retained on resets; n counts actual board plies, not claims
or full moves. One main per module, shared definitions separate, exact data and
statement/axioms added to AxiomCheck. No redundant length/prefix declarations.

[Paper](../proofs/EC-C025_RAW_CLOCK_EXTENSION_BOUND.md) and
[adversarial paper review](../audits/EC-C025_RAW_CLOCK_EXTENSION_PAPER.md) saved
BEFORE Lean. [Lean fidelity review](../audits/EC-C025_RAW_CLOCK_EXTENSION_LEAN.md).
Same-agent reviews, not independent external review. Symbolic falsification
attempts: zero exact-state identity; quiet increment; zeroing reset; mixed
paths; equal erased boards with differing histories; earlier raw draw.
No fixed complete promotion/ep/castling/draw-threshold history constructed or
run. Classical finite-path argument, no novelty claim, tablebase, engine,
class enumeration, stored position certificate or arbitrary-clock KRK witness.

## Observed verification

Published exact proof-source **`{sha}`** before ONE NEW GitHub
Gate F clone `{s['fresh_clone']}`; detached exact source, formal/.lake absent
before build. Full **lake build: 68 jobs, exit 0, {seconds}s**. Complete
**AxiomCheck: exit 0**, UTC **{utc}**; **272 allowed axiom reports**
(240 standard-three, 18 propext/Quot.sound, 9 propext, 5 axiom-free).
New main uses **[propext, Classical.choice, Quot.sound]**. Exact constructor and
main statement output inspected. Full clean/working reports byte-identical;
all Lean source bytes match exact source, with full source/transitive hashes.
Clean-source HEAD/tree/status retained. Official unmodified core Lean 4.35.0
release eb6cafb7290e8bd5f2937522d8d804f58f02bafc; executable hash matches prior
freeze identity. No dependencies/host shim, TLS/checksum verification unchanged.

Incremental build and complete authoring runner also passed. Initial compile
failed at a line break after `using`; parenthesizing the applied term fixed
syntax without altering the statement. Full failed log retained. The running
verifier compared the working report in the existing output path; its retained
reproducer later generalized that path for fresh output locations. No build or
axiom check was rerun for this documentation-only correction.

Runtime was connected with current observations, no secret/identity bindings;
unrestricted desired policy with enforcement state unknown. Network snapshot
inspected and inherited Git proxy reused successfully. No environment change
or installation needed. Hosted CI **unobserved**, not inferred from publication.
Complete [evidence](evidence/S038/README.md) retains commands/exits/timings,
source identities, full logs, hashes and separate validation/preservation output.
Relevant ledger structural validator and evidence/preservation/document checks
passed. No unrelated diagnostic suite or new trivial tests were run.

## Preservation, limits and publication

Twenty-two frozen bundles unchanged: no ledger row or manifest added, no prior
candidate/frozen source, paper, audit, session evidence or ledger bytes changed.
Aggregate Lean import/runner changes additive only. The prior candidate rows
remain intact; only EC-C025 is added with observed Gate F evidence.

This proves a raw counter upper bound, NOT sufficient-budget lifting.
h+n<100 remains a future certificate HYPOTHESIS. No numerical KRK mate bound,
repetition certificate/key correctness, no-earlier-terminal FIDE admissibility,
current/intended claims, automatic fivefold/75-move adjudication, mate precedence,
full Layer A/B/C instance, holding/outcome theorem, DTM/DTZ/WDL/Syzygy parity or
initial-position result. Every raw legal reply, including adverse draw-ending
children, remains admitted. Material-class coverage is unchanged.

S039 installs a separate fresh exact-source Gate Z review for this one new
bundle, preserving this own anchor and all prior evidence. After successful
freeze a narrowly stated explicit-hypothesis prefix/prospective-ply clock
certificate is a possible next small prerequisite, with repetition and full
FIDE lifting still separate. Session closeout is committed/pushed on the session
branch, fast-forwarded to main, pushed, and remote SHAs compared; exact final
identity is recorded by Git history and the final publication check.

## Required progress table

{table}

{delta}

## Full installed S039 prompt

{prompt}
"""
(root/'sessions/S038_RAW_CLOCK_EXTENSION_BOUND.md').write_text(closeout)
p=root/'sessions/SESSION_LEDGER.md'
t=p.read_text(); marker='Full session closeouts live'
row=f'| S038 | 2026-10-20 | EC-C025 raw multi-step clock bound (Gate L/F) | Exact-state zero and actual RawBoardStep successor; induction includes all resets. Source `{sha}`; ONE NEW 68-job fresh build, 272 allowed reports, main standard-three. Prior sources/records unchanged; S039 exact-source freeze installed. [Closeout](S038_RAW_CLOCK_EXTENSION_BOUND.md) | None — 22 frozen bundles |\n\n'
p.write_text(t.replace(marker,row+marker))
print('Wrote candidate status, completed fidelity audit, evidence README, full closeout/table/S039 prompt and session ledger from observed summary.')
