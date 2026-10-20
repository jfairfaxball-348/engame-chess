# S038 — Raw multi-step clock bound along actual trace extensions

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

Published exact proof-source **`22243b9ca5769e1478c75a333befa3c8465c90f2`** before ONE NEW GitHub
Gate F clone `/tmp/engame-s038-gate-f`; detached exact source, formal/.lake absent
before build. Full **lake build: 68 jobs, exit 0, 472.858s**. Complete
**AxiomCheck: exit 0**, UTC **2026-10-20T07:44:55Z**; **272 allowed axiom reports**
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

| Endgames / target | Progress | Remaining |
|---|---|---|
| K vs K | Draw proved and frozen | — |
| K+B vs K | Draw proved and frozen | — |
| K+N vs K | Draw proved and frozen | — |
| K+R vs K | Dead/live, clock-free forcing, generic projection, raw traces and counter frozen; multi-step clock bound formally verified | FIDE history/adjudication and distance |
| K+Q vs K | Open in this project | General proof and formal verification |
| K+P vs K | Open in this project | General proof and formal verification |
| All four-piece endgames | Open in this project | Every material class and legal position |
| All five-piece endgames | Open in this project | Every material class and legal position |
| All six-piece endgames | Open in this project | Every material class and legal position |
| All seven-piece endgames | Open in this project | Every material class and legal position |
| **Full Syzygy parity (through seven pieces)** | **Open** | **Complete class coverage, 50-move WDL and DTZ parity** |

Session change: S038 formally verified the raw multi-step clock bound along actual trace extensions; 22 bundles remain frozen and material-class coverage is unchanged.

## Full installed S039 prompt

# NEXT SESSION — S039: Freeze the actual-trace multi-step clock bound

**Owner instruction:** Execute when the owner says “run next session”. Follow
AGENTS.md: fetch ALL branches, merge earlier unmerged session work, then read
latest main's active prompt. Existing checkout, no worktree. Publication is
authorised. End committed, pushed on the session branch, merged and pushed to
main; never force main. Update docs/SESSION_PROGRESS.md and reproduce its FULL
stable table in closeout and final reply, Syzygy parity LAST, with a one-sentence
session delta immediately below. Bundles are not solved material classes.

## Starting point and required reading

S038 established EC-C025 at Gate F, not Gate Z. Twenty-two bundles remain frozen.
Own exact published proof-source anchor:
`22243b9ca5769e1478c75a333befa3c8465c90f2`.
Read docs/CHARTER.md, docs/PROOF_PROTOCOL.md, docs/ROADMAP.md,
research/CANDIDATES.md, research/KRK_RULE_DISTANCE_SPEC.md (sufficient-budget
lifting), EC-T0021/0022 manifests and actual S037 verification evidence.
Read proofs/EC-C025_RAW_CLOCK_EXTENSION_BOUND.md, both EC-C025 audits,
sessions/S038_RAW_CLOCK_EXTENSION_BOUND.md and actual sessions/evidence/S038/
logs, summary, source/import hashes and clean-source identities. Confirm the
recorded build/runner passed rather than relying on this handover.

## Principal task: one narrow exact-source Gate Z obligation

Review paper-to-Lean fidelity before attempting freeze:

- RawTrace.Extends is indexed by actual appended board plies and full raw
  State endpoints. refl retains the SAME state at zero. snoc uses the frozen
  RawBoardStep, whose witness is an actual Move, source legality proof, and
  exact append equality; full prior history is retained, including on reset.
- RawClock.clock_le_extension proves, for EVERY Extends n s t,
  clock t.trace ≤ clock s.trace + n. Induction uses the unchanged frozen
  append_clock_le, addition monotonicity and transitivity; resets are included.
- Different histories with equal erased boards are not interchangeable.
  No arbitrary seeded clock, ReachK surrogate, endpoint-clock premise,
  material/side restriction or earlier-terminal filter occurs.
- The complete new bundle boundary is exactly the two modules
  Rules/RawTrace/ExtensionDefinitions.lean and Rules/RawClock/ExtensionBound.lean,
  with one public main declaration. Imports, shared definitions and constructor
  signatures are part of the reviewed meaning. Both prior frozen sources stay
  unchanged. No redundant prefix-extraction or exact-length theorem was claimed.

Publish no new proof source merely to re-anchor unchanged code. Use ONE NEW
fresh GitHub Gate Z clone detached at the OWN exact SHA above; no formal/.lake
before build. Run full lake build followed by COMPLETE AxiomCheck. Inspect the
new exact statement and axiom report (only propext/Classical.choice/Quot.sound
subset). Retain full logs, exits/timings, UTC, official Lean identity, all
source/transitive hashes and clean-source identities. Compare against actual
S038 Gate F output and exact source, not only against current main's aggregate
runner: future additive entries must not rewrite historical evidence.

Only on observed success freeze EC-C025 as the next unused EC-T ID (expected
EC-T0023; inspect actual ledger first). Write an immutable manifest citing this
own exact proof-source SHA, full module boundary, exact definitions/statement,
axioms, paper/audit links, trust boundary and fresh Gate Z evidence. Add exactly
one ledger row, preserving all earlier rows/manifests/source/evidence bytes.
If verification or fidelity fails, document the precise blocker; do not freeze,
rewrite prior modules or invent a successful result.

## Audit controls and semantic limits

Recheck n=0 same-state retention, one quiet ply, one zeroing move, mixed paths,
equal erased boards with different history, and continuation after an earlier
raw draw. General symbolic arguments suffice. Do not claim an initial-rooted
promotion/ep/castling full prefix was run unless actually constructed/verified.
Never remove adverse draw-ending replies to manufacture a win.

The bound is NOT sufficient-budget lifting. h+n<100 is a future certificate
HYPOTHESIS, not a universal KRK conclusion. No numerical mate bound, repetition
certificate, no-earlier-terminal FIDE admissibility, repetition-key correctness,
current/intended claim semantics, fivefold/75-move adjudicator, mate precedence,
full Layer A/B/C instance, holding/outcome, DTM/DTZ/WDL/Syzygy parity or
initial-position result follows. No material-class coverage upgrade from freeze.
No tablebase, engine, class enumeration, stored certificate or arbitrary-clock
KRK game witness. Classical result, no novelty claim.

## Verification and closeout

No Lean source change is expected. Preserve all prior candidate/frozen source,
papers/audits/evidence and ledger bytes (apart from the one new ledger row);
aggregate Lean imports/runner may gain additive entries only if actually needed.
Do not rerun unrelated diagnostic suites or other clean theorem verification.
Run the relevant ledger structure, preservation, evidence and document checks.
Update candidates, roadmap/README, session ledger and progress table. Write
sessions/S039_FREEZE_RAW_CLOCK_EXTENSION.md with actual evidence and the FULL
installed S040 prompt. Choose the next small obligation from actual results.
A possible follow-on is a narrowly audited raw prefix/one-more-ply budget
certificate under an explicit h+n<100 hypothesis, covering prospective defending
moves; it must still not claim repetition control or full rule-aware lifting.
Install a well-posed next prompt, not a numerical KRK assertion.
Commit, push session branch, merge/push main and compare remote SHAs. Distinguish
observed local/fresh-clone checks from hosted CI if it remains unobserved.

## Cloud activation

Use runtime skill if available; inspect environment/network policy and reuse
existing Git proxy authentication. Official unmodified core Lean 4.35.0, no new
dependency. Export ELAN_HOME=/workspace/.tools/elan and prepend its bin directory
to PATH. Lake runs in formal/, Python at repo root. One fresh build at a time;
keep TLS/checksum verification. Existing environment suffices unless actual
evidence establishes a missing prerequisite.
