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
