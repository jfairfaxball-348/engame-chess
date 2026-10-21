# Protocol — propose, prove, formalise, freeze

## Admission: direct obligation before new research

Apply the [repository-wide direct-obligation rule](../AGENTS.md) for the active
target, including future targets after KRK. Before new research or formalisation,
put this short admission record in the session document or linked proof:

- **Target and priority:** the active material class and highest-priority open
  closure obligation being attacked.
- **Exact gap:** the missing quantified statement, input domain and criterion
  that would close or materially narrow that obligation.
- **Direct contribution:** the proposed work's role in that proof and the
  outcome/distance coverage or quantitative improvement it would establish.
- **Necessity, if foundational:** the named blocked proof step, smallest needed
  lemma, why existing results fail, and its explicit use in the chosen direct
  route. General usefulness alone does not admit a prerequisite.
- **Return criterion:** when the prerequisite/local case/diagnostic ends and
  the direct proof resumes. Further prerequisite work needs its own necessity
  record; no automatic library-building sequence.

Do not replace a hard quantified obligation with isolated examples, generic
equivalences, reusable infrastructure or theorem-count milestones. Necessary
foundations and necessary cases are allowed, with the above dependency made
concrete. Required proof and verification gates remain mandatory for admitted
results; passing a gate does not itself advance material-class coverage.

At closeout, compare the actual result with this admission record. Name each
closure obligation closed, narrowed or unchanged and distinguish supporting
work from newly covered inputs. The chart must expose the immediate blocker;
unchanged headline gaps must be reported as unchanged. Owner-directed governance
or tooling is recorded separately and creates no mathematical claim.

## Gate P: proposed
Record a theorem candidate with unique ID, exact board/rules assumptions, quantifier order, precise result type and known counterexample risks. Status `PROPOSED`. No theorem-ledger row is required for a candidate: use `research/CANDIDATES.md`.

## Gate L: locally verified mathematics
Before touching Lean, write a standalone proof in `research/` or `proofs/` with:
- Unambiguous definitions for every symbol; distinguish reachability from play stopped by rules.
- Proof of required lemmas, including preservation of legality under every relevant move.
- Adversarial counterexample search: illegal placements, boundaries, side-to-move, path length zero, opponent cooperation, definitions of check/checkmate, and all declared rules.
- An independent audit note listing attempted falsifications and outcomes.
- Source attribution. Classical results must not be described as novel.

Once every gap is resolved, mark the candidate `LOCAL_VERIFIED`; keep evidence and reviewer/session reference. **Computational evidence alone is insufficient.**

## Gate F: formal verification
Implement the exact local statement in Lean 4, preferably using mathlib if it decreases trusted code. Pin the `lean-toolchain` and `lakefile` dependency revisions as soon as a Lean project is introduced. The formal theorem must correspond to the prose statement: do not replace chess legality with a weaker surrogate without stating that reduction and proving it.

Required checks at the referenced commit:
- `lake build` successful in a clean reproducible checkout.
- No `sorry`, `admit`, unjustified `axiom`, `unsafe` proof escapes or fabricated proof tokens.
- `#print axioms <qualified_theorem_name>` inspected and recorded.
- Audit all imported axioms and the trusted kernel assumptions.
- Verify no incorrect coercion of a finite test or a tautology into the intended theorem.
- Save full build logs/toolchain revision and proof declaration name.

Set `FORMAL_VERIFIED` only once evidence exists.

### Re-checking obligations (incremental verification)
The library will hold many small proofs. They are **not** all re-verified on every commit.
- **One module per theorem** (`formal/EndgameChess/<Topic>.lean`). Definitions shared by several theorems live in their own modules and are imported.
- **Lean CI** (`.github/workflows/lean-build.yml`) runs only when `formal/**` changes. It restores the cached `formal/.lake`, so `lake build` rebuilds only the changed modules and the modules that import them.
- **What must be re-checked:**
  1. a new or edited proof module;
  2. every module downstream of a changed shared definition, frozen ones included, because the statement's meaning may have changed;
  3. everything, after a toolchain or dependency bump (the cache key changes).
  Nothing else is an obligation.
- **The full clean-checkout verification above** is a one-off at Gate F and again at Gate Z, for the theorem being certified only. It is not a per-commit duty for the rest of the library.

## Gate Z: freeze
Create an immutable theorem statement/proof manifest under `theorems/frozen/<ID>/` which records: ID, theorem statement and scope, rule edition, local proof audit, Lean source path/declaration, toolchain/dependency revisions, full verified **proof-source commit SHA**, axiom-check findings, clean build evidence, date and version. Then add a single `FROZEN` row to `theorems/LEDGER.csv`. Reference the already-created verified proof-source commit, avoiding a circular reference to the commit containing its own ledger row.

A frozen theorem's Lean module is **never edited**. A correction is a new module or declaration plus a superseding manifest version. Shared modules a frozen theorem imports may change only if CI shows the frozen module still builds, with the same statement and the same axioms. Frozen proofs are not quietly edited or reclassified. If a defect is discovered, append a conspicuous correction/superseding record and update ledger history via an additional auditable commit. Git history is the permanent record; an optional immutable Git tag can additionally anchor each release.

**Versioning convention (owner decision, S009).** A strengthened or re-anchored form of a frozen result is frozen as a **new theorem ID** (e.g. the kernel-level K vs K result becomes EC-T0003). Its manifest states which earlier ID it strengthens, and how it supersedes that ID's trust boundary. Earlier ledger rows and manifests are never rewritten, and the ledger schema is unchanged (one row per ID). A genuine *defect* in a frozen theorem still requires a conspicuous correction record, as described above.

### Toolchain migration (owner decision, S020)
A toolchain bump is a **migration**, not a correction:
- Rebuild every frozen theorem from a clean clone on the new toolchain.
- Confirm that each statement's `#check` output is identical and that each main declaration's axioms stay within the standard three.
- Write a `vN+1.md` manifest per theorem, citing the migration commit, with shared logs under `theorems/frozen/MIGRATION-<session>/`.
- Earlier manifests and ledger rows are not rewritten.

If the migration needs Lean source edits to frozen modules (e.g. the module-system port Palomar requires), the same rule applies, plus per-module hashes in the new manifests.

## Permitted status transitions
`PROPOSED → LOCAL_VERIFIED → FORMAL_VERIFIED → FROZEN`. A falsified candidate becomes `REJECTED` *in the candidate register only*, with a concrete counterexample. A blocked claim remains in its current stage. No 'all clear' or theorem count until the actual checks have run.

## Session closeout
Each session must record: changes and links; proven, conjectured, computationally tested and blocked findings separately; checks actually run (or 'not run'); exact commit/tree state; ledger effect; and full text of the installed next session prompt. Never imply that a remote CI job passed just because a workflow file was committed.

Closeout is a checkpoint, not a pause. An owner instruction to continue until
the active target closes persists across sessions, commits, merges, freezes and
handoffs. Complete these records and continue the next necessary direct step;
do not end the run solely because a milestone finished. Preserve open proof
status honestly. Only actual closure, an explicit owner stop/scope change or a
concrete unavailable-input/external-action dependency supplies a stopping reason;
continue independent authorised direct work where possible. No new approval
gate is implied by an unfinished proof or a session boundary.

**Required progress table (owner instruction, 2026-10-19):** update [SESSION_PROGRESS.md](SESSION_PROGRESS.md) and reproduce its table in the written closeout and the final reply to the owner, including sessions with no mathematical change. Keep its columns and baseline rows in order, from K vs K through every material-size stage, with full Syzygy parity last. Preserve the distinction between frozen results, formal verification, partial coverage and open work. Follow the table with one sentence describing this session's change, or stating that mathematical progress is unchanged. The table is a reporting summary, not a theorem certificate or a substitute for Gates F/Z.
