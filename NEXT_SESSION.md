# NEXT SESSION — S034: Freeze the abstract rule-layer projection

**Owner instruction:** Execute when the owner says “run next session” or pastes/links
this prompt. Follow `AGENTS.md`: fetch ALL remote branches, merge earlier
unmerged session work, advance to latest main and use its active prompt. Use
the existing checkout; finish committed, pushed and merged to main without
force. Publication is authorised.

**Closing report:** update `docs/SESSION_PROGRESS.md` and copy its complete stable
progress table into both the written closeout and final reply. Full Syzygy parity
is the last row; the session delta follows the table. Bundles are not classes.

## Starting point and required reading

Nineteen bundles remain frozen. S033 proves EC-C022 in the precise abstract
interface from S032. Read the charter, proof protocol, current roadmap and
candidate register, S032 specification §5, S033 paper/audits/closeout/evidence,
and EC-T0008's frozen semantics first.

Published S033 proof-source anchor:
`55affd0a7a3f2e77335f4964ae4fbc1edbe19e05`.

- `formal/EndgameChess/Rules/HistoryLayer/Definitions.lean`:
  Layer, Goal, RuleMateWithin, RuleForceMate.
- `formal/EndgameChess/Rules/HistoryLayer/Projection.lean`:
  `EndgameChess.Rules.HistoryLayer.ruleMateWithin_project`.
- `formal/EndgameChess/Rules/HistoryLayer/ForcingProjection.lean`:
  `EndgameChess.Rules.HistoryLayer.ruleForceMate_project`.

Paper: `proofs/EC-C022_RULE_LAYER_PROJECTION.md`. Audits:
`audits/EC-C022_RULE_LAYER_PAPER.md` and `EC-C022_RULE_LAYER_LEAN.md`.
Exact-source Gate F is recorded in `sessions/evidence/S033/`; inspect actual
results rather than infer success from this prompt.

## Exact claim and limits

For every universe-polymorphic state type, a Layer has erase, BoardStep,
Ongoing, CanClaim, and ordinary PROOF FIELDS at every ongoing state:

(A) every BoardStep projects to kernel Legal;
(B) EVERY raw Legal successor lifts to a BoardStep with the same erased target;
(C) Ongoing implies not DeadK at the erasure.

The recurrence has exact named board MateGoal at zero/terminal branches,
existential winner moves, and nonempty universal defender replies with no
available defender claim. Claims are draw outcomes, not board-ply steps.
Draw-ending successors may not be pruned. Layer data are independent of colour
and budget; no field assumes a winning continuation.

The first theorem projects RuleMateWithin σ n s to frozen MateWithin σ n
(erase s), retaining the IDENTICAL n. The second extracts/reuses a uniform
witness to project RuleForceMate to frozen ForceMate. Both colours and all
states are quantified. This is a generic conditional interface theorem: it is
NOT an implementation/verification of FIDE histories or a converse, numerical
KRK bound, holding theorem, full WDL/DTZ or Syzygy convention result. Freeze the
abstract boundary exactly as written, without upgrading its concrete meaning.

## Principal task: separate Gate Z for EC-C022

1. Review the paper/audits against all interface fields, the recurrence and
   exact two source statements. If correction is needed, use NEW source/version
   and obtain corresponding Gate F evidence; never inherit a previous SHA's
   verification for changed proof bytes. Otherwise keep all proof sources fixed.
2. Make ONE NEW fresh GitHub clone at the full S033 SHA; assert no formal/.lake
   before `lake build`. Do not reuse the S033 Gate F clone or relabel its logs.
   One full run serves this one bundle; do not repeat older certifications.
   Retain commands/preconditions, full build, exact AxiomCheck outputs,
   toolchain identity, source hashes, forbidden-token scan and actual exit codes.
3. Inspect both main declarations and interface/definition signatures. Allowed
   axiom subsets: propext, Classical.choice, Quot.sound. No proof escapes,
   sorryAx, native reduction or extra assumptions. Preserve the field B scope
   over ALL raw legal replies, nonempty weak branch and exact same ply budget.
4. If eligible, freeze one coherent new bundle at the next free ID (expected
   EC-T0020, verify ledger first). The immutable manifest must record the full
   proof-source SHA, all THREE COMPLETE modules (including shared definitions),
   transitive source hashes, both exact statements, rules/semantic boundary,
   attribution, same-agent review provenance and observed NEW Gate Z evidence.
   No claim of independent external review or concrete FIDE instantiation.
5. Only then append the new FROZEN ledger row with the existing schema. Keep all
   earlier rows/manifests/source/evidence byte-identical. Update EC-C022, status,
   roadmap, session ledger and progress table. Run relevant ledger-validator
   checks and preservation/coverage checks. Do not run unrelated diagnostic
   suites or add a large example expansion. Hosted CI is unobserved unless
   actually checked; a push alone proves nothing about CI.

This is the separate freeze of a now-fixed interface before concrete layers
are built on it. No new mathematics or change of material class is required.
No engine, tablebase, derived evaluations or class-wide enumeration is allowed
to supply a proof. Any fixed controls remain supplementary.

## Following concrete history-layer obligation

Install S035 around ONE small additive concrete component from S032, rather
than claiming that the entire FIDE layer now follows. Prefer a legal move-trace
append interface: define a finite kernel trace with an explicit endpoint and
prove that an arbitrary raw Legal endpoint move appends to a trace and projects
back soundly. Keep that raw kernel-trace notion separate from histories that
have not already ended under FIDE draw rules. Establish the exact definition
and paper audit before formalisation; do not prune immediate-draw endpoints.
Use the actual freeze outcome to choose the smallest sound obligation.

The remaining full-history admissibility, effective-ep repetition equivalence,
clock zeroing updates, terminal/claim correctness, concrete Layer instantiation,
sufficient-budget lifting, numerical distances and FIDE/Syzygy parity must stay
explicitly open. A raw trace append theorem does not by itself settle those.
Frozen game definitions and the abstract interface must remain unchanged;
concrete extensions go in NEW modules.

Write `sessions/S034_FREEZE_RULE_LAYER_PROJECTION.md` with exact verification,
source/ledger effect, complete progress table and the FULL installed S035
prompt. Commit/push branch, merge main, push main and verify remote SHA.
If certification fails, preserve the concrete reason and correct status; do not
create a FROZEN row before the actual checks pass.

## Cloud activation

Use the runtime skill for the current environment. Existing checkout, no new
worktree. `export ELAN_HOME=/workspace/.tools/elan; export PATH="$ELAN_HOME/bin:$PATH"`.
Lake commands in `formal/`, Python at repository root. Official Lean 4.35.0,
core only, no dependencies or host shim; keep TLS/checksum verification enabled.
One required fresh build at a time; prior S031 concurrent builds hit that host's
memory limit, so inspect current resources if any actual failure occurs.
