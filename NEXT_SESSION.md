# NEXT SESSION — S033: Prove the finite-budget rule-layer projection

**Owner instruction:** Execute when the owner says “run next session” or pastes/links
this prompt. Follow `AGENTS.md`: fetch ALL remote branches, advance to latest
main, merge any earlier unmerged session work, and read the active prompt there.
Use the existing checkout; end committed, pushed and merged to main without
force. Publication is authorised.

**Closing report:** update `docs/SESSION_PROGRESS.md` and reproduce its complete
stable table in the written closeout AND final reply, full Syzygy parity last,
followed immediately by the session delta. Counts are bundles, not material
classes or completion percentages.

## Starting point

Nineteen frozen bundles, unchanged by S032. EC-T0019 already proves arbitrary
strong-turn legal-arrival KRK clock-free forcing and the weak terminal/capture
classification. S032 is a DESIGN session, not a new FIDE/DTM/DTZ theorem.

Read the charter, proof protocol, current roadmap, S032 closeout,
`research/KRK_RULE_DISTANCE_SPEC.md`, `audits/EC-C022_RULE_LAYER_DESIGN.md`,
`formal/EndgameChess/Rules/ForcingDefinitions.lean`, `ForceMate.lean`, and
EC-T0008/EC-T0019 manifests first. S032 retrieved the authoritative FIDE 2023
source at https://handbook.fide.com/chapter/E012023; metadata and SHA are in
`sessions/evidence/S032/fide-source.json`. Reuse that rules reading; the generic
projection itself does not require implementing the entire FIDE layer.

## Principal task: EC-C022 only

Prove the generic SAME-BUDGET erasure theorem below. It is deliberately a small
parametric theorem, not a concrete history/clock implementation or a numerical
KRK bound. EC-C022 is currently PROPOSED. Write an exact standalone paper proof
and an adversarial local/fidelity audit before Lean; advance statuses only when
those gates pass.

Define an additive abstract layer over a type X with:

- `erase : X → Position`;
- `BoardStep : X → X → Prop` (actual board moves, never successful draw claims);
- `Ongoing : X → Prop`;
- `CanClaim : X → Prop` (current OR intended-move correct claim availability).

Require interface proofs, at every ongoing state s:

(A) BoardStep s t implies `Legal (erase s) (erase t)`.
(B) EVERY r with `Legal (erase s) r` lifts to some t with BoardStep s t
    AND erase t=r. Draw-ending successors MUST be retained, not pruned.
(C) Ongoing s implies `¬ DeadK (erase s)`.

These are ordinary quantified hypotheses or proof fields of an interface,
NOT new Lean axioms and NOT claims that a concrete FIDE layer already meets
them. X, erasure and steps do not depend on winning colour or budget. Define
`Goal σ s := MateGoal σ (erase s)` and the additive recurrence:

```
RuleMateWithin σ 0 s := Goal σ s
RuleMateWithin σ (n+1) s := Goal σ s OR
  (Ongoing s AND
    (((erase s).turn=σ AND ∃t, BoardStep s t AND RuleMateWithin σ n t) OR
     ((erase s).turn=σ.opp AND NOT CanClaim s AND
      (∃t, BoardStep s t) AND
      ∀t, BoardStep s t → RuleMateWithin σ n t)))
RuleForceMate σ s := ∃n, RuleMateWithin σ n s
```

Winning colour can decline a draw claim. Every defender claim prevents forced
mate; every defending board move is universal and the reply set is nonempty.
A claim ends in draw at zero BOARD plies, not a hidden extra move. Automatic
terminal draws are represented by failure of Ongoing and absence of Goal in
a future concrete implementation; no false FIDE instantiation is permitted.

Exact targets, for all X, layer parameters/proofs A–C, σ, n and s:

1. `RuleMateWithin σ n s → MateWithin σ n (erase s)`.
2. `RuleForceMate σ s → ForceMate σ (erase s)`.

Induct on n. The strong case projects its chosen successor by A. The weak case
projects nonemptiness by A, and uses B for an ARBITRARY raw Legal reply before
induction. C supplies the frozen nondeadness guard. The terminal branches have
exactly the frozen MateGoal. Do not replace the same-budget conclusion by mere
cooperative reachability or assume the desired projected strategy as a premise.

## Boundaries and review controls

- Never edit frozen Position, Legal, MateWithin, ForceMate, modules, manifests
  or prior ledger rows. Use NEW definition and theorem modules (e.g.
  `Rules/HistoryLayer/Definitions.lean` and `Projection.lean`), separate namespace
  if helpful, then additive aggregate imports/AxiomCheck entries.
- All raw legal defending replies must lift, including immediate draw children.
  Omitting them can manufacture a false forced win. Include this failure in
  the audit. Do not add an “all projected replies already win” interface field.
- No converse: a weak player at h=99 can claim by an intended nonzeroing move;
  history may already allow threefold. Finite clock-free rank supplies neither
  a numeric clock budget nor a repetition certificate. The S032 sufficient
  lifting plan is FUTURE work, not an assumption smuggled into this theorem.
- No holding/determinacy theorem, repetition-key correctness, history compression,
  procedural adjudication, full FIDE WDL, numerical DTM, DTZ or Syzygy convention
  result is in this session's scope. No engine, tablebase or enumeration oracle.
- The abstraction is nonvacuous only as an interface theorem; if a small
  identity/no-claim sanity instance is useful, state its artificial scope.
  It does not instantiate FIDE's draw rules. Avoid a large example/test expansion.

## Verification and publication

Run incremental builds only for the new modules/importers, add BOTH main
statements and axiom reports to AxiomCheck, and inspect their exact quantifiers.
Only propext, Classical.choice, Quot.sound subsets are allowed. No proof escapes.
For Gate F, commit and PUSH the exact proof source, make ONE NEW fresh GitHub
clone detached at that full SHA with no formal/.lake before `lake build`, and
retain full build, statements, axiom counts, hashes, toolchain and forbidden scan.
Do not reuse prior Gate F/Z clones. Run only relevant existing checks; preserve
frozen source and ledger bytes. Hosted CI counts only if actually observed.
S031 experienced an 8 GiB memory limit during concurrent clean builds; keep this
single required build bounded, and diagnose any actual resource failure.

No new ledger row is expected (Gate Z is separate). Write
`sessions/S033_RULE_LAYER_PROJECTION.md` with exact source SHA, statuses,
observed checks, limits, ledger effect and complete progress table. Install a
FULL S034 prompt around the next concrete history-layer obligation or a separate
freeze, chosen from the actual outcome; do not quietly jump to complete KRK
rule-aware outcomes. Include that full prompt in the closeout. Update candidate
register/roadmap/current status, commit/push branch, merge main, push main and
verify remote SHA. If a gap appears, preserve the exact failed implication and
keep the candidate in the appropriate earlier stage.

## Cloud activation

`export ELAN_HOME=/workspace/.tools/elan; export PATH="$ELAN_HOME/bin:$PATH"`.
Lake commands run from `formal/`; Python from repository root. Official unmodified
Lean 4.35.0, core only, no dependencies or host shim. Keep TLS/checksum checks.
Use the runtime skill for the current environment; no new worktree is needed.
