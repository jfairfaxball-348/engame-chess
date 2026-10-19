# S032 — KRK rule/history and distance-layer design

Date: 2026-10-19 (Europe/London). Base main:
`ab54fc8de2d0c1c2777808cb37812991978d0def`. Branch:
`session/s032-krk-rule-distance`, existing isolated checkout.

The initial local prompt was S031, but the required all-branch fetch found S031
already committed and merged remotely. Main was fast-forwarded, no earlier
unmerged work remained, and the newly active S032 prompt was executed instead.
No S031 certification was repeated and no duplicate frozen IDs were created.

## Result: design completed, mathematical coverage unchanged

[Specification](../research/KRK_RULE_DISTANCE_SPEC.md) and
[same-agent design audit](../audits/EC-C022_RULE_LAYER_DESIGN.md) define the next
layer without altering any frozen game definition. This is a normative and
mathematical design, **not** a new Lean theorem or completed FIDE WDL model.

- State: existing Position plus a derived halfmove counter and full preceding
  legal move/position history, including the initial and current endpoints.
  Strict prefixes cannot already have ended the game. Raw arbitrary flags are
  distinguished from history-derived castling rights and effective legal ep.
- Repetition: same board/turn/rights/effective legal ep key, including pinned-ep
  and blocked-castling concerns. Its correspondence to FIDE is an explicit
  future proof obligation; current legal-move-list equality alone is insufficient.
- Updates: pawn moves/captures reset h, other moves increment it; actual rook
  capture yields dead KK, not a successful mate-distance event. Full history is
  retained after zeroing; compression requires a separate theorem.
- Terminals/actions: board mate, stalemate/deadness, automatic fivefold/75-move
  draws, and optional current OR intended-move threefold/50-move claims. Claims
  terminate the current game before executing an announced move. Mate on the
  75-move threshold takes precedence. The model uses fresh pre-touch decisions
  with correct claims; physical/procedural penalties, resignation, agreement
  and thinking-clock forfeiture are explicitly outside this named layer.
- Winning: finite board-ply recurrence with existential winner choices,
  universal nonempty defender moves, and no defender draw-claim option when
  winning. Holding is separately specified; determinacy and full-game
  termination are not silently assumed.
- First distance target: a finite **upper bound in plies to named mate**, not
  an exact DTM or a DTZ. Mate at zero, one for a mating move, and no finite bound
  for draws/nonwins are explicit. Min/max, rule dependence and future parity
  obligations are stated; exact Syzygy conventions were not asserted.

EC-C022 is registered **PROPOSED** only. Its precise generic target is
`RuleMateWithin σ n s → MateWithin σ n (erase s)`, then the existential forcing
corollary. The interface requires ongoing step soundness, lifting of EVERY raw
legal reply including draw-ending children, and ongoing nondeadness. A paper
induction is supplied, with a design audit; neither Gate L/F certification nor
a concrete FIDE instantiation is claimed. The first bridge does not need a new
numerical KRK theorem or the full history implementation.

The converse requires more data. A later sufficient lifting plan uses an
explicit clock-free tree with bound n, conservative h+n<100, and full-history
key counts at most two at every tree node, including every defending announced
move child. No such universal KRK certificate or numerical bound is proved.
Claim windows, dead-KK captures, repetition cycles, protected-rook stalemate and
same-board/different-history examples are retained as adversarial controls.
Local suffix examples without a full compatible prefix are labelled accordingly;
no new reachability or diagnostic success is claimed for them.

## Actual source reading and verification

The cloud runtime skill reported a current connected instance and enforced
unrestricted HTTP policy; `/etc/codex/network-policy.json` was inspected. Existing
Git HTTPS authentication worked; no credentials were requested or exposed.
The FIDE authoritative 2023 Laws were fetched with TLS verification enabled:
<https://handbook.fide.com/chapter/E012023>. Articles 5 and 9, including intended
claims and threshold mate, were read from the actual available text.

Retrieval: 2026-10-19 13:14:54 UTC / 14:14:54 Europe/London. HTML SHA-256:
`c5b1692a0614d4bd93fe9238287b9ab7d1f47320934d5df3be113523906c476f`.
[Metadata](evidence/S032/fide-source.json) records covered articles and scope.
The tracked specification paraphrases the clauses; full fetched text remains
a temporary workspace artifact. No engine, tablebase, derived position
valuation or per-position certificate was consulted.

Observed checks:

- `python3 scripts/validate_ledger.py`: **19 valid frozen rows**, structure only.
- Preservation check: **291** existing formal/theorem/script/test/proof/audit/
  prior-evidence files byte-identical to base main, including the ledger and
  all frozen manifests. Existing Lean and Python sources are unchanged.
- Source retrieval/hash consistency, local authored-document links, stable
  progress table, complete installed S033 prompt and `git diff --check` checked.
- **No Lean build or new formal check run:** this is documentation-only design.
  Historical diagnostic suites and clean-clone certifications were not rerun.
  No new executable test or numerical distance result is claimed.
- Hosted CI **unobserved**; publication is not a CI success claim.

[Validation evidence](evidence/S032/validation.log) and
[preservation record](evidence/S032/preservation.log) retain the checks. Candidate,
roadmap, README and session ledger reflect design/proposed status only. No prior
ledger row, manifest, frozen module or proof evidence changed. Nineteen frozen
bundles are not nineteen solved material classes.

## Next task and publication

S033 targets only the small parametric projection theorem and existential
corollary, in new definition/proof modules with explicit interface proof fields.
Concrete rule/history correctness, holding/outcome coverage, procedural
extensions, sufficient-budget lifting, numerical DTM/DTZ and full FIDE/Syzygy
parity remain open. The next agent must not turn those obligations into extra
axioms or report a concrete FIDE result from a generic interface theorem.

This documentation commit is to be pushed on the session branch, fast-forwarded
onto main, pushed, and compared with the remote SHA under AGENTS publication
instructions. Its exact base is recorded above; the closing commit's immutable
Git identity carries this report without a circular self-reference.

## Repeatable progress table

| Endgames / target | Progress | Remaining |
|---|---|---|
| K vs K | Draw proved and frozen | — |
| K+B vs K | Draw proved and frozen | — |
| K+N vs K | Draw proved and frozen | — |
| K+R vs K | Dead/live and clock-free forcing classification frozen | FIDE rule/distance parity |
| K+Q vs K | Open in this project | General proof and formal verification |
| K+P vs K | Open in this project | General proof and formal verification |
| All four-piece endgames | Open in this project | Every material class and legal position |
| All five-piece endgames | Open in this project | Every material class and legal position |
| All six-piece endgames | Open in this project | Every material class and legal position |
| All seven-piece endgames | Open in this project | Every material class and legal position |
| **Full Syzygy parity (through seven pieces)** | **Open** | **Complete class coverage, 50-move WDL and DTZ parity** |

Session change: S032 specified the rule/history and distance layer and proposed the next projection lemma; mathematical coverage and the nineteen frozen bundles are unchanged.

## Full installed next-session prompt

````markdown
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
````
