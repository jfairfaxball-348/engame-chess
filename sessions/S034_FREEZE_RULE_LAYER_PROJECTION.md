# S034 — Freeze the abstract rule-layer projection

Date: 2026-10-19 (Europe/London). Base main `7d36b8f8a94576e906ec5f50e9fc025e6df2c238`. Existing checkout on
`session/s034-freeze-rule-layer`. All-branch fetch found no earlier unmerged
remote work; latest main's S034 prompt was executed. Publication is authorised.

## Result and exact ledger effect

**EC-C022 frozen as [EC-T0020](../theorems/frozen/EC-T0020/v1.md)**. One new
coherent bundle, two declarations, ALL three complete HistoryLayer modules
including definitions/proof fields. Ledger: **19 → 20 bundles**, not classes.
Earlier rows/manifests, all Lean sources, papers/audits and prior evidence
remain unchanged; the new ledger row is appended to the original bytes.

The finite-budget theorem projects RuleMateWithin L σ n s to frozen MateWithin
σ n (L.erase s), with the IDENTICAL n. The forcing corollary reuses that uniform
witness. Every state type, colour and state is quantified. Ordinary ongoing
proof fields require move soundness, coverage of EVERY raw Legal successor,
and erased nondeadness; none assumes a winning continuation. Exact named board
mate, nonempty universal defending replies and the no-defender-claim guard
remain explicit. Draw-ending children cannot be pruned. No correction or
new mathematical theorem was needed for the freeze.

S034 reviewed the S033 paper, adversarial/fidelity audits, all interface fields,
recurrence and both exact source statements. Same-agent review, not external
independent review. Classical reachability-game simulation, no novelty claim.
This is NOT a concrete FIDE history/clock/repetition implementation, converse,
holding/determinacy, numerical KRK distance, DTM/DTZ/WDL/Syzygy or initial-
position result. No new material-class coverage is claimed.

## Actual verification

Published proof-source: **`55affd0a7a3f2e77335f4964ae4fbc1edbe19e05`**. ONE NEW GitHub checkout
`/tmp/engame-s034-gate-z`, detached at the full SHA; no formal/.lake BEFORE
build. S033's Gate F directory/logs were not reused as Gate Z.

- Full `lake build`: **54 jobs, exit 0, 371.256s**.
- Full `lake env lean AxiomCheck.lean`: exit 0, exact interface/definition
  signatures and both main statements inspected. **261 reports** allowed:
  230 standard-three, 18 propext/Quot.sound, 8 propext, 5 axiom-free.
  Both bundle declarations use the standard three only. No sorryAx/native
  reduction or extra assumption. Whole-run counts are not new-theorem counts.
- Verified UTC `2026-10-19T13:52:54Z`. New report byte-identical to prior Gate F;
  all anchor Lean/build source bytes match. Zero forbidden tokens in three
  modules; full source and transitive dependency hashes in the manifest.
- Official unmodified core Lean 4.35.0, release
  `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, no dependencies or host shim.
  Runtime skill reported current connected/enforced network context; existing
  Git proxy authentication worked; TLS/checksum verification unchanged.
- Existing ledger-validator tests: **6 passed**. Structural validation: **20
  valid FROZEN rows**. Record validation: **366 protected prior tracked files
  unchanged**, prior ledger bytes retained as a prefix, exactly EC-T0020
  appended, complete source/statement/hash coverage and local links checked.
  Results are retained in [Gate Z evidence](../theorems/frozen/VERIFICATION-S034/README.md).
  These check records, not mathematics. No Python/Lean implementation changed;
  unrelated historical diagnostic suites were not rerun. No new diagnostic
  example or source evaluation certifies this generic theorem.
- Hosted CI **unobserved**; local verification and publication are separate.

No engine/tablebase, derived evaluation, retrograde value or class-wide
enumeration supplied a proof. Evidence includes exact command exit/timing
records, preconditions, complete logs, toolchain identity and reproducible
verification/record validators. No successful fresh build was repeated.

## Next obligation and publication

S035 targets one concrete RAW move-trace append interface retaining actual
ordered moves and endpoint positions. It must distinguish raw kernel traces
from histories that have not already ended under FIDE rules, and keep every
legal child, including a future immediate-draw endpoint. It is not a full
HistoryLayer instantiation. Concrete admissibility, clock updates, repetition
keys, claims/terminals, sufficient-budget lifting and numerical distance remain
open, as does full FIDE/Syzygy parity.

The closing commit carries this manifest/evidence/report and the full S035
prompt without changing any proof-source bytes. It is pushed on the session
branch, fast-forwarded to main, pushed, and remote SHA compared under AGENTS.
The immutable proof-source anchor above avoids any circular reference to the
commit containing its own ledger row.

## Repeatable progress table

| Endgames / target | Progress | Remaining |
|---|---|---|
| K vs K | Draw proved and frozen | — |
| K+B vs K | Draw proved and frozen | — |
| K+N vs K | Draw proved and frozen | — |
| K+R vs K | Dead/live, clock-free forcing and generic projection frozen | Concrete FIDE history layer and distance |
| K+Q vs K | Open in this project | General proof and formal verification |
| K+P vs K | Open in this project | General proof and formal verification |
| All four-piece endgames | Open in this project | Every material class and legal position |
| All five-piece endgames | Open in this project | Every material class and legal position |
| All six-piece endgames | Open in this project | Every material class and legal position |
| All seven-piece endgames | Open in this project | Every material class and legal position |
| **Full Syzygy parity (through seven pieces)** | **Open** | **Complete class coverage, 50-move WDL and DTZ parity** |

Session change: S034 froze EC-C022 as EC-T0020 (20 bundles); mathematical coverage is unchanged and concrete FIDE rule/distance work remains open.

## Full installed next-session prompt

````markdown
# NEXT SESSION — S035: Concrete raw move traces and complete append lifting

**Owner instruction:** Execute when the owner says “run next session” or pastes/links
this prompt. Follow `AGENTS.md`: fetch ALL remote branches, merge any earlier
unmerged session work, advance to latest main and use its active prompt. Work
in the existing checkout; finish committed, pushed and merged to main without
force. Publication is authorised.

**Closing report:** update `docs/SESSION_PROGRESS.md`; copy the complete stable
table into the written closeout and final reply, full Syzygy parity last and
the session delta directly below. Frozen bundle counts are not solved classes.

## Starting point and reading

S034 froze EC-C022 as EC-T0020, bringing the register to twenty bundles. Verify
that actual outcome from `sessions/S034_FREEZE_RULE_LAYER_PROJECTION.md` and
`theorems/frozen/EC-T0020/v1.md`; do not infer a successful freeze just from this
prompt. The exact abstract proof source is
`55affd0a7a3f2e77335f4964ae4fbc1edbe19e05`.

Read the charter, proof protocol, current roadmap, S032 specification
`research/KRK_RULE_DISTANCE_SPEC.md` (especially history/transition sections),
S033 paper/audits, S034 closeout/manifest, frozen kernel Legal/play/ReachK
semantics and the frozen HistoryLayer interface. The authoritative FIDE 2023
rules retrieval is recorded in `sessions/evidence/S032/fide-source.json`.
No new rules claim is needed for the raw-trace lemma; additional clause reading
is required only if it is used to make a new normative assertion.

EC-T0020 is conditional: ongoing BoardStep soundness, coverage of EVERY raw
Legal reply and ongoing nondeadness imply same-budget rule forcing projection.
It does NOT instantiate actual FIDE histories, claims, clocks or repetition.
EC-T0019 still supplies only the clock-free KRK forcing classification.

## Principal task: one raw kernel-history component

Design and prove a small concrete move-trace append interface. Register EC-C023
only after fixing the exact statement in a standalone paper and adversarial
audit, BEFORE Lean. No ledger row is expected in this mathematics session.

Use NEW modules/namespace, without editing any frozen definition or proof.
Choose a data representation that retains actual ordered MOVES and their
successive kernel positions, with an explicit endpoint. A proof of frozen
`Arisen q`/`ReachK initial q` alone is insufficient: it is a Prop, not a stored
trace for computing later clock updates and repetition counts.

One possible design is an indexed Type of traces rooted at `initial`, with an
empty constructor and a snoc constructor carrying a Move and a proof that it
isLegal at the current endpoint. Bundle the endpoint and its trace into a state.
Alternatively use a move list plus replay validity and endpoint proofs. If a
general starting position is parameterised, keep it explicit and state the
`initial` specialisation separately; never silently replace global history by
an arbitrary starting board. Empty and nonempty traces must be unambiguous.

Define erase(s) as the concrete endpoint. Define an append operation for every
m with `isLegal (erase s) m = true`, retaining the prefix and exactly that m.
The appended endpoint must equal `play (erase s) m`. Define RawBoardStep by
such an actual one-move append, not by merely relating any two erased boards.

Precise principal obligations:

1. Append preserves the chosen trace validity and returns the exact played
   endpoint (with ordered prefix/move retention, not just an existential path).
2. **Soundness:** RawBoardStep s t implies kernel Legal (erase s) (erase t).
3. **Complete raw-reply lifting:** for EVERY state s and EVERY r,
   `Legal (erase s) r → ∃t, RawBoardStep s t ∧ erase t=r`.
   Extract the actual Move witness from Legal; do not assume a chosen strategy
   or remove successors based on their result.

A short endpoint reachability/turn or trace-length lemma may support these
statements if needed; avoid expanding into unrelated history machinery. The
root/append definitions should make the prefix retained and one additional
board ply clear. State exactly what counts as a stored move, position endpoint
and proof-only field. General proof, not class-wide replay/enumeration.

## Critical semantic boundary

Call the object a **RAW kernel move trace**. It proves that each recorded board
move satisfies the existing Legal relation. It does NOT prove that actual FIDE
play had not previously ended. In particular, these objects may record moves
past an earlier automatic draw or a dead-position draw whenever raw Legal
allows them. No clock, repetition test or Ongoing classifier is yet included.

The unrestricted lifting theorem must retain an endpoint that would immediately
draw under a future history-aware classifier. Later FIDE admissibility must
restrict which PARENT prefixes may continue, while allowing a terminal child;
it must not prune adverse legal replies to manufacture forcing. A raw trace
append theorem is only a concrete step toward interface fields A/B, not a full
HistoryLayer instance or a proof of field C/claim correctness.

Do not initialise KRK with an arbitrary flags/clock/count snapshot and call it
an initial-position history. An arbitrary-flags clock-free KRK theorem does not
supply a compatible-prefix witness for every such snapshot.

Retain audit controls: empty trace/root, all turn orientations, genuine Move
witness and target equality orientation, full prefix retention, terminal-child
coverage, no “all replies already win” hypothesis, no confusion of a data
trace with proof-irrelevant ReachK. Fixed local controls are optional and
supplementary; do not add a large test expansion or artificial passing tests.

Explicitly OUT OF SCOPE: full no-earlier-terminal FIDE histories, halfmove
zeroing semantics, effective-ep repetition-key equivalence, current/intended
claim rules, terminal precedence proofs, holding/determinacy, sufficient-budget
lifting, a numeric KRK bound, DTM/DTZ/Syzygy convention parity, another material
class or the initial-position value conjecture. Preserve these obligations in
status and the following prompt. No engine/tablebase/oracle evaluations.

## Verification and publication

Follow Gate L/F. Add main declarations to AxiomCheck, inspect exact types and
allowed axiom subsets (propext, Classical.choice, Quot.sound only). Run only
new modules/importers incrementally. For Gate F, commit and PUSH the exact
proof-source SHA, then use ONE NEW fresh GitHub clone with no formal/.lake
before `lake build`; retain complete build, axiom/statements, source hashes,
toolchain and forbidden scan. Do not reuse prior Gate F/Z clone evidence.
Keep all existing frozen sources, manifests, earlier ledger rows and prior
evidence byte-identical. Run relevant existing structural checks. No hosted
CI claim without observing its result. No new ledger entry at Gate F.

Write `sessions/S035_RAW_TRACE_APPEND.md`, update candidate/roadmap/status and
session ledger according to the actual result, and include the full progress
table and FULL installed S036 prompt. Choose S036 from the actual next narrow
obligation (separate freeze or one clock/history component), retaining the
remaining concrete FIDE layer and distance gaps. Commit/push branch, merge main,
push main and verify remote SHA. If the representation exposes a genuine gap,
preserve the exact failed implication and avoid upgrading the candidate.

## Cloud activation

Use the runtime skill, existing checkout and pinned official Lean 4.35.0.
`export ELAN_HOME=/workspace/.tools/elan; export PATH="$ELAN_HOME/bin:$PATH"`.
Lake commands in `formal/`, Python at root. Core only, no dependencies or host
shim. Keep TLS/checksum verification enabled; one required fresh build at a time.
````
