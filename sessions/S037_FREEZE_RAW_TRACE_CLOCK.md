# S037 — Freeze raw trace and halfmove-counter components

Date 2026-10-19. Base main `5b42e5136e3d7fc77d6fe471c3a405603cfd57b6`; existing
checkout, branch `session/s037-freeze-raw-components`. All-branch fetch advanced
main to current origin/main; no earlier remote work remained unmerged.
Publication authorised by AGENTS.md and the installed S037 prompt.

## Result and fidelity review

**EC-C023 frozen as EC-T0021; EC-C024 frozen as EC-T0022.** Twenty-two theorem
bundles, not twenty-two solved material classes. Exactly two ledger rows added;
prior twenty rows, all prior manifests, papers, audits, evidence and all formal
source bytes remain unchanged. No new mathematical class or distance theorem.

Read charter/protocol/roadmap/candidates, S032 specification, S035/S036 papers,
paper/Lean audits, closeouts and actual Gate F evidence. Same-agent S037 review,
not independent external review, confirms exact paper/Lean fidelity:

- Raw Trace is an indexed TYPE rooted at initial, retaining actual full Moves,
  source Position indices, flags/turn and complete ordered prefix. Actual append
  equality defines RawBoardStep. Every raw Legal successor lifts, including
  adverse draw-ending successors; origin is raw Arisen only.
- Counter starts at zero and folds stored source/move data. On legal moves,
  source pawn OR occupied destination iff source pawn OR CaptureEvent (enemy
  destination OR explicit en-passant event). Promotions/empty-destination ep
  reset; actual castling has empty destination. Quiet nonpawn moves increment
  despite rights/ep changes. No material-count equivalence or formal English
  FIDE bridge claimed. Exact append and both bounds count BOARD PLIES.

Classical constructions, no novelty claim, oracle/tablebase/engine/enumeration
or arbitrary-clock KRK history witness. Existing owner-reviewed kernel encoding,
A1, official Lean kernel and standard axiom subsets remain the trust boundary.

## Observed fresh Gate Z evidence

| Candidate → freeze | Own exact proof-source SHA | Jobs / build exit | Seconds | Reports / runner exit | Verified UTC |
|---|---|---|---|---|---|
| EC-C023 → EC-T0021 | `526a298b80ef04541e518a3dcc62f861c8f51c5c` | 59 / 0 | 2270.05 | 265 / 0 | 2026-10-19T17:25:45Z |
| EC-C024 → EC-T0022 | `2d2b40ddaaff2a962bb9f573e8de799b1427d5f8` | 66 / 0 | 1793.59 | 271 / 0 | 2026-10-19T17:55:50Z |

TWO NEW GitHub clones, sequentially, at `/tmp/engame-s037-c023-gate-z` and
`/tmp/engame-s037-c024-gate-z`; neither existed beforehand. Each had no
formal/.lake BEFORE its full build. No reuse of Gate F or historical clones.
Each full build was followed by complete AxiomCheck. Full runner outputs are
byte-identical to actual S035/S036 Gate F evidence. All ten main statements and
axiom reports inspected: trace four use standard three; counter event_cases
uses propext, other five use standard three. No sorryAx/native reduction.

Official unmodified core Lean 4.35.0, release
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`; empty dependency list, no host shim,
TLS/checksum settings unchanged. Existing elan and Git proxy access sufficient.
Runtime connected, observations current, unrestricted/enforced; no new secret,
installation, Docker or configuration needed. Hosted CI **unobserved**.

[Complete evidence](../theorems/frozen/VERIFICATION-S037/README.md) includes
per-candidate full build/axiom logs, toolchain/release identity, command exits
and timings, pre-build assertions, clean source/import SHA-256 inventories and
UTC. Every candidate/import byte equals current main and its exact anchor. Historical
aggregate imports/runner are hashed at their own anchor; current main adds the
S036 counter entries to those two aggregate files.
RawClock's complete dependency closure records all five RawTrace imports;
their bytes also equal EC-T0021's earlier independent anchor. Complete sources,
exact public statements, axioms and import hashes appear in each v1 manifest:
[EC-T0021](../theorems/frozen/EC-T0021/v1.md),
[EC-T0022](../theorems/frozen/EC-T0022/v1.md).

The first verifier's post-build comparison was initially too strict: it compared
current aggregate imports/runner with the earlier trace-only anchor. Build
and AxiomCheck had BOTH passed; only evidence post-processing stopped.
The interruption is retained in EC-C023/postprocess-interruption.log. Corrected
inspection preserves historical aggregate hashes and verifies additive later
entries separately; finalize.py reads the successful logs without rerunning
Lean. No theorem, source or mathematical scope was changed. A supplemental
elan identity query initially ran outside formal/ (no selected toolchain);
repeating the identity query in formal/ succeeded. No build was repeated.

Relevant ledger structural validation and existing ledger unit tests, prior
file preservation, source/import identities, ten declarations, Gate F equality,
canonical table, installed full prompt, local links and diff checks are run
and retained in the evidence directory. No unrelated diagnostic suite or new
trivial tests. No formal edits, so no additional working-copy Lean build.

## Remaining obligations and next task

RAW components do not constitute a full HistoryLayer instance. Still open:
no-earlier-terminal admissibility, effective-ep key/correctness, current AND
intended claims, automatic fivefold/75-move adjudication and mate precedence,
Layer A/B/C instantiation, sufficient-clock/repetition lifting, holding/outcome
proofs and numerical KRK distance. Raw legal traces may continue past earlier
draws; no adverse draw-ending child is pruned. A clock bounded by historical
length establishes neither a remaining sub-100 budget nor uniform mate bound,
DTM/DTZ/WDL, Syzygy parity or initial-position value.

S038 targets one raw multi-step growth bound along actual trace extensions,
with paper/audit before Lean. It supplies no numerical KRK bound or repetition
certificate. Closing publication commits/pushes the session branch, fast-forwards
main, pushes main and compares remote SHAs, without claiming hosted CI success.
Proof manifests anchor earlier verified source commits rather than themselves.

## Repeatable progress table

| Endgames / target | Progress | Remaining |
|---|---|---|
| K vs K | Draw proved and frozen | — |
| K+B vs K | Draw proved and frozen | — |
| K+N vs K | Draw proved and frozen | — |
| K+R vs K | Dead/live, clock-free forcing, generic projection, raw traces and counter frozen | FIDE history/adjudication and distance |
| K+Q vs K | Open in this project | General proof and formal verification |
| K+P vs K | Open in this project | General proof and formal verification |
| All four-piece endgames | Open in this project | Every material class and legal position |
| All five-piece endgames | Open in this project | Every material class and legal position |
| All six-piece endgames | Open in this project | Every material class and legal position |
| All seven-piece endgames | Open in this project | Every material class and legal position |
| **Full Syzygy parity (through seven pieces)** | **Open** | **Complete class coverage, 50-move WDL and DTZ parity** |

Session change: S037 froze the raw trace and counter components as EC-T0021/0022 after separate fresh Gate Z checks; 22 bundles are frozen and material-class coverage is unchanged.

## Full installed S038 prompt

````markdown
# NEXT SESSION — S038: Raw multi-step clock growth along actual trace extensions

**Owner instruction:** Execute when the owner says “run next session”. Follow
AGENTS.md: fetch ALL branches, merge earlier unmerged session work, then use
latest main's active prompt. Existing checkout; no worktree. End committed,
pushed on the session branch, merged and pushed to main; never force main.
Publication is authorised. Update docs/SESSION_PROGRESS.md and reproduce its
FULL stable table in closeout and final reply, Syzygy parity LAST, with one
sentence session delta immediately below. Bundles are not solved classes.

## Starting point and reading

S037 froze EC-C023 as EC-T0021 and EC-C024 as EC-T0022 at their separate exact
proof-source anchors after TWO new sequential Gate Z clones. Read actual
manifests and theorems/frozen/VERIFICATION-S037/ evidence, not just this prompt.
Twenty-two bundles are frozen; full FIDE history/adjudication and numerical
KRK distance remain open. Read docs/CHARTER.md, docs/PROOF_PROTOCOL.md,
docs/ROADMAP.md, research/CANDIDATES.md, research/KRK_RULE_DISTANCE_SPEC.md
(especially sufficient-budget lifting), S035–S037 papers/audits/closeouts,
and frozen RawTrace/RawClock definitions and exact append/one-step statements.

## Principal task: one narrow sufficient-budget prerequisite

Register EC-C025 only after fixing an exact, well-posed statement in a
standalone paper and adversarial audit BEFORE Lean. Prove the raw multi-step
upper bound along ACTUAL stored-trace extensions: after n board plies from
state s to state t, clock(t.trace) ≤ clock(s.trace) + n.

Use a new indexed finite extension relation whose zero case is the SAME raw
state and whose successor case is an actual RawBoardStep/append preserving
the full prior trace, with each actual Move and legality witness. A relation
on erased endpoint positions alone is insufficient: different histories can
have equal boards and different counters. Do not assume endpoint clock data,
replace Trace by ReachK, seed arbitrary KRK clocks, or add terminal filtering.
A path's n counts actual appended moves, not full moves or claim actions.

Choose the smallest useful definition and theorem set. A bound for every
prefix of such an extension may be a corollary if justified by the definition;
do not inflate the session with redundant elementary declarations. Use induction
on the actual extension and frozen append_clock_le, including zeroing edges.
The n=0 case retains s exactly; resetting does not invalidate an upper bound
or truncate the stored history. If recording exact move-length growth, prove
it from actual appends and frozen append_spec, not a hypothesised length field.

Import every frozen source unchanged. Add NEW modules, one main theorem per
module and shared definitions separately; add main statements/axioms to
AxiomCheck. No tablebase, engine, class enumeration, stored certificates or
arbitrary-clock game witness. The construction is classical; no novelty claim.

## Audit and semantic limits

Attempt falsification at n=0, one quiet ply, a resetting move, mixed reset/quiet
paths, same erased board with different history, and an earlier raw draw.
Use symbolic general arguments; do not claim a fixed promotion/ep/castling
full prefix was run unless actually constructed and verified. The bound holds
for EVERY actual raw extension, regardless of material, side or outcome.
Never prune adverse draw-ending legal replies to manufacture a win.

This result alone is NOT a sufficient-budget lifting theorem. It supplies no
KRK numerical mate bound, repetition certificate, no-earlier-terminal FIDE
admissibility, repetition-key correctness, current/intended claims, automatic
fivefold/75-move adjudication, mate precedence, full Layer A/B/C instance,
holding/outcome theorem, DTM/DTZ/WDL/Syzygy parity or initial-position value.
In particular h+n<100 is a future certificate HYPOTHESIS, not something proved
for all KRK positions by clock growth. Full history and every defender's
intended-move claim remain separate obligations.

## Verification and closeout

Run changed modules/importers incrementally. Publish the proof-source commit
before ONE new fresh GitHub Gate F clone at its exact SHA; no formal/.lake
before build. Full lake build then complete AxiomCheck must actually pass.
Retain full logs, exits, UTC, official toolchain identity, exact statements and
axioms, source/transitive hashes and clean-source identities. Inspect each new
main report: only propext/Classical.choice/Quot.sound subsets. Gate Z is separate;
no new frozen row or manifest is expected. Preserve all frozen/candidate source,
prior papers/audits/evidence and ledger bytes; aggregate Lean imports/runner
may gain additive entries only. No unrelated diagnostic suite or trivial tests.

Update candidates, roadmap/README, session ledger, progress table and write
sessions/S038_RAW_CLOCK_EXTENSION_BOUND.md with complete actual evidence and
FULL installed S039 prompt. Choose the next small obligation from actual
results, without claiming a full FIDE instance or a numeric KRK bound. Commit,
push branch, merge/push main and compare remote SHAs. Report actual checks and
unobserved hosted CI separately.

## Cloud activation

Use runtime skill if available; inspect environment/network policy and reuse
existing Git proxy authentication. Official core Lean4.35.0, no new dependency:
export ELAN_HOME=/workspace/.tools/elan
export PATH="$ELAN_HOME/bin:$PATH"
Lake commands run in formal/, Python at root. One required fresh build at a
time; keep TLS/checksum verification. Existing environment suffices unless
actual evidence establishes a missing prerequisite.
````
