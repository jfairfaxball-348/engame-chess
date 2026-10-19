# S036 — Raw halfmove-clock fold over stored legal traces

Date 2026-10-19. Base main `7c357b33ce75f6cfeb5561190f463cd70cc6ecbb`;
branch session/s036-raw-halfmove-fold. All-branch fetch found no earlier unmerged
remote session work; latest main prompt executed. Publication authorised.

## Result and scope

**EC-C024 FORMAL_VERIFIED**, Gate Z pending; EC-C023 freeze also pending.
Twenty frozen bundles unchanged; no ledger row, manifest or prior source edited.
Classical construction, no novelty claim, no engine/tablebase/oracle used.

New Rules.RawClock modules: Definitions plus ONE main theorem each in EventCases,
LegalEvent, CastleEmpty, Append, LengthBound and StepBound. Six declarations:

- event_cases: source pawn resets (all promotion/ep choices), occupied dst
  resets, nonpawn empty dst does not. Capture interpretation needs legality.
- legal_zero_iff: for EVERY kernel legal move, detector iff Pawn OR CaptureEvent.
  Legality's targetOK ensures destination occupancy is enemy nonking; ep is
  already a pawn move. CaptureEvent is enemy dst OR explicit kernel ep event.
- castle_empty: actual canCastle predicate requires empty destination in both
  branches; source king and event_cases therefore give no reset. Quiet
  king/rook rights loss and ep flag changes alone never reset the counter.
- append_clock: for EVERY raw state/move/legal proof, child clock is exactly
  zero on reset, parent+1 otherwise; initial stored trace counter is zero.
- clock_le_length: EVERY stored Trace has counter <= move-list length,
  structurally proved at root/snoc. Counts BOARD PLIES, not full moves.
- append_clock_le: every raw append increases counter by at most one ply.

[Paper](../proofs/EC-C024_RAW_HALFMOVE_FOLD.md) and
[adversarial review](../audits/EC-C024_RAW_HALFMOVE_PAPER.md) saved BEFORE Lean;
[fidelity review](../audits/EC-C024_RAW_HALFMOVE_LEAN.md) records exact correspondence.
Reviews same-agent, not independent external review. FIDE Articles 9.3 and
9.6.2 actually retrieved; SHA matches S032, UTC/hash/clause text in evidence.
The 75-move clause explicitly preserves last-move mate precedence, but this
session builds no adjudicator. Kernel event specification is explicit; no
material-count equivalence or formal theorem about English FIDE is claimed.
The existing owner-reviewed FIDE-to-kernel encoding remains trusted.

## Observed verification

Published proof-source **`2d2b40ddaaff2a962bb9f573e8de799b1427d5f8`**, PUSHED before Gate F.
ONE NEW fresh GitHub clone `/tmp/engame-s036-gate-f`, detached at that exact SHA;
formal/.lake absent BEFORE build. Official core Lean **4.35.0** release
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, no deps/host shim.

- Incremental new modules/importer build passed, 66 jobs; full runner exit 0.
- Fresh full build **66 jobs**, exit 0, **365.225s**; complete AxiomCheck exit 0.
- Verified UTC **2026-10-19T14:23:42Z**. **271 allowed axiom reports**: 239 standard-three,
  18 propext/Quot.sound, 9 propext, 5 axiom-free. event_cases uses propext;
  other five new mains use standard three. Exact statements/data printed.
- Working/clean outputs byte-identical; every Lean source matches fresh exact
  source. New and full formal-source/import hashes retained. Seven-module
  forbidden-token scan zero. **359** prior protected files byte-identical;
  two aggregate files additive only, five traces equal S035 original anchor.
- Ledger structural validator passed: **20** frozen rows, all unchanged.
- Initial authoring command used the wrong working directory and wrote no
  source. Initial local Lean compile failed on hypothesis simplification and
  Boolean lemma syntax; exact failure log retained. Corrected and verified
  without changing the mathematical statement or kernel definitions.
- Existing environment/toolchain sufficient; runtime current, connected and
  unrestricted/enforced. No installation, environment configuration change,
  TLS/checksum bypass or secret requested. Existing Git proxy access worked.
- No unrelated Python diagnostic suites rerun (no Python/ledger changes), no
  new trivial tests, no fixed compatible promotion/ep/castling full game prefix
  constructed or claimed. Controls are general symbolic facts/paper arguments.
- Hosted CI **unobserved**; a push is not claimed as a CI pass.

Complete [evidence](evidence/S036/README.md) includes full build/axiom/statement
logs, failure log, source identity, hashes, toolchain, preservation and counts.
Final progress/table/full-prompt/link and diff checks are recorded separately.

## Remaining obligations and publication

Counter never truncates full trace, including resets; frozen append_spec retains
ordered move/position prefix and exact length. No terminal filter added. RAW
continuation past a future automatic draw is still accepted when kernel Legal
permits; this is not FIDE no-earlier-terminal admissibility. No repetition key,
current/intended claims, automatic fivefold/75-move outcomes or mate precedence
classifier, full Layer A/B/C instance, sufficient-budget/repetition lifting,
holding/outcome or uniform KRK bound is proved. Clock <= historical length does
not imply a remaining budget below 100, exact DTM/DTZ/WDL, Syzygy parity or
initial-position value. Both pending freezes remain separate from Gate F.

S037 installs separate Gate Z verification of EC-C023/024 at their OWN exact
anchors, with new sequential fresh clones and immutable manifests only on
observed success. After successful freezes, a raw multi-step clock-growth bound
is a possible next narrow budget prerequisite; it supplies no numerical KRK
bound. Closing documentation retains all exact proof-source Lean bytes, then
pushes branch, fast-forwards main, pushes main and verifies matching remote
SHAs. This report anchors evidence to the earlier immutable proof-source commit,
not circularly to its own publication commit.

## Repeatable progress table

| Endgames / target | Progress | Remaining |
|---|---|---|
| K vs K | Draw proved and frozen | — |
| K+B vs K | Draw proved and frozen | — |
| K+N vs K | Draw proved and frozen | — |
| K+R vs K | Dead/live, clock-free forcing and generic projection frozen; raw traces and counter verified | FIDE history/adjudication and distance; freeze raw components |
| K+Q vs K | Open in this project | General proof and formal verification |
| K+P vs K | Open in this project | General proof and formal verification |
| All four-piece endgames | Open in this project | Every material class and legal position |
| All five-piece endgames | Open in this project | Every material class and legal position |
| All six-piece endgames | Open in this project | Every material class and legal position |
| All seven-piece endgames | Open in this project | Every material class and legal position |
| **Full Syzygy parity (through seven pieces)** | **Open** | **Complete class coverage, 50-move WDL and DTZ parity** |

Session change: S036 formally verified raw halfmove reset events, append updates and ply bounds; full FIDE rule/distance coverage remains open and the frozen count stays twenty.

## Full installed S037 prompt

````markdown
# NEXT SESSION — S037: Freeze the raw trace and halfmove-counter components

**Owner instruction:** Execute when the owner says “run next session”. Follow
AGENTS.md: fetch ALL branches, merge earlier unmerged session work, then use
the latest main's active prompt. Existing checkout; no worktree. End committed,
pushed on the session branch, merged and pushed to main; never force main.
Publication is authorised. Update docs/SESSION_PROGRESS.md and reproduce its
FULL stable table in closeout and final reply, Syzygy parity LAST, with one
sentence session delta immediately below. Bundles are not solved classes.

## Starting point and required reading

Twenty bundles remain frozen. EC-T0020 is abstract rule-layer projection;
EC-T0019 is the clock-free KRK forcing classification. No complete FIDE history
layer or numerical KRK distance is certified. Read docs/CHARTER.md,
docs/PROOF_PROTOCOL.md, docs/ROADMAP.md, research/CANDIDATES.md,
research/KRK_RULE_DISTANCE_SPEC.md, and the two papers/audits/closeouts with
actual evidence under sessions/evidence/S035/ and S036/.

Pending Gate Z candidates and exact PUBLISHED proof-source anchors:

- EC-C023: `526a298b80ef04541e518a3dcc62f861c8f51c5c`.
  RawTrace/{Definitions,Append,Soundness,Completeness,Origin}.lean.
  Four main declarations: append_spec, raw_step_sound, raw_step_complete,
  trace_arisen, namespace EndgameChess.Rules.RawTrace.
  Gate F: 59 jobs, 265 standard-subset axiom reports.
- EC-C024: `2d2b40ddaaff2a962bb9f573e8de799b1427d5f8`.
  RawClock/{Definitions,EventCases,LegalEvent,CastleEmpty,Append,LengthBound,
  StepBound}.lean. Six main declarations: event_cases, legal_zero_iff,
  castle_empty, append_clock, clock_le_length, append_clock_le, namespace
  EndgameChess.Rules.RawClock. Actual Gate F results are in S036 evidence;
  inspect rather than assuming success from this prompt.

## Principal task: separate immutable Gate Z records

Review paper/Lean fidelity before freezing. Raw Trace is an indexed TYPE with
actual source positions, full Moves and preserved prefix, rooted at initial;
RawBoardStep is actual append. Every raw Legal successor lifts, without
pruning draws. Endpoint Arisen is raw reachability, not real game admissibility.

The counter folds those traces from zero. Source pawn OR occupied destination
is proved equivalent, ON LEGAL MOVES, to source pawn OR kernel CaptureEvent.
CaptureEvent is enemy destination OR explicit en-passant event. Pawn moves
include promotion and ep with empty destination. Castling predicate forces
empty destination; king/nonpawn quiet moves increment despite lost rights or
changed ep. Exact append and global-length/one-step bounds use BOARD PLIES.
No material-count equivalence theorem or formal bridge to English FIDE is
claimed; the owner-reviewed kernel encoding remains the modelling boundary.
Do not upgrade these results into full rule adjudication.

Run Gate Z ONCE per candidate at its exact published anchor: TWO NEW fresh
GitHub clones, sequentially, no formal/.lake before either build. Do not reuse
Gate F or historical verification clones. Use pinned official core Lean4.35.0,
no dependencies/host shim; TLS/checksum verification on. Each full lake build
must actually pass, followed by its complete AxiomCheck. Retain full logs,
actual exits, toolchain/release identity, exact statements/axioms, source and
transitive import hashes, clean-source identities and verification UTC.
Inspect all main reports: only propext/Classical.choice/Quot.sound subsets.
Compare candidate files and main statement output to actual Gate F evidence.
Confirm current main's candidate source bytes equal both immutable anchors.
A push alone does not establish hosted CI success.

If both pass, freeze EC-C023 as EC-T0021 and EC-C024 as EC-T0022 with complete
v1 manifests. Each manifest names its OWN full proof-source SHA, declaration
list, scope, rule edition, paper/audit, exact build/axiom evidence and hashes.
RawClock's five verified trace imports and frozen kernel dependencies must be
recorded; do not silently substitute the later source SHA for EC-C023's anchor.
Append TWO FROZEN rows to theorems/LEDGER.csv only after successful Gate Z;
prior twenty rows/manifests, all frozen and candidate Lean sources, prior papers,
audits and evidence remain byte-identical. No formal source change expected.
If a gate fails, preserve exact failure and leave that candidate unfrozen;
never weaken the theorem or bypass verification to create a ledger row.

## Semantic boundaries and closeout

These are RAW components, not a full HistoryLayer instance. Full FIDE work still
needs no-earlier-terminal admissibility, effective-ep repetition keys and their
correctness, current AND intended-move claims, automatic fivefold/75-move rules,
mate precedence, Layer A/B/C instantiation, sufficient clock/repetition lifting,
and holding/outcome proofs. Raw traces may continue after earlier draws when
kernel legality permits. Never delete adverse draw-ending legal replies.
A clock bounded by total historical length is not a uniform KRK mate bound,
a remaining budget below 100, DTM/DTZ/WDL/Syzygy parity or initial-position value.
No engine/tablebase/enumeration or arbitrary-clock KRK game witness.

Update actual candidate/roadmap/README status, session ledger, progress table
and write sessions/S037_FREEZE_RAW_TRACE_CLOCK.md with complete evidence and
FULL installed S038 prompt. After successful freezes, prefer one narrow raw
multi-step clock-growth bound using actual trace extensions as the next
sufficient-budget prerequisite, with paper/audit before Lean. Do not claim
that a numeric KRK bound or repetition certificate follows. If freeze fails,
choose the exact repair obligation from observed evidence. Run relevant ledger
validation and preservation/source/link/progress checks; no unrelated diagnostic
suite or new trivial tests. Commit, push branch, merge and push main; compare
remote SHAs and report actual frozen count (22 only if both gates passed).

## Cloud activation

Use runtime skill if available; inspect environment/network policy and reuse
existing Git proxy authentication. Official core Lean4.35.0, no new dependency:
export ELAN_HOME=/workspace/.tools/elan
export PATH="$ELAN_HOME/bin:$PATH"
Lake commands run in formal/, Python at root. One required fresh build at a
time; keep TLS/checksum verification. Existing configured environment suffices
unless actual evidence establishes a missing prerequisite.
````
