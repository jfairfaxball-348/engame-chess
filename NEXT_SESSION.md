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
