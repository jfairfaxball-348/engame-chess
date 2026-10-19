# S035 — Concrete raw move traces and complete append lifting

Date: 2026-10-19 (Europe/London). Base main `e409907896f80d838213ee33cdfa5a7a35f9c1cf`; existing checkout on
`session/s035-raw-trace-append`. All-branch fetch found no earlier unmerged
remote work; latest main's S035 prompt was executed. Publication authorised.

## Result and exact scope

**EC-C023 FORMAL_VERIFIED**, awaiting Gate Z; twenty frozen bundles unchanged.
No theorem ledger row or frozen manifest/source changed.

Concrete `Rules.RawTrace.Trace q` is an indexed TYPE: start at the standard
initial Position, or snoc a full Move plus its kernel isLegal proof to a prior
trace. The prior trace and Move are data; the legality evidence is proof-only.
The positions/moves recursors retain ordered actual history including the
initial and current full Position, with turn/rights/ep flags. This is not a
wrapper containing only an Arisen/ReachK proposition or an arbitrary KRK seed.

Four exact new declarations:

- `Rules.RawTrace.append_spec`: given an actual legal Move, append has the
  exact played endpoint; its ordered move list is prefix++[m], its ordered
  position list is prefix++[played endpoint], and move length increases by one.
  Validity is preserved by the indexed snoc constructor, not an unproved replay.
- `Rules.RawTrace.raw_step_sound`: a RawBoardStep, defined by actual append
  equality with that prefix and Move, projects to the kernel Legal relation.
- `Rules.RawTrace.raw_step_complete`: for EVERY raw state s and EVERY raw
  Legal successor r, extract the Move witness and return its exact append
  t with RawBoardStep s t and erase t=r. No outcome/ongoing/winning filter.
- `Rules.RawTrace.trace_arisen`: forgetting data gives frozen kernel Arisen
  at the endpoint, by structural trace induction. It does NOT prove that
  real FIDE play never previously ended.

Five new modules: Definitions, Append, Soundness, Completeness, Origin under
`formal/EndgameChess/Rules/RawTrace/`. Only additive aggregate imports/axiom
runner entries change among prior Lean files. All earlier sources, records,
audits and evidence are preserved.

[Standalone paper](../proofs/EC-C023_RAW_TRACE_APPEND.md) and
[adversarial review](../audits/EC-C023_RAW_TRACE_PAPER.md) were saved BEFORE
Lean; [fidelity review](../audits/EC-C023_RAW_TRACE_LEAN.md) matches the exact
constructors, definitions, all four statements and quantified Move witnesses.
Same-agent reviews, not independent external review. Classical legal-history
construction, no novelty claim. No new diagnostic or per-game replay is used
to certify the general result.

## Observed verification

Published exact **proof-source `526a298b80ef04541e518a3dcc62f861c8f51c5c`**, pushed before a new verification run.
Official core Lean 4.35.0 release
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, no dependency, host shim or TLS/
checksum change. Runtime skill reported current connected/enforced networking;
existing Git HTTPS authentication worked. The S032 authoritative FIDE reading
was reused for scope only; no new normative claim required a new rules fetch.

- Incremental new modules and aggregate build passed; **59-job** final target.
- ONE NEW GitHub clone `/tmp/engame-s035-gate-f`, detached at full SHA;
  no formal/.lake BEFORE build. Full build: **59 jobs, exit 0, 360.247s**.
- Full AxiomCheck/data signatures: exit 0; **265 allowed reports**:
  234 standard-three, 18 propext/Quot.sound, 8 propext, 5 axiom-free.
  All FOUR new declarations have exact statement/axiom output and standard
  three axioms only; no sorryAx/native reduction or extra assumptions.
- Working/clean reports byte-identical; every Lean source byte matches the
  exact checkout. Five-module forbidden scan zero; full module hashes saved.
- All **336** protected prior formal/theorem/proof/audit/script/test/evidence
  files unchanged. Structural ledger check: **20 valid frozen rows**, unchanged.
- No Python implementation or ledger change: unrelated historical diagnostic
  suites were NOT rerun and no new artificial tests were written. These are
  general Lean proofs, not computational samples or class-wide enumeration.
- Progress-table/full-prompt/link/source checks and `git diff --check` passed.
  Hosted CI **unobserved**; no inferred CI result from publication.

Verified UTC `2026-10-19T14:09:53Z`. Full [evidence](evidence/S035/README.md) retains exact
logs, source/axiom identities, toolchain, preservation and machine-readable
counts. No failed build or unexecuted example is counted as successful evidence.

## Remaining work and next session

RAW traces may continue after a future automatic or dead-position draw whenever
kernel Legal allows. No clock, repetition key, Ongoing, current/intended claim,
no-earlier-terminal admissibility or concrete full HistoryLayer instance was
implemented. The result supports the move-data part of A/B; field C and actual
claim/terminal correctness are separate. No numerical KRK bound, holding/
determinacy, full FIDE WDL, DTM/DTZ/Syzygy or initial-position result follows.

S036 targets one raw halfmove-counter fold over this retained data, with
pawn/capture zeroing cases, exact append update and a structural length bound.
It must import the S035 anchor unchanged and retain EC-C023's pending Gate Z.
Full FIDE admissibility/outcome/distance remain open; no arbitrary-clock KRK
snapshot is claimed to have a legal initial-position history.

The closing documentation commit retains exact-source Lean bytes and publishes
this evidence/report and S036 prompt on the session branch, fast-forwards main,
pushes main and compares remote SHA under AGENTS. The immutable proof-source
anchor is separate from the commit containing this report, avoiding a circular
self-reference.

## Repeatable progress table

| Endgames / target | Progress | Remaining |
|---|---|---|
| K vs K | Draw proved and frozen | — |
| K+B vs K | Draw proved and frozen | — |
| K+N vs K | Draw proved and frozen | — |
| K+R vs K | Dead/live, clock-free forcing and generic projection frozen; raw traces verified | FIDE history/clock rules and distance; freeze traces |
| K+Q vs K | Open in this project | General proof and formal verification |
| K+P vs K | Open in this project | General proof and formal verification |
| All four-piece endgames | Open in this project | Every material class and legal position |
| All five-piece endgames | Open in this project | Every material class and legal position |
| All six-piece endgames | Open in this project | Every material class and legal position |
| All seven-piece endgames | Open in this project | Every material class and legal position |
| **Full Syzygy parity (through seven pieces)** | **Open** | **Complete class coverage, 50-move WDL and DTZ parity** |

Session change: S035 formally verified raw trace append retention and complete reply lifting; FIDE rule/distance coverage remains open and the frozen count stays twenty.

## Full installed next-session prompt

````markdown
# NEXT SESSION — S036: A raw halfmove-clock fold over stored legal traces

**Owner instruction:** Execute when the owner says “run next session” or pastes/links
this prompt. Follow `AGENTS.md`: fetch ALL remote branches, merge earlier
unmerged session work, advance to latest main and execute its active prompt.
Use the existing checkout; end committed, pushed and merged to main without
force. Publication is authorised.

**Closing report:** update `docs/SESSION_PROGRESS.md`; copy its complete stable
table into the written closeout and final reply, with full Syzygy parity last
and the session delta immediately below. Bundles are not material classes.

## Starting point and reading

Twenty frozen bundles remain. EC-T0020 is the abstract rule-layer same-budget
projection; EC-T0019 is the clock-free KRK forcing classification. Neither
implements the FIDE history/clock layer. S035 proves EC-C023 concrete RAW trace
append soundness/completeness and endpoint origin; check its actual Gate F
results in `sessions/S035_RAW_TRACE_APPEND.md` and `sessions/evidence/S035/`.
EC-C023 is not frozen; Gate Z remains separate.

Read the charter, proof protocol, current roadmap/candidates,
`research/KRK_RULE_DISTANCE_SPEC.md` §§1–4 and lifting plan,
S035 paper/audits/closeout/evidence, and kernel Move/isLegal/play definitions.
For the new clock interpretation, read the relevant actual FIDE Laws effective
2023-01-01 (Articles 9.3/9.6.2) from the authoritative source if available,
recording retrieval and any unavailable text. The earlier source/hash metadata
is in `sessions/evidence/S032/fide-source.json`. No tablebase or engine source.

S035 exact published proof-source:
`526a298b80ef04541e518a3dcc62f861c8f51c5c`.
Five RawTrace modules (Definitions, Append, Soundness, Completeness, Origin)
and all frozen modules MUST be imported unchanged. Extensions use NEW files.
Do not silently alter the verified trace representation while extending it.

## Principal task: one clock component, not outcome adjudication

Design and prove a raw reversible-halfmove counter as a fold over actual stored
moves. Register EC-C024 only after fixing a well-posed exact statement in a
standalone paper and same-agent adversarial audit BEFORE Lean. No ledger row
is expected in this mathematics session; EC-C023 Gate Z also stays pending.

Use `Rules.RawTrace.Trace q`, rooted at the standard initial position. The data
retain source positions, full Moves, played endpoints and ordered prefixes;
legality proofs are proof-only. Do not replace the stored trace by Arisen or
initialise a KRK snapshot with an arbitrary clock and call it its legal history.

Define a clock-zeroing move event on legal moves: a pawn move OR an actual
capture. A suitable small implementation may detect a pawn at m.src, or an
occupied m.dst. Justify its intended domain carefully: on legal moves a
non-pawn capture is an ordinary destination capture; en passant has an empty
destination but the mover is a pawn and must still zero the counter. Promotion
also moves a pawn. Castling and a noncapturing king/rook move do NOT zero it,
even when castling rights or an ep flag change. If a chosen detector's
correspondence with actual move events is not proved, say exactly which claim
remains conditional instead of calling an arbitrary Boolean the FIDE event.
Do not add oracle data or a material-class lookup to settle event correctness.

Define the raw counter recursively:

- empty initial trace: 0;
- snoc prior m hm at source q: 0 if the move zeroes, otherwise counter(prior)+1.

The stored history is never truncated by this fold, including after a zero.
No Ongoing/terminal filter is added to Trace or RawBoardStep. The function
computes the prescribed update along a RAW kernel trace; it does not certify
that a real FIDE game could legally continue after a prior draw.

Precise first obligations:

1. State/prove the event/reset case facts needed for the chosen legal-move
   detector, explicitly covering pawn moves (including promotion/ep), ordinary
   captures, and nonpawn empty-destination moves (including castling).
2. Exact append law for EVERY raw state s, Move m and legality proof hm:
   counter((append s m hm).trace) equals 0 on zeroing, else counter(s.trace)+1.
3. Global bound for EVERY stored Trace: counter(t) ≤ t.moves.length, and/or
   the directly useful one-step bound counter(append) ≤ counter(prior)+1.
   Keep units as BOARD PLIES; do not confuse 50 full moves with 50 plies.

Use structural induction on the stored trace, not enumeration of positions or
per-game certificates. One-module-per-theorem, shared definitions separately;
add main statements/axiom reports to AxiomCheck. A small bounded event case
split is ordinary mathematics, not a class-wide enumeration proof. Avoid a
large new diagnostic or trivial tests that merely mirror the implementation.

## Audit and semantic boundaries

Retain controls/argument for: empty root, quiet move, ordinary capture, pawn
single/double move, promotion, en passant's empty destination, castling-right
loss without reset, prefix and move-count retention, and raw continuation past
a future automatic draw. Fixed local controls may supplement the proof; label
unexecuted controls and any missing compatible full prefix explicitly.

The new function is a RAW trace counter only. A complete FIDE layer still
needs no-earlier-terminal admissibility, repetition-key correctness, current
AND intended-move claims, automatic fivefold/75-move and mate precedence,
concrete Layer A/B/C instantiation, sufficient-clock/repetition lifting and
holding/outcome proofs. This session does not implement those. A counter bound
by total trace length does NOT produce a uniform KRK mate bound, establish a
remaining budget below 100, or settle DTM/DTZ/WDL/Syzygy conventions. Do not
switch material classes or claim an initial-position result.

## Verification and closeout

Follow Gates L/F, preserve all prior source/manifest/ledger/evidence bytes.
Run incremental new-module/importer checks; inspect exact types and axiom
subsets (propext, Classical.choice, Quot.sound only). For Gate F, commit and
PUSH the exact proof-source SHA, make ONE NEW fresh GitHub clone with no
formal/.lake before `lake build`, and retain complete build/axioms/statements,
hashes, forbidden-token scan, toolchain, actual exits and source identity.
Do not reuse earlier Gate F/Z clones or imply hosted CI passed from a push.
Run only relevant existing checks; no new ledger row in this session.

Write `sessions/S036_RAW_HALFMOVE_FOLD.md`, update actual candidate/roadmap/
status and session ledger, and include the complete progress table and FULL
installed S037 prompt. Choose the next narrow obligation or separate freeze
from actual results; preserve pending EC-C023/024 freezes and the complete
rule/distance gap. If a detector or representation fails, retain the exact
counterexample and correct status rather than weakening the target silently.
Commit/push branch, merge main, push main and verify remote SHA.

## Cloud activation

Use a cloud runtime skill if available; otherwise inspect the provided
environment/network policy and reuse configured access. Existing checkout;
official core Lean 4.35.0,
no dependencies or host shim. `export ELAN_HOME=/workspace/.tools/elan;
export PATH="$ELAN_HOME/bin:$PATH"`. Lake commands in formal/, Python at root.
Keep TLS/checksum checks enabled; one required fresh build at a time.
````
