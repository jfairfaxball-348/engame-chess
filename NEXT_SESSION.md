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
