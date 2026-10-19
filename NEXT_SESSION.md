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
