# NEXT SESSION — S040: Raw prefix and prospective-ply clock certificate

Execute as the next authorised session. Follow AGENTS.md: explicitly fetch ALL
remote heads, merge earlier unmerged work, start from latest main in the existing
checkout, no worktree. Publication authorised. Commit/push the session branch,
merge/push main and compare remote SHAs; never force main. Update and reproduce
the FULL stable progress table in closeout and owner report, Syzygy parity LAST,
with a one-sentence session delta below. Bundles are not solved classes.

## Starting point and reading

S039 froze EC-C025 as EC-T0023 at its own exact proof-source anchor
22243b9ca5769e1478c75a333befa3c8465c90f2 after a NEW Gate Z clone. Read the actual
manifest and VERIFICATION-S039 evidence, EC-T0021/0022 manifests and unchanged
RawTrace/RawClock definitions. Read docs/CHARTER.md, docs/PROOF_PROTOCOL.md,
docs/ROADMAP.md, research/CANDIDATES.md, research/KRK_RULE_DISTANCE_SPEC.md
(especially intended claims and sufficient-budget lifting), S038/S039 closeouts,
EC-C025 paper/audits, exact Extends constructors and clock_le_extension statement.
Twenty-three frozen bundles; full FIDE adjudication and numerical KRK bounds open.

## Principal task: one explicitly conditional clock certificate

Write a standalone paper and adversarial audit BEFORE Lean and only then
register EC-C026. Prove this precise statement (all counters in BOARD PLIES):

For every raw state s and n:Nat, if clock(s.trace)+n<100, then for EVERY
k≤n and EVERY actual Extends k s u,

  clock(u.trace)<100 AND
  (k<n → for EVERY v, RawBoardStep u v → clock(v.trace)<100).

The root budget inequality is a HYPOTHESIS, not a promised bound for KRK.
The second conjunct quantifies over EVERY raw legal prospective append at
an interior prefix, including moves outside a selected strategy and reset or
draw-ending children. The announced prospective move is not asserted to be
played; the theorem merely bounds its computed child. This does not model
claim actions. k=n must retain the current-prefix bound but makes NO claim
about another ply. n=0 still bounds the root and gives no prospective guarantee.

Use frozen full-state Extends, RawBoardStep and clock_le_extension unchanged.
One combined theorem in one NEW module suffices; no redundant arithmetic or
prefix extraction declarations, arbitrary clock seeds, ReachK surrogate,
endpoint clock hypothesis, terminal filtering or strategy tree is needed.
The prefix clock bound follows from k≤n and frozen growth. For k<n, construct
Extends (k+1) s v with its actual RawBoardStep and use k+1≤n. Keep the complete
trace and all original imports unchanged. Add the new main statement/axioms to
AxiomCheck and the aggregate import additively; one module per main theorem.
Classical arithmetic certificate, no novelty claim, oracle, tablebase, engine,
class enumeration, stored certificate or fabricated compatible KRK history.

## Audit and semantic limits

Attempt falsification at n=0, k=0, k=n, one quiet edge, zeroing edge, mixed
reset paths, equal erased boards with differing histories, and an earlier raw
draw. Check strict boundaries: clock(s)+n=99 satisfies the threshold condition;
=100 does not. At a terminal-depth prefix with clock 99, a further quiet
prospective move could reach 100, explaining why k<n is essential. These are
symbolic controls; do not claim a concrete initial-rooted full game was run.
No fixed promotion/ep/castling prefix is required or may be fabricated.

This certificate supplies only the clock side of a later sufficient-budget
argument. It does NOT prove a FIDE CanClaim predicate false, repetition bounds,
no-earlier-terminal admissibility, key correctness, current/intended claim
semantics, automatic fivefold/75-move adjudication, mate precedence, full Layer
A/B/C instance, strategy-tree extraction, rule-aware lifting, numerical KRK mate
bound, holding/outcomes, DTM/DTZ/WDL/Syzygy parity or initial-position value.
Do not claim that all KRK states admit this budget. Full preceding history and
every defender's repetition/intended-move claims remain separate obligations.

## Verification and closeout

Run only changed modules/importers incrementally. Publish the proof-source
commit BEFORE ONE NEW fresh GitHub Gate F clone detached at its exact SHA;
no formal/.lake before build. Full lake build THEN complete AxiomCheck must
actually pass. Inspect the new exact statement and axiom report (only subsets
of propext/Classical.choice/Quot.sound). Retain full logs, exits/timings, UTC,
official toolchain identity, full source/transitive hashes and clean-source
identities. Compare working and clean outputs. Gate Z is separate; no new
frozen row or manifest expected. Preserve all prior source/papers/audits/evidence
and ledger bytes; aggregate Lean files only gain additive entries.

Update candidate status only from actual evidence, roadmap/README, session
ledger and progress table. Write sessions/S040_RAW_CLOCK_BUDGET_CERTIFICATE.md
with complete evidence and FULL installed S041 prompt. Select the next narrow
obligation from actual results, considering separate Gate Z before expanding
scope. Run relevant evidence/preservation/document checks and ledger structure;
no unrelated diagnostic suite or trivial tests. Commit/push/merge/push and
verify remote SHAs; hosted CI remains unobserved unless actually inspected.

## Cloud activation

Use runtime skill, inspect environment/network policy and reuse inherited Git
proxy authentication. Official unmodified core Lean4.35.0, no new dependency.
ELAN_HOME=/workspace/.tools/elan; prepend its bin directory to PATH. Lake in
formal/, Python at root. One fresh build at a time. Keep TLS/checksum validation.
Existing environment suffices unless actual evidence establishes otherwise.
