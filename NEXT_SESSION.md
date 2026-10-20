# NEXT SESSION — S042: Full raw-history key occurrence counting and exact append law

Execute as the next authorised session. Follow AGENTS.md: explicitly fetch ALL
remote heads, merge earlier unmerged work, read latest main prompt, existing
checkout/no worktree. Publication authorised. Commit/push branch, merge/push main,
compare remote SHAs; never force main. Update/reproduce FULL stable progress table
in closeout and owner report, Syzygy parity LAST, one sentence delta below.
Consecutive execution authorised until owner stops. Bundles are not solved classes.

## Starting point and reading

S041 froze EC-C026 as EC-T0024 at its own source
`dd24ef3b4bd68d429c9c381908a7f3d5bfa9f85f` after a NEW exact-source Gate Z.
Read actual manifest/VERIFICATION-S041 evidence, EC-T0021–0023 manifests,
RawTrace.Trace.positions and append_spec, S035–S041 papers/audits/closeouts relevant
to stored history and clock, docs/CHARTER.md, docs/PROOF_PROTOCOL.md,
docs/ROADMAP.md, research/CANDIDATES.md, and research/KRK_RULE_DISTANCE_SPEC.md
(repetition key, occurrence convention and intended claims). Twenty-four bundles
frozen; full FIDE repetition/adjudication and numerical KRK remain open.

## Principal task: one generic bookkeeping prerequisite

Write standalone paper and adversarial audit BEFORE Lean, then register EC-C027.
Fix an arbitrary key type K with decidable equality and a FIXED map
key:Position→K. Define a raw full-history occurrence count by counting positions
q in the frozen Trace.positions list whose key(q)=a, for a queried a:K.
Count BOTH the initial root and current endpoint. Do not count moves, omit the
root, discard a reset prefix, or introduce an independent count vector/clock.
Keep the existing full indexed Trace data and exact append relation unchanged.
A separate new definitions module should hold the count; one new theorem module
should establish the exact append law for EVERY s, legal actual m and queried a:

  occ(key, append(s,m,hm).trace, a)
    = occ(key,s.trace,a) + (if key(play(erase s)m)=a then 1 else 0).

Derive it from frozen append_spec's exact position-list append equation and
ordinary list counting. Decidable equality is an explicit typeclass parameter;
do not assume an arbitrary Boolean equality without correctness. Avoid extra
trivial bound/monotonicity theorem modules. At the root, the definition counts
one iff key(initial)=a; give this computation in the paper/audit, without adding
an unnecessary public theorem if not needed for the main proof.

The key map MUST be the SAME on both histories. For counting the new current
key, substitute a=key(new endpoint): the prior term queries that NEW key in the
OLD full history. It is NOT generally old-current-count+1, because the old
current key may differ. No fixed material, colour, terminal or strategy filter.
Retain every raw legal append, including zeroing and draw-ending children.
No independent clock seeds, erased-history substitutions, arbitrary KRK witness,
class enumeration, engine, tablebase or stored position certificate.
Classical list counting, no novelty claim.

## Adversarial controls and semantic limits

Audit empty-move root (positions has one element), absent key, equal/new key,
nonconsecutive repeated occurrences, same erased board with differing prior
histories, reset move retaining all preceding positions, and earlier raw draw.
A constant key is a valid generic diagnostic: every position counts. This
shows why the generic map is NOT automatically the FIDE repetition key.
Controls may be symbolic lists/definitions; do not claim a compatible full
promotion/ep/castling/threshold game was run without actually constructing it.

No effective-legal-en-passant key, Article 9.2.3 correspondence, lawful rights
history, repetition threshold certificate, current/intended claim classifier,
no-earlier-terminal admissibility, automatic fivefold/75-move adjudication,
mate precedence, full Layer/strategy extraction/lifting, numerical KRK bound,
holding/outcome, DTM/DTZ/WDL/Syzygy parity or initial-position value follows.
No theorem that all KRK histories have low repetition or h+n<100. Generic key
counting is bookkeeping, not a complete FIDE history instance. No adverse reply
may be pruned to turn a clock-free forcing result into a rule-aware win.

## Verification and closeout

Add NEW modules only, one main per theorem module/shared definitions separate;
add exact definition/main statement/axioms to AxiomCheck and aggregate imports
additively. Preserve all prior frozen/candidate source, papers/audits/evidence,
manifest and ledger bytes. No new frozen row/manifest this Gate F session.
Run changed modules/importers incrementally, publish proof source BEFORE ONE NEW
GitHub Gate F clone at FULL exact SHA. No formal/.lake before full build; then
COMPLETE AxiomCheck must actually pass. Retain full logs, exits/timings, UTC,
official toolchain, exact definition/statement and allowed standard-three subset
axioms, all source/transitive hashes and clean-source identity. Compare full
working/clean output. No unrelated diagnostic suite or trivial tests.

Update candidates, roadmap/README, session ledger and progress table. Write
sessions/S042_RAW_KEY_OCCURRENCES.md with complete actual evidence and FULL
installed S043 prompt; consider separate exact-source freeze before expanding
semantics. Run relevant preservation/evidence/ledger/document checks. Commit,
push branch, merge/push main, compare remote SHAs. Hosted CI unobserved unless
actually inspected. Continue the installed next prompt under standing authorisation.

## Cloud activation

Use available runtime guidance and inspect network policy; reuse inherited Git
proxy. Official core Lean4.35.0, no dependency. ELAN_HOME=/workspace/.tools/elan;
prepend bin to PATH. Lake in formal/, Python at root. ONE fresh build at a time;
TLS/checksums unchanged. Existing environment suffices absent actual blocker.
