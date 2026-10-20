# NEXT SESSION — S052: Normalized-key legal-move congruence

Owner authorises consecutive sessions until told to stop. Follow AGENTS.md,
charter/protocol. Fetch ALL remote heads, merge prior unmerged work, latest main,
existing checkout. Commit/push branch, merge/push main, compare remote identities;
never force main. Full stable progress table, Syzygy last, immediate session delta.

## Starting point and reading

S051 froze EC-C031 as EC-T0029 at OWN proof-source
4d47b33549fc5286099cae0bd89de76b05fbeb42; 29 frozen bundles, not solved classes.
Read actual manifest/Gate Z evidence, S050/51 closeouts, EC-C031 paper/audits,
NormalizationDefinitions/Normalization, RawRepetition/Definitions, EC-T0026–28,
RawOccurrences definitions/append, research/KRK_RULE_DISTANCE_SPEC.md and roadmap.

## Principal task

After complete standalone exact paper and separate adversarial audit BEFORE Lean,
register EC-C032 LOCAL_VERIFIED. NEW shared KeyDefinitions module defines
noncomputable key (q:Position):Position := normalizeEP q. Key equality means FULL
normalized Position equality (board function/turn/castling/effective ep); no lossy
hash or board-only equality. ONE NEW main theorem module KeyCongruence:

∀q r, key q=key r → ∀m,
 isLegal q m=isLegal r m ∧
 (isLegal q m=true → play q m=play r m).

Exact actual Move/promotion retained, every raw q/r including malformed flags,
both colours, no history/material/terminal/strategy restriction. Proof uses
normalizeEP_preserves twice, transports along full normalized equality and
transitivity. Legal equality supplies legality at r before using its endpoint
preservation. Full endpoints, including newly computed ep and castling rights,
must coincide. Do not assert equality of raw play for illegal EP-shaped moves.
This is move/endpoint congruence, one prerequisite for a repetition key; no full
Article9.2.3 iff, converse, historical rights validity, executable hashing/search
or equivalence of arbitrary histories. Avoid introducing a global classical
DecidableEq Position instance unnecessarily; this task needs equality only.

Audit equal boards but different turn/rights/effective marker do not satisfy key
premise; raw marker differing only when unavailable can be ignored by frozen
normalization. Pinned/pseudo-only EP, promotions, king/castling, source=destination,
no legal moves and all adverse replies remain under the actual quantified Move.
Symbolic proofs, no coordinate/class enumeration/tablebase/engine/certificates.
Same-agent review transparently named, not independent external audit; no concrete
full promotion/castling/threshold game run or novelty claim.

## Verification and closeout

Frozen sources unchanged, aggregates additive only. Incrementally build changed
modules/importers, COMPLETE working AxiomCheck. Publish proof source BEFORE ONE
NEW GitHub Gate F clone at FULL exact SHA, .lake absent before full build then
COMPLETE runner. Inspect exact main, standard-three axiom subsets only, retain
full logs/commands/exits/times/UTC/toolchain identity, all source/transitive SHA256,
clean HEAD/tree/status; compare whole working/clean report and source bytes.
Official core Lean4.35.0, no dependency/shim. Gate Z separate; no new frozen
manifest/ledger row this session. Preserve all prior protected records/source/29
rows. Relevant ledger/evidence/preservation/full-table/full-prompt/local-link/diff
checks only, no unrelated diagnostics/trivial tests. Record any gap honestly.

Update candidate/roadmap/README/session ledger/progress, write
sessions/S052_NORMALIZED_KEY_CONGRUENCE.md with actual evidence and FULL installed
S053 prompt; consider separate own-source freeze before full key counting.
Commit/push/merge/push and compare remote identities. Hosted CI unobserved unless
actually inspected. Continue next session under standing owner instruction.

No full FIDE key/rights-history, claim/automatic-draw/mate-precedence adjudication,
strategy lifting, numerical KRK, holding/outcome, WDL/DTZ/Syzygy or initial-position
result. No adverse legal replies pruned; key states not assumed to share compatible
initial-rooted histories.

Use available runtime guidance/status, network policy and inherited proxy/CA.
ELAN_HOME=/workspace/.tools/elan; lake in formal/, Python at root. ONE fresh build
at a time, official core toolchain, TLS/checksums unchanged.
