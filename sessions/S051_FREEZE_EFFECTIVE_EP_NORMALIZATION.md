# S051 — Freeze effective ep normalization preservation

2026-10-20, base main be6469ea790c453f07663d5690e3ec6d0f0e71fb;
branch session/s051-freeze-effective-ep-normalization. All-heads fetch,
no prior unmerged work, existing checkout. Consecutive sessions/publication
authorised by owner. EC-C031 frozen as EC-T0029, 29 bundles; no class upgrade.

## Result and fidelity

For every raw Position q and actual Move m, effective ep normalization preserves
Boolean isLegal, and for actual original legal moves preserves the FULL played
Position. No reachability/history/material/terminal/colour/promotion premise.
Available legal EP witness gives normalization identity. Without witness, ordinary
moves use frozen ep irrelevance plus same-turn self-check; EP-shaped moves are
illegal originally by frozen characterization, normalized pseudo false by nonzero
dx, empty dst and none marker. No equality of illegal raw EP endpoints asserted.
No adverse legal reply pruning or replacement of actual self-check legality.

Both complete normalization modules frozen unchanged, exact paper and Lean fidelity
reviewed. [Review](../theorems/frozen/VERIFICATION-S051/fidelity-review.md).
Same-agent review, not independent external audit. Both colours, arbitrary flags,
promotions, missing/wrong-colour/nonpawn/king/castling/same-file/occupied/source=
destination/pseudo-only-selfcheck cases reviewed symbolically. No concrete full-game
diagnostic, enumeration/oracle/stored certificate or novelty claim. Initial S050
incremental simp failure and unchanged-statement rewrite correction reviewed.

## Observed evidence

Own proof-source `4d47b33549fc5286099cae0bd89de76b05fbeb42`; NEW GitHub clone `/tmp/engame-s051-gate-z`, no .lake before build. Full 77-job build exit 0 in 478.964s; COMPLETE AxiomCheck exit 0 at 2026-10-20T12:32:16Z, 278 allowed reports. Main standard-three; entire report identical to S050 Gate F.
[Evidence](../theorems/frozen/VERIFICATION-S051/README.md). Full source/transitive
hashes, clean HEAD/tree/status, full logs/commands/exits/times/UTC/toolchain retained.
Every formal byte matches own anchor/current source. Official core Lean4.35.0
release eb6cafb7290e8bd5f2937522d8d804f58f02bafc, no dependencies/shim or setup/
TLS/checksum change. Hosted CI unobserved. One new successful clean run, no repeated
build. No source edit/incremental build. Relevant ledger structure/tests,
preservation/evidence/full-table/full-prompt/local-link/diff checks passed; all
prior protected source/papers/audits/evidence/manifests and 28 rows preserved,
exactly EC-T0029 appended. No unrelated diagnostics/trivial tests.
Commit/push branch, merge/push main and compare remote SHAs; final identities
retained in Git/observed publication checks. Continue S052 unless owner stops.

## Limits and continuation

No full FIDE key/rights-history/claims/adjudication/mate precedence, strategy
lifting, numerical KRK, holding/outcome, WDL/DTZ/Syzygy or initial-position value.
S052 normalized-key congruence prerequisite installed, not a solved-class claim.

## Required progress table

| Endgames / target | Progress | Remaining |
|---|---|---|
| K vs K | Draw proved and frozen | — |
| K+B vs K | Draw proved and frozen | — |
| K+N vs K | Draw proved and frozen | — |
| K+R vs K | Dead/live and clock-free forcing frozen; projection, raw history/clock/key-count and legal-ep and normalization prerequisites frozen | Concrete rule integration and distance |
| K+Q vs K | Open in this project | General proof and formal verification |
| K+P vs K | Open in this project | General proof and formal verification |
| All four-piece endgames | Open in this project | Every material class and legal position |
| All five-piece endgames | Open in this project | Every material class and legal position |
| All six-piece endgames | Open in this project | Every material class and legal position |
| All seven-piece endgames | Open in this project | Every material class and legal position |
| **Full Syzygy parity (through seven pieces)** | **Open** | **Complete class coverage, 50-move WDL and DTZ parity** |

Session change: S051 froze effective-ep normalization preservation as EC-T0029 after a new exact-source Gate Z check; 29 bundles are frozen and material-class coverage is unchanged.

## Full installed S052 prompt

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
