# S050 — Effective ep normalization preserves legal play

2026-10-20. Base main 985854c4e852d68668d109b2fdbdfbb21665198f;
branch session/s050-effective-ep-normalization. Explicit all-heads fetch,
no prior unmerged work, existing checkout; consecutive sessions/publication
authorised by owner. EC-C031 FORMAL_VERIFIED, Gate Z pending.

## Result and audit

NEW shared normalizeEP definition and ONE NEW main theorem module. Every raw q,m:
Boolean legality unchanged by normalization, FULL played Position unchanged for
actual original legal moves. Available EP yields identity; absent EP/nonshape
uses frozen OrdinaryEP then same-turn self-check; absent EP/shape contradicts
original legality via legalEP_iff_shape and makes normalized pseudo false via
nonzero dx, empty dst and none marker. No unconditional raw illegal EP play
equality, history/material/terminal/colour/promotion restriction or reply pruning.

Standalone [paper](../proofs/EC-C031_EFFECTIVE_EP_NORMALIZATION.md) and separate
[adversarial paper audit](../audits/EC-C031_NORMALIZATION_PAPER.md) saved BEFORE
Lean. [Lean fidelity](../audits/EC-C031_NORMALIZATION_LEAN.md). Same-agent review,
not independent external audit. Symbolic missing/wrong-colour/nonpawn/king/castling,
same-file/occupied pawn/promotion/source=destination/both-colour/malformed-marker/
pseudo-only-self-check cases reviewed. No concrete pinned/compatible full-game
run, enumeration/engine/tablebase/stored certificate or novelty claim.

## Observed verification

Own proof-source `4d47b33549fc5286099cae0bd89de76b05fbeb42`; NEW GitHub clone `/tmp/engame-s050-gate-f`, no .lake before build. Full 77-job build exit 0 in 469.893s, COMPLETE AxiomCheck exit 0 at 2026-10-20T12:23:48Z; 278 allowed reports, main standard-three. Full working/clean report byte-identical.
[Evidence](evidence/S050/README.md). Exact main inspected; all formal bytes match
own anchor. Full formal/transitive hashes, clean HEAD/tree/status and full commands/
exits/times/UTC/toolchain retained. Official core Lean4.35.0 release
 eb6cafb7290e8bd5f2937522d8d804f58f02bafc; no dependencies/shim. Forbidden scan
zero on both NEW modules. First incremental simp unfolding failure retained;
explicit change/rw fixed unchanged statement; final 77-job incremental build/full
working runner passed without warnings. One new successful clean run, no repeated
clean build. Existing current connected runtime/proxy/CA sufficient, no setup/
TLS/checksum changes. Hosted CI unobserved. Relevant ledger/evidence/preservation/
full table/prompt/local-link/diff checks passed; prior source/papers/audits/evidence/
manifests and 28 rows unchanged, aggregates additive only. No unrelated diagnostics/
trivial tests. Own source published before clone; commit/push/merge/push and remote
identity checks retained in Git/observed publication, continuing S051 unless stopped.

## Limits

One normalization prerequisite, not full FIDE repetition key/rights-history,
claims/no-earlier-terminal/adjudication/mate precedence, strategy lifting,
numerical KRK, holding/outcome, WDL/DTZ/Syzygy or initial-position value.
Altered raw positions need not have compatible initial-rooted histories.
Remaining work described as concrete rule integration/distance to distinguish
already specified/frozen foundations from outstanding model/strategy obligations.

## Required progress table

| Endgames / target | Progress | Remaining |
|---|---|---|
| K vs K | Draw proved and frozen | — |
| K+B vs K | Draw proved and frozen | — |
| K+N vs K | Draw proved and frozen | — |
| K+R vs K | Dead/live and clock-free forcing frozen; projection, raw history/clock/key-count and legal-ep and ordinary ep-irrelevance prerequisites frozen; normalization formally verified | Concrete rule integration and distance |
| K+Q vs K | Open in this project | General proof and formal verification |
| K+P vs K | Open in this project | General proof and formal verification |
| All four-piece endgames | Open in this project | Every material class and legal position |
| All five-piece endgames | Open in this project | Every material class and legal position |
| All six-piece endgames | Open in this project | Every material class and legal position |
| All seven-piece endgames | Open in this project | Every material class and legal position |
| **Full Syzygy parity (through seven pieces)** | **Open** | **Complete class coverage, 50-move WDL and DTZ parity** |

Session change: S050 formally verified effective-ep normalization preserves legal moves and their full endpoints; 28 bundles remain frozen and material-class coverage is unchanged.

## Full installed S051 prompt

# NEXT SESSION — S051: Freeze effective ep normalization preservation

Owner authorises consecutive sessions until told to stop. Follow AGENTS.md,
charter/protocol. Fetch ALL remote heads, merge prior unmerged work, latest main,
existing checkout. Commit/push branch, merge/push main, compare remote identities;
never force main. Full stable progress table, Syzygy last, immediate session delta.

## Starting point and principal task

S050 formally verified EC-C031 at OWN full proof-source
4d47b33549fc5286099cae0bd89de76b05fbeb42. Twenty-eight bundles frozen before
this session. Read actual S050 evidence/closeout, standalone paper and both audits,
NormalizationDefinitions/Normalization complete modules and all unchanged imports,
EC-T0026/27/28 manifests, charter/protocol/roadmap/candidates, S032 specification.

Separate exact-source Gate Z for EC-C031, no Lean source changes. Main
RawRepetition.normalizeEP_preserves: for EVERY raw q,m,
isLegal(normalizeEP q)m=isLegal q m AND
(isLegal q m=true → play(normalizeEP q)m=play q m).
Shared NEW normalizeEP definition replaces ep with frozen effectiveEP.
Review exact paper/Lean: available EP gives identity; no-EP/nonshape invokes
OrdinaryEP then same-turn self-check; no-EP/shape contradicts original legality
using legalEP_iff_shape and proves normalized pseudo false by nonzero dx,
empty destination and none marker. Legal-only endpoint equality essential;
illegal EP raw play equality NOT asserted. Both colours/all promotion/raw flags,
no history/material/terminal filter, no adverse reply pruning. Same-agent audit
transparently named, no enumeration/engine/tablebase/stored certificate/full-game
run/novelty claim. Review retained initial incremental simp failure/correction.

ONE NEW GitHub clone at OWN FULL proof-source SHA above, .lake absent before
full lake build then COMPLETE AxiomCheck. Official core Lean4.35.0, standard-three
subsets only, inspect exact main. Retain full logs/commands/exits/times/UTC,
toolchain/executable, all source/transitive SHA256, clean HEAD/tree/status; compare
whole actual S050 report and all formal source bytes. ONE fresh build at a time.
Hosted CI unobserved unless inspected. Only observed success permits immutable
EC-T0029/v1.md, freezing BOTH complete NormalizationDefinitions and Normalization
modules, and exactly one appended ledger row. Prior 28 rows and every prior
source/paper/audit/evidence/manifest byte preserved. No incremental build when no
source edit. Relevant ledger tests/structure, evidence/preservation/document checks;
no unrelated diagnostics/trivial tests. If failure, record honestly, no fake freeze.

## Closeout and next step

Update candidate/roadmap/README/session ledger/theorems index/progress; write
sessions/S051_FREEZE_EFFECTIVE_EP_NORMALIZATION.md with actual complete evidence
and FULL installed S052 prompt. Commit/push/merge/push and compare remotes;
continue under standing authorisation until told to stop.

S052 may select the normalized-key congruence prerequisite after its own complete
paper/audit: NEW shared definition key q := normalizeEP q, and one NEW theorem
module for ∀q,r, key q=key r → ∀m,
isLegal q m=isLegal r m ∧ (isLegal q m=true → play q m=play r m).
Use exact normalized identity, frozen preservation twice and endpoint equality
transitivity. Include every actual Move/promotion; key equality is FULL normalized
Position equality (board function, turn, rights, effective target), never board-only
or a guessed finite hash. This establishes move/endpoint congruence, not yet the
full FIDE Article9.2.3 iff or historical rights correctness. Select exact smallest
claim after reviewing raw key definitions/specification; do not invent executable
key hashing/decidable search from noncomputable definitions. Later count instantiation
must use consistent key equality and include full history/root/current.

No FIDE key/rights-history correspondence, claims/no-earlier-terminal/adjudication,
automatic draws/mate precedence, strategy lifting, numerical KRK, holding/outcome,
WDL/DTZ/Syzygy or initial-position result follows from this normalization freeze.

Use available cloud runtime guidance/status, network policy and inherited proxy/CA.
ELAN_HOME=/workspace/.tools/elan, official core Lean4.35.0, no dependencies/shim.
Lake in formal/, Python at root; one fresh build, TLS/checksums unchanged.
