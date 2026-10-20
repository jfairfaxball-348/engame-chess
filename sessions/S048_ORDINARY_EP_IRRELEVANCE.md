# S048 — Ordinary ep-marker irrelevance

2026-10-20, base main 66e7638f8c9da89dd326d74165342343afacf62c;
branch session/s048-ordinary-ep-irrelevance. Explicit all-heads fetch, no unmerged
prior work, existing checkout; owner resumed consecutive sessions and publication.

## Result

EC-C030 FORMAL_VERIFIED; Gate Z pending. Every raw q,m,e, outside source-Pawn,
distinct-file, empty-destination shape: marker replacement preserves isPseudo
and FULL play. No legality/reachability/history premise. Paper and separate
same-agent adversarial review saved before Lean; not independent external audit.
[Paper](../proofs/EC-C030_ORDINARY_EP_IRRELEVANCE.md),
[paper audit](../audits/EC-C030_ORDINARY_EP_PAPER.md),
[Lean review](../audits/EC-C030_ORDINARY_EP_LEAN.md).

Raw epCapture false for both markers by guard; unfolding play preserves board
function, turn, castling and freshly recomputed ep. Source/colour/kind analysis
isolates pawnMoveOK; equal files make capture geometry false, occupied destination
makes EP test false. Absent/wrong-colour/nonpawn/king/castling, promotion,
source=destination, both colours and arbitrary markers handled symbolically.
No concrete pinned/full promotion/castling/threshold game run; no enumeration,
engine/tablebase, stored certificates or novelty claim.

## Observed checks and publication

Own source `c4c900036dcffd209d6c08f27e2323637852c940`; new exact GitHub clone, no .lake before build; 75-job build exit 0 in 502.587s; complete AxiomCheck exit 0 at 2026-10-20T12:05:15Z, 277 allowed reports. Main standard-three; entire working/clean output byte-identical.
[Evidence](evidence/S048/README.md). Exact main inspected; official core
Lean4.35.0, no dependency/shim. Full command/exits/timings/UTC/toolchain, formal
source/transitive hashes and clean HEAD/tree/status retained. New module forbidden
scan zero. Final incremental changed module/importer build and full working
runner passed. One first incremental failure retained, fixed wrong-colour Boolean
simplification without changing statement. Initial shell cwd error wrote no source;
empty stray directories removed. Root-cwd elan identity lookup failed, succeeded
in formal/. Clean build/runner succeeded once, no repeated clean build. Runtime
current/connected/unrestricted; inherited proxy/CA/toolchain unchanged.
Relevant ledger/evidence/preservation/full-table/full-prompt/local-link/diff checks
passed. All prior protected sources/papers/audits/evidence/manifests and 27 ledger
rows unchanged; aggregate imports/runner additive. No unrelated diagnostics/tests.
Hosted CI unobserved. Proof source published before fresh clone. Closeout commit,
branch push, main merge/push and remote identity recorded in Git/publication checks.

## Limits and continuation

Conditional raw-kernel lemma only. ¬LegalEP alone does not justify equality of
raw play for illegal EP-shaped moves. No normalization/FIDE key/rights-history,
claim/adjudication/mate precedence, strategy lifting, numerical KRK, WDL/DTZ or
solved material-class upgrade. S049 separate exact-source freeze installed;
continue under standing owner authorisation until told to stop.

## Required progress table

| Endgames / target | Progress | Remaining |
|---|---|---|
| K vs K | Draw proved and frozen | — |
| K+B vs K | Draw proved and frozen | — |
| K+N vs K | Draw proved and frozen | — |
| K+R vs K | Dead/live and clock-free forcing frozen; projection, raw history/clock/key-count and legal-ep prerequisites frozen; ordinary ep irrelevance formally verified | FIDE history/adjudication and distance |
| K+Q vs K | Open in this project | General proof and formal verification |
| K+P vs K | Open in this project | General proof and formal verification |
| All four-piece endgames | Open in this project | Every material class and legal position |
| All five-piece endgames | Open in this project | Every material class and legal position |
| All six-piece endgames | Open in this project | Every material class and legal position |
| All seven-piece endgames | Open in this project | Every material class and legal position |
| **Full Syzygy parity (through seven pieces)** | **Open** | **Complete class coverage, 50-move WDL and DTZ parity** |

Session change: S048 formally verified ordinary ep-marker irrelevance outside the raw EP shape; 27 bundles remain frozen and material-class coverage is unchanged.

## Full installed S049 prompt

# NEXT SESSION — S049: Freeze ordinary ep-marker irrelevance

Owner resumed consecutive sessions on 2026-10-20: continue through session
closeouts until told to stop. Follow AGENTS.md and docs/PROOF_PROTOCOL.md.
Explicitly fetch ALL remote heads, merge prior unmerged work, start latest main
in existing checkout. Publication authorised: commit/push branch, merge/push
main, compare remote SHAs, never force main. Reproduce FULL stable progress
table, Syzygy last, followed immediately by one-sentence session delta.

## Starting point and task

S048 formally verified EC-C030, ordinary_ep_irrelevance, at OWN proof-source
c4c900036dcffd209d6c08f27e2323637852c940. Read actual S048 summary/logs,
proofs/EC-C030_ORDINARY_EP_IRRELEVANCE.md and both audits; complete OrdinaryEP
module and its unchanged frozen imports; charter/protocol/roadmap/candidates,
S048 closeout, S032 specification. Twenty-seven bundles frozen before this freeze.

Principal task: separate exact-source Gate Z for EC-C030. Audit exact paper/Lean
fidelity and all raw ep uses: guard excludes source-Pawn/distinct-files/empty-dst
shape; no actual legality premise. Marker replacement preserves Boolean isPseudo
and FULL play, including output ep recomputation, castling, promotions and board
function. Review absent/wrong-colour/nonpawn/king/castling, same-file/occupied
pawn cases, both colours, source=destination, arbitrary markers. ¬LegalEP alone
is insufficient for total raw play equality. Same-agent review must not be
called independent external audit. No new source edits, enumeration or oracle.

Run ONE NEW GitHub clone at OWN FULL proof-source SHA above, ensure formal/.lake
absent before full lake build and COMPLETE AxiomCheck. Official core Lean4.35.0,
standard-three axiom subsets only; inspect exact main, compare entire S048 report,
all formal bytes, full source/transitive SHA256, clean HEAD/tree/status, retain
commands/exits/times/UTC/toolchain identity. ONE fresh build at a time. Hosted CI
unobserved unless actually inspected. Only observed success permits immutable
EC-T0028/v1.md and exactly one appended ledger row. Preserve all prior source,
papers/audits/evidence/manifests and 27 rows byte-for-byte; no source/incremental
build needed when source unchanged. Run relevant ledger tests/structure and
preservation/evidence/document checks; no unrelated diagnostics/trivial tests.

## Closeout and continuation

Update candidate/roadmap/README/session ledger/progress; write
sessions/S049_FREEZE_ORDINARY_EP_IRRELEVANCE.md with actual complete evidence and
FULL installed S050 prompt. Commit/push/merge/push and verify remote identities.
Continue S050 under standing owner authorisation unless stopped.

Prepare S050 for effectiveEP normalization preservation, only after a complete
standalone paper/audit: define normalizeEP q={q with ep:=effectiveEP q} in a NEW
shared definitions module and one NEW main theorem module. Intended statement
for all raw q,m: isLegal(normalizeEP q)m=isLegal q m AND
(isLegal q m=true → play(normalizeEP q)m=play q m).
Available EP means normalized q=q. Without legal EP, ordinary moves use EC-C030
plus inCheck unchanged; EP-shaped moves cannot be legal in original q by frozen
legalEP_iff_shape. Normalized marker none makes pawnMoveOK false on that shape:
dx≠0 removes straight moves, empty dst ordinary capture, none marker EP. Prove
both illegality directions without assuming compatible histories or raw play
equality for illegal EP shapes. No full FIDE repetition key/rights correspondence,
claims/adjudication, strategy lifting, numerical KRK, WDL/DTZ or solved class claim.

Use cloud runtime guidance/status/network policy, inherited proxy/CA and existing
ELAN_HOME=/workspace/.tools/elan. Lake in formal/, Python at root. No toolchain,
dependency, TLS/checksum changes absent an actual blocker.
