# S046 — Kernel characterization of actual legal en-passant

2026-10-20, base main 3e5f693b90d2f3420effc630aba09677bc971d72;
branch session/s046-legal-ep-characterization. Explicit all-heads fetch, no
prior unmerged session, existing checkout, publication/consecutive run authorised.

## Result and proof fidelity

**EC-C029 FORMAL_VERIFIED, Gate Z pending.** One new EPCharacterization module
imports frozen RawRepetition.Definitions unchanged. Main legalEP_iff_shape:
for EVERY raw q,m, LegalEP iff actual isLegal + source Pawn + distinct files +
empty destination. Marker/flank equations RECOVERED, not assumed on RHS.
Forward projects clauses. Backward preserves original legality, proves dx≠0
by finite-file equality/Fin.ext/integer omega, extracts isPseudo then pawnMoveOK
using exact source pawn, eliminates dx=0 single/double and occupied-dst capture,
and obtains raw ep/opposing flank from remaining EP branch. Both colours, raw
flags and every actual Move/promotion field retained. No enumeration, extra
shared definitions/corollaries, seeds, erased-history or terminal/strategy filter.

[Paper](../proofs/EC-C029_LEGAL_EP_CHARACTERIZATION.md) and
[adversarial audit](../audits/EC-C029_LEGAL_EP_PAPER.md) saved BEFORE Lean;
[Lean fidelity](../audits/EC-C029_LEGAL_EP_LEAN.md). Same-agent reviews, not
independent external audit. Symbolic straight/ordinary-capture/nonpawn/missing-
wrong-flag-flank/both-colour/pseudo-only-self-check controls found no gap.
No concrete pinned or compatible full promotion/ep/castling/threshold game run.
Classical kernel branch reasoning, no novelty/tablebase/engine/certificates.

## Observed verification

OWN source **421608f5b20fee055bc3cb9d0c5904b0d192527b** published BEFORE ONE NEW GitHub clone
**/tmp/engame-s046-gate-f**, detached FULL exact SHA; no .lake before build.
Full **74-job lake build exit 0, 465.649s**, COMPLETE **AxiomCheck exit 0**,
UTC **2026-10-20T09:04:07Z**, **276 allowed reports** (244 standard-three,
18 propext/Quot.sound, 9 propext, 5 axiom-free), main standard-three only.
Exact main inspected; entire working/clean report identical. Every formal byte
matches own anchor; full source/transitive hashes and clean HEAD/tree/status
retained. One new module forbidden scan zero. Incremental build/full authoring
runner passed FIRST attempt, no warnings/failures or repeated clean build.
Official unmodified core Lean4.35.0 release eb6cafb7290e8bd5f2937522d8d804f58f02bafc,
no dependency/shim. Existing elan/Git proxy/network policy sufficient, no setup
or TLS/checksum change. Hosted CI unobserved. [Evidence](evidence/S046/README.md).
Relevant ledger structure, source/record preservation, evidence/full table/prompt/
local-link/diff checks passed. Prior formal/candidate source/papers/audits/session/
evidence/manifests and 26 ledger rows unchanged; aggregate import/runner additive.
No unrelated diagnostics/trivial tests.

## Limits and next session

No theorem that effective-ep normalization preserves legal moves/played endpoints,
full repetition key/Article9.2.3/rights-history correspondence, low-count
certificate, claims/terminal admissibility/adjudication/mate precedence, full Layer/
strategy extraction/lifting, numerical KRK, holding/outcome, DTM/DTZ/WDL/Syzygy
or initial-position result. Raw flags not certified lawful. S047 installs separate
OWN exact-source freeze. A later normalization candidate needs its own complete
paper/audit of every raw ep use, ordinary/pawn/castling/self-check cases and exact
played endpoint/updated flags; no such result assumed here. Commit/push branch,
merge/push main and compare remote SHAs; final identity in Git history/observed
publication checks. Continue installed S047 under standing authorisation.

## Required progress table

| Endgames / target | Progress | Remaining |
|---|---|---|
| K vs K | Draw proved and frozen | — |
| K+B vs K | Draw proved and frozen | — |
| K+N vs K | Draw proved and frozen | — |
| K+R vs K | Dead/live and clock-free forcing frozen; projection, raw trace/clock and generic key counting frozen; effective-ep target frozen; EP event characterization formally verified | FIDE history/adjudication and distance |
| K+Q vs K | Open in this project | General proof and formal verification |
| K+P vs K | Open in this project | General proof and formal verification |
| All four-piece endgames | Open in this project | Every material class and legal position |
| All five-piece endgames | Open in this project | Every material class and legal position |
| All six-piece endgames | Open in this project | Every material class and legal position |
| All seven-piece endgames | Open in this project | Every material class and legal position |
| **Full Syzygy parity (through seven pieces)** | **Open** | **Complete class coverage, 50-move WDL and DTZ parity** |

Session change: S046 formally verified the kernel legal-en-passant event characterization; 26 bundles remain frozen and material-class coverage is unchanged.

## Full installed S047 prompt

# NEXT SESSION — S047: Freeze the kernel legal-en-passant characterization

Execute as next authorised session. Follow AGENTS.md: explicitly fetch ALL remote
heads, merge earlier unmerged work, read latest main prompt, existing checkout/no
worktree. Publication authorised. Commit/push branch, merge/push main, compare
remote SHAs; never force main. Update/reproduce FULL stable progress table in
closeout/owner report, Syzygy parity LAST, one sentence delta below. Continue
installed sessions until owner stops. Bundles are not solved material classes.

## Starting point and required reading

S046 establishes EC-C029 at Gate F only. OWN FULL published proof-source:
`421608f5b20fee055bc3cb9d0c5904b0d192527b`.
Read charter/protocol/roadmap/candidates, S032 repetition/claim specification,
EC-T0021–0026 manifests, frozen RawRepetition Definitions/EffectiveEP,
RawClock.Pawn, Rules.Board dx and Moves isLegal/isPseudo/pawnMoveOK/play,
proofs/EC-C029_LEGAL_EP_CHARACTERIZATION.md and both EC-C029 audits,
sessions/S046_LEGAL_EP_CHARACTERIZATION.md and actual sessions/evidence/S046/
logs/summary/source/transitive hashes/clean identity. Twenty-six bundles frozen.

## Principal task: one OWN exact-source Gate Z obligation

Review paper-to-Lean fidelity BEFORE freeze. Complete new bundle is exactly
formal/EndgameChess/Rules/RawRepetition/EPCharacterization.lean, one main
EndgameChess.Rules.RawRepetition.legalEP_iff_shape. For every raw q,m:

 LegalEP q m ↔ isLegal q m=true ∧ RawClock.Pawn q m ∧
   m.src.file≠m.dst.file ∧ q.board m.dst=none.

Raw ep marker/opposing flank pawn are RECOVERED, not RHS premises. Actual
legality retained including self-check/promotion fields. Backward proof shows
dx≠0 using Fin.ext/integer arithmetic, extracts isPseudo/pawnMoveOK from actual
legality and source pawn, excludes single/double by dx and ordinary capture by
empty dst, then reconstructs LegalEP from EP branch flag/flank. No enumeration,
extra definitions, seed, erased-history surrogate or terminal/material/side filter.

Use ONE NEW GitHub Gate Z clone at OWN FULL SHA above, no .lake before build.
Full lake build THEN COMPLETE AxiomCheck must pass. Inspect exact main and
standard-three subset axioms. Retain full logs/commands/exits/timings/UTC,
official toolchain identity, all source/transitive hashes, clean HEAD/tree/status.
Compare ENTIRE report with actual S046 Gate F. No reuse of clone/cache, re-anchor
of unchanged proof or unrelated verification. No Lean edit/incremental build expected.

Only on actual success freeze EC-C029 as next unused ID, expected EC-T0027
(inspect ledger first). Add immutable manifest recording COMPLETE module,
exact theorem/source/axioms, own SHA, paper/audit/trust links and fresh Gate Z
results. Append exactly one ledger row preserving prior bytes. If fidelity/build
fails, record blocker, do not freeze or edit old source or manufacture success.

## Audit and semantic limits

Recheck straight single/double, ordinary occupied captures, nonpawns, missing/
wrong marker/flank, both colours, promotion fields and pseudo-only/self-check
ep. Distinct files is not itself full capture geometry; actual legality supplies
the remaining kernel constraints. No concrete pinned/initial-rooted full
promotion/ep/castling/threshold game claimed run. Symbolic branch controls only.
No ep-normalization preservation, full repetition key/Article9.2.3/rights-history
correspondence, low-count certificate, claims/admissibility/adjudication/mate
precedence, full Layer/strategy extraction/lifting, numerical KRK, holding/outcome,
DTM/DTZ/WDL/Syzygy or initial-position result. No adverse reply pruning,
tablebase/engine/enumeration/stored certificates/arbitrary-clock KRK witness or
novelty claim. Raw malformed flags not certified as lawful FIDE histories.

## Verification, next obligation and closeout

Preserve all prior formal/candidate/frozen source/papers/audits/evidence/manifests.
Prior ledger prefix plus exactly one new row. Aggregates unchanged unless
actually needed additively. Run relevant ledger structure/tests, preservation/
evidence/document checks; no unrelated diagnostics/trivial tests. Update candidate,
roadmap/README/theorem index, session ledger/progress table. Write
sessions/S047_FREEZE_LEGAL_EP_CHARACTERIZATION.md with actual evidence and FULL
installed S048 prompt. Commit/push/merge/push, compare remote SHAs; hosted CI
unobserved unless inspected. Continue only installed next prompt.

Choose next small obligation from actual results. A useful candidate is raw
ep-field normalization: NEW normalizeEP(q)={q with ep:=effectiveEP(q)}, explicitly
noncomputable, preserving board/turn/castling. Consider the combined exact target
for EVERY q,m:

 isLegal (normalizeEP q) m = isLegal q m AND
 (isLegal q m=true → play (normalizeEP q) m = play q m).

Do NOT assume this result. Fix paper/adversarial audit before registering the
next candidate/Lean. Inspect ALL ep uses in kernel legality/play, including
canCastle and self-check. If an actual legal ep exists, normalization is q
itself. Otherwise both positions admit no legal empty-dst file-changing pawn
move (use characterization and absent normalized flag). For all other moves,
prove pseudo-legality/play effects independent of raw ep: same-file pawn moves
cannot satisfy capture geometry, occupied destinations cannot trigger ep,
nonpawns do not use pawn ep branch, and castling tests do not read ep. Prove
these facts, including exact played endpoint/updated flags, rather than pruning
or assuming them. Missing marker, pseudo-only/pinned ep, both colours, malformed
raw flags, ordinary captures/quiet/castling/promotion moves are audit risks.
If too broad or falsified, record honest gaps and select the smallest well-posed
prerequisite; no automatic full FIDE key/claim result follows. Never edit frozen
Definitions to add normalization; use a NEW shared definitions module.

## Cloud activation

Use available runtime guidance, inspect network policy, reuse inherited Git proxy.
Official core Lean4.35.0, no dependency. ELAN_HOME=/workspace/.tools/elan; prepend
bin to PATH. Lake in formal/, Python at root. ONE fresh build at a time, TLS/
checksums unchanged. Existing environment suffices absent actual blocker.
