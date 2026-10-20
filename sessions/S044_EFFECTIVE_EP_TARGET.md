# S044 — Legality-filtered en-passant availability and effective target

2026-10-20, base main 52f28df8cc60c91f9c5c27712fb072983476e33e;
branch session/s044-effective-ep-target. Explicit all-heads fetch, no earlier
unmerged session, existing checkout. Publication/consecutive execution authorised.

## Result and exact scope

**EC-C028 FORMAL_VERIFIED, Gate Z pending.** Shared RawRepetition/Definitions
and one main EffectiveEP/effectiveEP_spec. LegalEP requires actual isLegal,
frozen Pawn, q.ep=some m.dst, distinct files, empty destination and opposing
flank pawn. It is the existing CaptureEvent EP event with legality; play's
epCapture remains a LOCAL let, not an exported predicate. effectiveEP is explicitly
NONCOMPUTABLE classical existence-filtered q.ep, no enumeration/search claim.

For EVERY raw q the combined main gives none iff no legal event, and some dst
iff an actual legal witness targets dst. Witness flag consistency proves the
available branch cannot be none or wrong-target; some injectivity identifies
all witness destinations. No independent target/count/clock seed, endpoint
hypothesis, pseudo-legal substitute or terminal/material/colour/strategy filter.
Arbitrary raw flags covered without asserting lawful preceding FIDE history.

[Paper](../proofs/EC-C028_EFFECTIVE_EP_TARGET.md) and
[adversarial audit](../audits/EC-C028_EFFECTIVE_EP_PAPER.md) saved BEFORE Lean;
[Lean fidelity](../audits/EC-C028_EFFECTIVE_EP_LEAN.md). Same-agent review, not
independent external audit. Symbolic absent flag/no eligible pawn/only pseudo-
legal self-check/multiple-source/occupied/wrong-kind-colour-flank/ordinary-move
controls found no local gap. No concrete pinned board or full compatible
promotion/ep/castling/threshold game run. Classical construction, no novelty,
tablebase/engine/enumeration or stored-position certificate.

## Observed verification

OWN source **28bdacfa34995ed3d778bfb2dab1654e46999f0c** published BEFORE ONE NEW GitHub clone
**/tmp/engame-s044-gate-f**, detached FULL exact SHA; no .lake before build.
Full **73-job lake build exit 0, 417.929s**, COMPLETE **AxiomCheck exit 0**,
UTC **2026-10-20T08:44:40Z**, **275 allowed reports** (243 standard-three,
18 propext/Quot.sound, 9 propext, 5 axiom-free); main standard-three only.
Definitions/main exact output inspected. Whole clean/working report identical;
every formal source matches exact anchor, full source/transitive hashes and
clean HEAD/tree/status retained. Two new modules forbidden scan zero.

First local compile failed because existential unpacking cleared `available`
while subsequent proof steps reused it. Reconstructing the actual witness
fixed the proof; a redundant simpa warning removed by direct contradiction
simplification. Full initial failure retained; mathematical definitions/statement
unchanged. Final incremental build/runner and fresh build/runner passed with no
warning. No repeated clean run. Official unmodified core Lean4.35.0 release
 eb6cafb7290e8bd5f2937522d8d804f58f02bafc, no dependency/shim. Existing elan/
Git proxy/network policy sufficient, TLS/checksums unchanged, no setup change.
Hosted CI unobserved. [Evidence](evidence/S044/README.md). Relevant preservation,
ledger structure, evidence/full table/prompt/local-link/diff checks passed;
no unrelated diagnostics/trivial tests. Prior source/papers/audits/session/
evidence/manifests and 25 rows unchanged; aggregates additive only.

## Limits and next session

No full repetition key or Article9.2.3/rights-history correspondence, low-count
certificate, claims/admissibility/adjudication/mate precedence, full Layer/
strategy extraction/lifting, numerical KRK mate bound, holding/outcomes,
DTM/DTZ/WDL/Syzygy or initial-position value. Frozen generic counts do not
upgrade this target spec to FIDE claims. S045 installs separate exact-source
freeze; a later precise kernel-fidelity EP characterization may precede any
normalization/key composition. Commit/push branch, merge/push main and compare
remote SHAs; final identity in Git history/observed publication checks. Continue S045.

## Required progress table

| Endgames / target | Progress | Remaining |
|---|---|---|
| K vs K | Draw proved and frozen | — |
| K+B vs K | Draw proved and frozen | — |
| K+N vs K | Draw proved and frozen | — |
| K+R vs K | Dead/live and clock-free forcing frozen; projection, raw trace/clock and generic key counting frozen; effective-ep target formally verified | FIDE history/adjudication and distance |
| K+Q vs K | Open in this project | General proof and formal verification |
| K+P vs K | Open in this project | General proof and formal verification |
| All four-piece endgames | Open in this project | Every material class and legal position |
| All five-piece endgames | Open in this project | Every material class and legal position |
| All six-piece endgames | Open in this project | Every material class and legal position |
| All seven-piece endgames | Open in this project | Every material class and legal position |
| **Full Syzygy parity (through seven pieces)** | **Open** | **Complete class coverage, 50-move WDL and DTZ parity** |

Session change: S044 formally verified legality-filtered en-passant availability and its effective-target specification; 25 bundles remain frozen and material-class coverage is unchanged.

## Full installed S045 prompt

# NEXT SESSION — S045: Freeze legality-filtered effective en-passant target

Execute as next authorised session. Follow AGENTS.md: explicitly fetch ALL remote
heads, merge earlier unmerged work, read latest main prompt, existing checkout/no
worktree. Publication authorised. Commit/push branch, merge/push main, compare
remote SHAs; never force main. Update/reproduce FULL stable progress table in
closeout/owner report, Syzygy parity LAST, one sentence delta below. Continue
installed sessions until owner stops. Bundles are not solved material classes.

## Starting point and required reading

S044 establishes EC-C028 at Gate F only. OWN FULL published proof-source:
`28bdacfa34995ed3d778bfb2dab1654e46999f0c`.
Read charter/protocol/roadmap/candidates, research/KRK_RULE_DISTANCE_SPEC.md
(repetition/claims), EC-T0021–0025 manifests, actual frozen RawClock Pawn and
CaptureEvent EP branch, Moves pawnMoveOK/isPseudo/isLegal/play, EC-C028 paper/
audits, sessions/S044_EFFECTIVE_EP_TARGET.md and actual sessions/evidence/S044/
full logs/summary/source/transitive hashes/clean-source identity. Twenty-five
bundles frozen; target bookkeeping is not full FIDE repetition/claims.

## Principal task: one OWN exact-source Gate Z obligation

Review paper-to-Lean fidelity before freeze. Complete new bundle boundary:
- formal/EndgameChess/Rules/RawRepetition/Definitions.lean
- formal/EndgameChess/Rules/RawRepetition/EffectiveEP.lean

One main: EndgameChess.Rules.RawRepetition.effectiveEP_spec.
LegalEP q m explicitly requires actual isLegal, frozen Pawn, q.ep=some m.dst,
distinct source/destination files, empty destination and opposing flank pawn.
It reuses the existing raw EP capture-event specification with legality, not
an exported epCapture name (that test is a local let in play). effectiveEP is
NONCOMPUTABLE classical existence-filtered q.ep; no search/enumeration claim.
Main for EVERY raw q proves:

 (effectiveEP q=none ↔ ¬∃m,LegalEP q m) AND
 (∀dst,effectiveEP q=some dst ↔ ∃m,LegalEP q m ∧ m.dst=dst).

Witness flag consistency proves the available branch is some at exactly its
actual target. No separate target/clock/count seed, pseudo-legal substitute,
terminal/material/side/strategy filter or lawfulness-of-raw-flags assumption.
All colours and arbitrary raw flags; no FIDE admissibility/key theorem.

Use ONE NEW GitHub Gate Z clone at OWN FULL exact SHA above, no formal/.lake
before build. Full lake build THEN COMPLETE AxiomCheck must actually pass.
Inspect exact LegalEP/effectiveEP definitions/main and standard-three subset
axioms. Retain full logs/commands/exits/timings/UTC, official toolchain identity,
all source/transitive hashes, clean HEAD/tree/status. Compare ENTIRE report
with actual S044 Gate F. No reuse of clone/cache or re-anchor of unchanged source.
No Lean source change/incremental build expected.

Only on actual success freeze EC-C028 as next unused ID, expected EC-T0026
(inspect ledger first). Add immutable manifest with complete definitions/proof
modules, exact definition/main/source/axioms, own SHA, paper/audit/trust links
and NEW Gate Z evidence. Append exactly one ledger row preserving prior bytes.
If fidelity/build fails, record blocker; do not freeze, alter frozen source or
manufacture success. Preserve prior S044 initial compile failure evidence.

## Audit and scope limits

Recheck no flag, flag/no eligible pawn, only pseudo-legal/self-check moves,
multiple sources/same target, occupied dst, wrong source kind/colour/flank and
ordinary pawn/capture moves. Symbolic controls only; no pinned-board/full
promotion/ep/castling/threshold history was constructed or required.
No complete repetition key/Article9.2.3/rights-history correspondence, low-count
certificate, claims/admissibility/adjudication/mate precedence, full Layer/
strategy extraction/lifting, numerical KRK bounds, holding/outcome,
DTM/DTZ/WDL/Syzygy or initial-position result. No tablebase/engine/enumeration,
arbitrary-clock KRK witness or novelty claim. No adverse reply pruned.

## Verification, next obligation and closeout

Preserve all prior formal/candidate/frozen source, papers/audits/evidence and
manifests. Prior ledger bytes prefix plus exactly one new row; aggregate Lean
files unchanged unless needed additively. Run relevant ledger structure/tests,
preservation/evidence/document checks; no unrelated diagnostics or trivial tests.
Update candidates, roadmap/README/theorem index, session ledger/progress table.
Write sessions/S045_FREEZE_EFFECTIVE_EP_TARGET.md with complete actual evidence
and FULL installed S046 prompt. Commit/push/merge/push; compare remote SHAs,
hosted CI unobserved unless actually inspected. Continue installed next prompt.

A useful next narrow obligation is a kernel-fidelity characterization of this
EP event BEFORE full key composition. Consider proving, for ALL raw q,m:

 LegalEP q m ↔ isLegal q m=true ∧ RawClock.Pawn q m ∧
   m.src.file≠m.dst.file ∧ q.board m.dst=none.

Forward direction projects existing clauses. Backward direction should extract
isPseudo from isLegal, specialize source pawn and pawnMoveOK, eliminate straight
single/double branches by distinct files and ordinary capture by empty dst,
and recover q.ep flag/opposing flank pawn from the remaining EP branch.
Inspect actual source and audit exact integer/file geometry before registering
EC-C029; do not assume the characterization or count malformed flags as lawful
histories. Use a standalone paper/adversarial audit BEFORE Lean. This would
validate the event boundary used for later ep normalization without asserting
a FIDE repetition key or numerical KRK bound. Select a well-posed statement
from actual results; if a gap/counterexample exists record it, do not weaken
legality or fabricate compatible full games.

## Cloud activation

Use available runtime guidance, inspect network policy, reuse inherited Git proxy.
Official core Lean4.35.0, no dependency. ELAN_HOME=/workspace/.tools/elan; prepend
bin to PATH. Lake in formal/, Python at root. ONE fresh build at a time, TLS/
checksums unchanged. Existing environment suffices absent actual blocker.
