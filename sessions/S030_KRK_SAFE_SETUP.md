# S030 — Arbitrary KRK safe setup and clock-free forcing classification

**Outcome:** EC-C011 and EC-C019–021 are FORMAL_VERIFIED, awaiting Gate Z.
The principal arbitrary strong-turn target and the weak-turn terminal/capture
classification both close. No theorem ledger change; eleven frozen bundles.

## Exact new mathematics

- `krk_strong_arrival_force`: for either σ and arbitrary flags, exact
  `IsKRK q σ S R W`, `q.turn=σ`, and `∃p, Legal p q` imply `ForceMate σ q`.
  The stronger `krk_strong_force_of_not_check` only requires the weak king to
  be out of check, so the geometric proof needs no assumed source predecessor.
- `krk_weak_force_iff`: on the weak turn, forcing iff actual mate OR a nonempty
  legal reply set in which no reply leaves KK. The safety-form equivalent is
  actual mate OR a distant/protected rook with at least one reply. Stalemate
  does not win; ANY legal capture supplies a dead-KK holding action.
- C019: actual unprotected capture and necessary weak-turn safety; exact strong
  move projection with no source castling. C020: finite alternating strategy
  transport with actual terminal preservation, witnessed nonempty branches and
  ALL defending replies; coordinate axes/directions. This is deliberately not
  an unrestricted kernel symmetry theorem.
- C021: safe bounded setup. An off-rank far retreat may lose its original
  two-rank king gap; the proof then switches axes and proves perpendicular
  safety. Same-rank positive cases retreat the strong king; back-rank cases
  use protected rook entry, with king alignment first when needed. Reply
  witnesses exclude stalemate. No setup recursion or assumed continuation.

The exact final [paper](../proofs/EC-C019_C021_KRK_SAFE_SETUP.md), retained
[development notes](../proofs/EC-C019_C020_KRK_TRANSPORT.md),
[paper audit](../audits/EC-C019_C020_PAPER.md),
[Lean audit](../audits/EC-C019_C021_LEAN.md) and
[strategy record](../research/S030_STRATEGY_ATTEMPT.md) give the argument and
attempted falsifications. Reviews are same-agent, not independent external
reviews. A failed development-note append used the wrong working directory;
that provenance is recorded, and the final paper supersedes intermediate scope
notes. Interim elaboration failures were corrected and are not reported as
successful runs.

Ten new Lean modules, CaptureSafety through SetupExamples, add 24 public theorem
declarations. All earlier Lean sources apart from additive aggregate imports
and AxiomCheck entries are unchanged. Frozen theorem records and all S028/S029
anchors are byte-identical. Fixed controls prove back-rank preparation, black
file-axis setup with arbitrary flags, and that the S029 naive-capture setup
wins before the bad moves but loses forcing after each of them.

## Observed verification and publication

Exact published **proof-source `4acc3e8638a916f329788d4c2b5f0db6f2c9bf67`**, on `session/s030-safe-setup` before
fresh verification. Core-only official Lean 4.35.0, release commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, no dependencies or host shim.
No TLS/checksum verification disabled.

- Incremental `lake build` and `lake env lean AxiomCheck.lean`: exit 0.
- NEW GitHub clone `/tmp/engame-s030-gate-f`, detached at the full SHA, no
  `formal/.lake` before build: **51 jobs, exit 0, 336.763s**.
- Full exact statements/axioms: exit 0, **259 reports**, including all 24 new
  declarations. 228 standard-three; 18 propext/Quot.sound; 8 propext; 5 axiom-
  free. No sorryAx/native reduction. Byte-identical working/clean reports and
  every Lean source byte match. Verified UTC `2026-10-19T12:16:49Z`.
- Zero forbidden tokens in ten new modules; all 100 protected prior Lean files
  and theorem records unchanged. Hashes retained.
- `python3 -m unittest discover -s tests -v`: **39 tests passed, 104.760s**,
  no failures or skips. Existing diagnostics and fixed controls are supplementary,
  never a general-proof oracle. No new Python diagnostic was needed.
- `python3 scripts/validate_ledger.py`: **11 frozen bundles**, structure only.
- Hosted CI **not observed**. Local observed checks are the evidence.

Full logs and machine-readable counts: [evidence](evidence/S030/README.md).
The closing documentation commit retains the identical Lean proof-source bytes,
updates current status and installs S031. Session publication follows AGENTS:
push the session branch, fast-forward main, push main and verify remote SHA.
The exact proof-source anchor above is immutable; the closing commit carries
this report rather than trying to cite its own circular commit identifier.

## Limits and next work

EC-C011 is completed only in the frozen **clock-free** forcing semantics.
No full FIDE WDL, clock/repetition, numeric optimal mate distance, DTZ, seven-
piece or initial-position result is claimed. All new results still await Gate Z;
no theorem ledger row or frozen manifest changed. No mathematical setup gap
remains in the stated flagships. S031 is the separate review/freeze session;
its follow-on prompt must preserve the remaining rule/distance obligations.

## Repeatable progress table

| Endgames / target | Progress | Remaining |
|---|---|---|
| K vs K | Draw proved and frozen | — |
| K+B vs K | Draw proved and frozen | — |
| K+N vs K | Draw proved and frozen | — |
| K+R vs K | Dead/live frozen; clock-free forcing classified and formally verified | Freeze new results; FIDE rule/distance parity |
| K+Q vs K | Open in this project | General proof and formal verification |
| K+P vs K | Open in this project | General proof and formal verification |
| All four-piece endgames | Open in this project | Every material class and legal position |
| All five-piece endgames | Open in this project | Every material class and legal position |
| All six-piece endgames | Open in this project | Every material class and legal position |
| All seven-piece endgames | Open in this project | Every material class and legal position |
| **Full Syzygy parity (through seven pieces)** | **Open** | **Complete class coverage, 50-move WDL and DTZ parity** |

Session change: S030 proved arbitrary strong-turn KRK safe setup and the weak-turn terminal/capture classification, completing EC-C011 in the clock-free kernel; the frozen count stays eleven.

## Full installed next-session prompt

```markdown
# NEXT SESSION — S031: Freeze the verified KRK forcing development

**Owner instruction:** Execute when the owner says “run next session” or pastes/links
this prompt. Follow `AGENTS.md`: fetch all remote branches and latest main, merge
any earlier unmerged session work first, work in this existing checkout, and end
committed, pushed and merged to main without force. Publication is authorised.

**Closing report:** update `docs/SESSION_PROGRESS.md`; copy the complete stable
table into the written closeout and final reply, with full Syzygy parity last
and the session delta immediately below. Preserve the baseline material rows.

## Starting evidence and scope

Eleven frozen bundles remain, not eleven solved material classes. Read the
charter and `docs/PROOF_PROTOCOL.md`, current README/roadmap/candidates, S027
freeze manifests, S028/S029/S030 papers/audits/closeouts/evidence first.

Three published proof-source anchors hold the new forcing development:

- S028: `cb5d3bb713257d7cac8e3c1f9d82d8e77b746d6c` — EC-C014 actual phase
  image and EC-C015 bounded upper-band rank advance/rescue. Fifteen public
  declarations, core Lean 4.35.0; Gate F in `sessions/evidence/S028/`.
- S029: `3ead1d587f4ff5e129f73666bd466f5eac764223` — EC-C016 two-file
  checking, EC-C017 bounded conditional pursuit, EC-C018 closed separated-wall
  ForceMate. Twenty-three public declarations; Gate F in `sessions/evidence/S029/`.
- S030: `4acc3e8638a916f329788d4c2b5f0db6f2c9bf67` — EC-C019 exact ordinary
  KRK interface/capture safety; EC-C020 restricted alternating strategy transport
  and all axes; EC-C021 finite arbitrary safe setup; EC-C011 weak-turn forcing
  classification. Twenty-four public declarations in ten new modules; exact
  Gate F evidence in `sessions/evidence/S030/`. Check its recorded results rather
  than inferring success from this prompt. Final paper:
  `proofs/EC-C019_C021_KRK_SAFE_SETUP.md`.

The strong flagship `krk_strong_arrival_force` has only exact `IsKRK`, strong
turn and existence of a legal incoming move, either colour and arbitrary flags.
The stronger geometric theorem assumes the weak king is not in check.
`krk_weak_force_iff` is actual mate OR a nonempty reply set with NO legal KK
capture. The safety-form corollary is also proved. This completes the intended
clock-free EC-C011 target; it does not supply clocks/repetition, optimal
numeric distance, DTZ, general FIDE WDL or an initial-position theorem.

## Principal task: Gate Z, not more setup research

Review exact paper-to-Lean fidelity and the existing same-agent audits. All new
proofs must remain unchanged; corrections, if necessary, go in new modules or
versions and cannot inherit the old Gate F claim without new evidence.

Freeze the eligible development as coherent bundles, using the next free IDs
EC-T0012 onward. A reasonable mapping is C014; C015; C016; C017; C018; C019;
C020; C021 together with the completed C011 classification. Verify this mapping
against the actual declarations and avoid duplicate or overstated ledger rows.
A conditional pursuit theorem must keep its continuation hypothesis explicit;
the wall and full setup flagships must not acquire such a hypothesis. Do not
rename clock-free forcing classification as full FIDE WDL.

1. For each of the three exact proof-source SHAs, make a NEW fresh GitHub clone
   with no `formal/.lake` before `lake build`, as Gate Z requires. A single run
   per SHA may serve every bundle anchored there. Retain the complete build,
   axiom/statement checks, toolchain identity, hashes and forbidden-token scan.
   Do not reuse the Gate F checkout as fresh Gate Z evidence or rerun unrelated
   historical certifications. Subsequent checks are incremental.
2. Inspect the exact `#check` and `#print axioms` results for every declaration
   listed in each manifest. Allowed subsets: propext, Classical.choice,
   Quot.sound only. No sorryAx, native reduction, extra axioms or proof escapes.
3. Create immutable `theorems/frozen/EC-T00xx/v1.md` manifests with full exact
   source SHA, theorem/module list, exact hypotheses/quantifiers, rule/semantic
   boundary, source/audit attribution, toolchain and observed fresh Gate Z data.
   Record all constituent modules/hashes; helpers and shared new definitions
   must not silently fall outside the frozen source boundary. Previous sources,
   manifests and ledger rows stay byte-identical.
4. Only then append the new FROZEN rows to `theorems/LEDGER.csv`, preserving its
   schema; update candidate records and current status. Run ledger structural
   validation and relevant existing checks. Any diagnostics are supplementary,
   never a substitute for a general proof. No engine/tablebase or class-wide
   enumeration supplies a theorem.
5. Retain fixed capture/stalemate/chase controls. State that all setup/reply
   quantifiers are covered, while finite rank is not an optimal numeric distance.
   Distinguish observed local verification from any unobserved hosted CI.

## Follow-on research prompt

After freezing, install S032 around a concrete next obligation. Prefer a short
mathematical design session for the remaining KRK rule/distance layer: define
clock and repetition semantics, terminal precedence and the exact relationship
to the existing clock-free ForceMate; specify the outcome/distance target and
what needs proof. Do not label clock-free mate bounds as 50-move WDL/DTZ parity,
and do not change frozen game definitions. If moving to another material class
instead, justify the choice against `docs/ROADMAP.md` and preserve outstanding
KRK rule/distance work explicitly. Avoid starting a large unplanned theorem
while the Gate Z publication is still unfinished.

Write `sessions/S031_FREEZE_KRK_FORCING.md`, including all actual check results,
exact anchors, ledger effect, full progress table and the FULL installed S032
prompt. Update the session ledger/current status, commit/push the branch, merge
main, push main and verify remote SHA. Frozen counts are bundles, not solved
material classes; report any blocker precisely rather than upgrading a claim.

## Cloud activation

`export ELAN_HOME=/workspace/.tools/elan; export PATH="$ELAN_HOME/bin:$PATH"`.
Lake commands run from `formal/`, Python from root. Official unmodified Lean
4.35.0, core only, no external dependencies; no host shim was required in S030.
Keep TLS/signature/checksum verification enabled. No new worktree is needed.
```
