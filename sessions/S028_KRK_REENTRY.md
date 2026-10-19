# S028 — Exact phase image and bounded upper-band contraction; re-entry still open

Date: 2026-10-19. Base main: `774d38486c5ebf448adf0585266bfdb43d8608d3`; initial fetch and clean tree; an expanded all-branch fetch at closeout confirmed every earlier remote branch is already merged into main. Session branch: `session/s028-reentry`. Proof-source: `cb5d3bb713257d7cac8e3c1f9d82d8e77b746d6c`, committed and pushed before the fresh Gate F run. This later closeout/status commit changes no proof source.

## Completed results and precise limit

**EC-C014 FORMAL_VERIFIED:** the actual two-reply image has rook one rank above strong king, lone king one or two above rook, at-most-two file offset, four-file rook/strong separation and distant rook. `krk_opposition_phase_image` retains the original check/all-first-replies/king-up/all-second-replies quantifiers, nonempty reply sets, exact Matches and Legal ancestry. This is a new proved refinement importing the frozen source, not a silent strengthening of EC-T0011.

**EC-C015 FORMAL_VERIFIED:** the entire upper band admits an explicit two-or-four-ply rank contraction. Choose rook-up; every reply either completes a distant barrier or is followed immediately by a chosen far-file rook rescue, then every reply. The rook rank is raised exactly one, 7−rookRank strictly decreases, and all required reply sets are nonempty. A two-file margin can leave the rook hanging on a strong turn; the prescribed rescue is proved legal before any further weak move. Three-file inputs finish without needing that extra repair. Both colours and arbitrary flags are parameters. See [image proof](../proofs/EC-C014_KRK_PHASE_IMAGE.md), [rank/rescue proof](../proofs/EC-C015_KRK_RANK_ADVANCE.md), [paper audit](../audits/EC-C014_C015_PAPER.md), [fidelity audit](../audits/EC-C014_C015_LEAN.md).

**The full S028 re-entry objective is not closed.** Non-aligned lower-band image inputs remain unresolved. A contraction can leave the strong king two ranks below the raised rook wall and grow file offsets; no recursively closed continuation invariant is proved. Safe setup from arbitrary legal KRK arrivals is also open. EC-C011 remains PROPOSED. No ForceMate conclusion for the whole image, general KRK WDL, clocks/repetition, distance theorem or initial-position draw is asserted.

## Sustained policy attempt and controls

The actual legal Kb2/Rh3/Kc4 → Kc2 Kb4 Kb2 Kc4 cycle refutes naive lateral chasing even within safe PhaseImage states. Kf6/Ra7/Kh8 → Rg7 is a protected-rook stalemate. Ka2/Re3/Kc4 → Re4+ Kc3 refutes dropping the upper-band premise. Ka2/Re3/Kc5 → Re4 Kd5 requires the new rook rescue; Rh4 is legal. Fixed kernel controls establish these concrete failures; additional local checks confirm all three other inputs are actual four-ply phase images (the chase prefix is kernel-checked); the independent local move-generator diagnostic is supplementary. No class-wide enumeration, stored values, engine or tablebase supplies a general proof.

An oriented pursue/wait approach and a candidate bounded two-tempo normalization are recorded in [strategy attempt](../research/S028_STRATEGY_ATTEMPT.md). Remaining obligations include all-reply normalization, direction changes at alignment, the d/e far-file switch, corners/nonempty replies and a measure proving finite pursuit. A new two-file checking lemma plus rescue may be needed; the frozen four-file phase must remain unchanged. S029 targets this mathematical gap rather than repeating definitions or treating the upper-band phase as a finished strategy.

## Observed verification

- Working incremental build and 212-report axiom check passed. Fifteen new theorem declarations across five new modules, all main statements inspected; frozen sources imported unchanged.
- New fresh GitHub checkout at the exact published proof-source, no .lake before build: **34 jobs, exit 0, 265.586 seconds**. Full axiom/statement runner exit 0, Gate F completed UTC `2026-10-19T09:06:21Z`. Allowed sets: 189 [propext, Classical.choice, Quot.sound]; 10 [propext, Quot.sound]; 8 [propext]; 5 axiom-free. Clean/working output is byte-identical; all working Lean source bytes match the fresh anchor.
- New five-module forbidden-token scan: zero. Source SHA-256 inventory retained. Existing theorem records (including all eleven frozen rows/manifests) and existing proof modules unchanged; only aggregate imports and AxiomCheck changed among earlier Lean files.
- Python: **36 tests passed**, 101.765 seconds. Ledger validation: 11 frozen bundles, structural only. Local diagnostic: 24 selected phase inputs / 194 image returns, 12 rank-raise inputs / 44 replies, 2 rescue inputs / 10 first replies / 2 hanging branches / 10 repair replies, four failed-policy controls. No global value claim follows.
- Official Lean 4.35.0 release commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, core only, no host shim. Same-agent audits; no external independent review. Hosted CI **not observed**. A transient polling transport disconnect did not stop the retained clean build. [Full evidence](evidence/S028/README.md).

## Ledger and publication

No theorem-ledger or frozen-manifest change: **11 frozen bundles**. EC-C014/015 are FORMAL_VERIFIED and await a later separate Gate Z freeze. Current status documents and the full S029 prompt are updated in this closeout commit. The proof-source commit above remains the immutable verification anchor. Commit/push/merge to main is authorised; the final response reports the observed remote SHA and publication separately from unobserved hosted CI.

## Installed next-session prompt (full text)

# NEXT SESSION — S029: Close the lower-band tempo and pursuit gap

**Owner instruction:** Execute when the owner says "run next session" or pastes/links this prompt. Follow `AGENTS.md`: fetch main, merge any unmerged session work first, finish committed, pushed and merged to main without force. Publication is authorised. Read the charter/proof protocol, S026 proofs/audits, EC-T0010/0011 manifests, S028 proofs/audits, `research/S028_STRATEGY_ATTEMPT.md`, S028 closeout and new evidence before working.

## Exact starting point

Eleven frozen theorem bundles, KRK L1 settled. EC-C011 general clock-free forcing remains PROPOSED. S028 at proof-source `cb5d3bb713257d7cac8e3c1f9d82d8e77b746d6c` proved and formally verified (not frozen):

- EC-C014: `krk_opposition_phase_image` retains the full alternating check/reply/king-up/reply quantifiers and proves `PhaseImage`: rook one rank above strong king, lone king one or two above rook, lone/strong file offset≤2, rook/strong file separation≥4, distant rook. The frozen source's conclusion was not silently strengthened.
- EC-C015: `krk_phase_image_upper_advance` covers the entire upper band. Chosen rook-up raises the barrier rank; every reply either leaves a distant barrier or is followed by a chosen same-rank far-file rook rescue and every reply. At most four plies; nonempty replies explicit; 7−rookRank decreases. The repair happens on the strong turn before another weak move.
- New source: `Rules/KRKForcing/{PhaseImage,RankAdvance,RookRescue,RankAdvanceRescue,ReentryExamples}.lean`. Import these unchanged to preserve their verified anchor, even though Gate Z is still pending. Frozen modules/manifests are immutable. No theorem-ledger change in this mathematics session.

The upper-band policy does **not** preserve PhaseImage: the king can be two ranks below the new wall, and file offsets can grow during repair. Repetition of the local contraction is therefore not yet justified. Neither liveness nor a contracting local phase is a full ForceMate proof.

## Principal obligation: a terminating lower-band policy and a usable post-phase invariant

The unsolved image inputs have W.rank=R.rank+1, S.rank=R.rank−1 and non-aligned files (offset one or two). Aligned lower-band **image** inputs already meet EC-T0011's four-file entry. Do not fill this session with new forcing definitions or just repeat image bounds.

1. First inspect whether a new **two-file** checking lemma plus rook rescue closes the alignment case of a broader invariant. In a new module, prove the chosen rook check is legal, every arbitrary reply rises one rank, the top edge is actual mate, and any hanging-rook strong-turn result can be repaired using the S028 far-file rescue. EC-T0011's fixed four-ply phase still needs four files; never edit it or pretend it already covers this weaker margin.
2. Investigate an oriented pursuit policy: with file offset one, use a distinct legal same-rank rook waiting move; with offset at least two, advance the strong king one file toward the lone king on its current rank. Staying in the lower band forces horizontal weak steps. Avoid crossing or following the lone king into the explicit chase cycle. An upward reply should enter an already proved upper-band contraction **with its actual margin verified**.
3. Prove the safety/tempo normalization, rather than assuming a waiting move exists. An extreme far rook target can equal the current rook square; provide a distinct target when a real tempo is required. A second-far file offers margin three in some cases, but current margin two can leave a hanging rook after the next reply. Every normalization grants another weak move; prove it cannot reset the pursuit indefinitely or silently reverse the chosen direction. The d/e far-file switch and board edges are substantive cases. The S028 strategy note proposes a bounded two-rook-turn normalization lemma: if an offset-two normalization reply moves toward the strong king, offset becomes one, and the next non-aligned same-band waiting reply returns the lone file to its original value. Prove that the chosen distinct far/second-far target then leaves margin≥3 (rightward cases x≤3, x=4, x≥5; leftward mirror cases), so a king step is finally available. This is a proof plan, not an already verified policy.
4. Supply a well-founded lexicographic measure, e.g. remaining distance to the approached file edge plus a *proved bounded* tempo-normalization phase. Prove finite completion inside every phase and strict decrease across completed phases. A finite board, a wall, or a cooperative route alone does not establish termination against every defence.
5. Close the post-contraction invariant. A candidate broader family has the strong king below a separating rook rank, the lone king above it, a distant rook on strong turns and actual legal ancestry excluding illegal incoming check. After rank advance the strong king may need to approach the wall. Advancing the king when at least two ranks below the wall, with optional rook rescue, is a possible bounded normalization; its nonempty-reply and termination obligations remain to be proved. Do not assume PhaseImage is restored. File/rook safety and nonempty replies must hold at every weak node, including corners and waiting moves.

If these components close, combine them through EC-T0008 finite-rank forcing semantics to a genuine all-defences mate result from the justified image family or broader wall family. Then attack arbitrary strong-turn legal KRK arrival setup. Keep EC-C011 PROPOSED until every case is closed; a conditional wall-family theorem is not arbitrary-arrival setup, full KRK WDL, clocks/repetition or distance-to-mate.

## Required adversarial controls

Retain S028's kernel witnesses:
- Kb2/Rh3/Kc4 → Kc2 Kb4 Kb2 Kc4: exact legal chase cycle without opposed strong-turn files.
- Kf6/Ra7/Kh8 → Rg7: protected-rook stalemate.
- Ka2/Re3/Kc4 → Re4+ Kc3: lower-band rank advance loses the wall.
- Ka2/Re3/Kc5 → Re4 Kd5: rook hanging; Rh4 is a legal repair, not permission to give Black another turn first.

Use locally generated fixed cases or small declared diagnostic sets for new failures; no class-wide enumeration, retrograde values, per-position certificates, tablebases or engine oracles. Do not assume a general kernel reflection/rotation theorem. Both colours and arbitrary flags must be explicit parameters or a proved reduction.

## Deliverables and honest stopping condition

Write a standalone exact mathematical proof and same-agent adversarial audit before Lean; new candidates EC-C016 onward only for well-posed new results. Put new source in new modules, add aggregate imports and main axiom checks. Reuse incremental .lake outputs for changed modules/importers. Successful Gate F promotion needs a published exact proof-source SHA and a new fresh GitHub checkout with no .lake, retained successful build, exact statements, forbidden scan and allowed axiom subsets (propext, Classical.choice, Quot.sound). Run relevant Python tests and ledger validation. Do not label unrun checks or hosted CI as passed.

Sustain the strategy attempt. If incomplete, retain useful new proved lemmas, precise failed policies/counterexamples and the exact unresolved all-defences/termination obligation; do not weaken quantifiers or report EC-C011 completed. Write `sessions/S029_KRK_LOWER_BAND.md`, session-ledger row and current status updates, then install a full actionable S030 prompt around the actual remaining gap and include it in the closeout. Preserve all frozen ledger rows/manifests; S028 prerequisites need a later separate Gate Z freeze. Commit, push session branch, merge main and push main, verifying the remote SHA.

## Cloud commands

Use the existing isolated checkout, no worktree unless requested. In Lean shells: `export ELAN_HOME=/workspace/.tools/elan; export PATH="$ELAN_HOME/bin:$PATH"`. Run Lake from `formal/`; Python tests and `scripts/validate_ledger.py` from the root. S028 used unmodified official Lean 4.35.0 without a path-discovery shim; use the documented workaround only if its actual host failure occurs.
