# S029 — Bounded lower-band pursuit and closed rank-wall forced mate

Date: 2026-10-19. Base main: `b90a521f9e61a3f86c5d4d2adc20f71e66d35df0`. Initial all-branch fetch found a clean main and no earlier unmerged remote work. Session branch: `session/s029-lower-band`. **Proof-source:** `3ead1d587f4ff5e129f73666bd466f5eac764223`, pushed before exact-source Gate F. This later closeout/status commit changes no Lean proof source.

## Proven and formally verified

**EC-C016:** two-file opposed checking, every legal reply one rank upward or actual top-edge mate. The frozen four-file/four-ply result is unchanged. No stronger follow-up is inferred from the weaker margin.

**EC-C017:** finite lower-band pursuit. Offset one uses an actual distinct far/second-far rook tempo. Offset≥2 with margin≥3 advances the strong king's file. Margin-two normalization has a bounded offset-two→one→two return branch; both directions and the d/e switch are symbolic. The only recursive pursuit call follows a king-file advance and strictly decreases remaining file distance. The separate theorem's `LowerExitWins` interface is explicit and discharged in the final wall proof.

**EC-C018:** `krk_rank_wall_force` proves **ForceMate σ q** from only exact strong-turn KRK Matches and **S.rank<R.rank<W.rank**. No initial rook-safety, file offset, prior-arrival or assumed winning-continuation hypothesis remains. Outer 7−rookRank and inner rook/strong rank-gap induction close continuation after wall advance; ready states are proved before same-measure far-rook normalization. All required defending reply sets are nonempty or actual mate; every legal reply is covered. Both colours and arbitrary flags. This includes **every S028 PhaseImage** (`krk_phase_image_force`) and closes S028's lower-band/continuation gap for that family.

A further proved setup subfamily, `krk_vertical_wall_entry_force`, handles W.rank≥S.rank+2, rook file different from S and rook/lone file margin≥2. It constructs a safe vertical wall entry and reduces every reply to the main theorem. [Paper proof](../proofs/EC-C016_C018_KRK_WALL_FORCING.md), [paper audit](../audits/EC-C016_C018_PAPER.md), [fidelity audit](../audits/EC-C016_C018_LEAN.md).

## Sustained arbitrary-setup attempt and remaining limit

A geometric wall on a weak turn does not suffice: Ka1/Rd4/Kc3 allows both Rd2 Kxd2 and Rb4 Kxb4, ending in KK. Fixed kernel controls prove both legal capture sequences. A threatened rook in the new main theorem is allowed only on the strong turn, before its prescribed repair. Equal-rank/downward king separation and axis changes are outside the current direct vertical-entry conditions. A full kernel forcing-transport theorem is not assumed from cooperative StepM symmetry.

Arbitrary strong-turn legal-arrival setup, required axis/direction transport and the remaining weak-turn terminal/capture classification are still open. **EC-C011 remains PROPOSED.** The new wall theorem is a genuine forcing family, not full KRK WDL or arbitrary-position setup. No clock/repetition, numerical distance bound, seven-piece parity or initial-position claim follows. [Strategy record](../research/S029_STRATEGY_ATTEMPT.md) and installed S030 prompt identify the precise next obligation.

## Observed checks

- Final working incremental build: 41 jobs, exit 0; all 23 new declarations compiled and exact signatures inspected. In particular the main wall theorem's only hypotheses are Matches and strict rank separation; no LowerExitWins assumption survives.
- New fresh GitHub clone at the published proof-source, positively no .lake: **41-job clean build, exit 0, 273.042 seconds**. Full axiom/statement runner exit 0, Gate F UTC `2026-10-19T10:06:07Z`. All **235** reports allowed: 204 [propext, Classical.choice, Quot.sound]; 18 [propext, Quot.sound]; 8 [propext]; 5 axiom-free. Clean/working report output is byte-identical and all current Lean source bytes match the anchor.
- Seven-module forbidden-token scan: zero. SHA-256 inventory retained. Every earlier theorem record, frozen module and S028 proof source unchanged; only aggregate imports/AxiomCheck changed among earlier Lean files. Frozen ledger still **11**, structural validation passed.
- Python suite: **39 tests passed**, 97.768 seconds. Independent coordinate-policy diagnostic: 64 selected actual-mate trajectories, both colours, all six action categories; maximum observed 51 plies, supplementary only. Local selectors use immediate replies, not game-value search. Concrete setup capture controls passed. No general proof comes from those computations.
- Core Lean 4.35.0, official release commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, no host shim or external project dependency. Same-agent audits, not independent external review. Hosted CI **not observed**. [Full new Gate F evidence](evidence/S029/README.md).

## Ledger and publication

No theorem-ledger/frozen-manifest changes: 11 frozen bundles. EC-C014–018 await later separate Gate Z work; S029 promotes only EC-C016–018 to FORMAL_VERIFIED after the observed exact-source check. Current status, candidates, roadmap and S030 prompt updated. Commit/push/merge to main is authorised; the final response records the observed remote publication SHA separately from unobserved CI. The proof-source SHA above avoids a self-referential closeout citation.

## Installed next-session prompt (full text)

# NEXT SESSION — S030: Safe setup from arbitrary legal KRK arrivals

**Owner instruction:** Execute when the owner says "run next session" or pastes/links this prompt. Follow `AGENTS.md`: fetch all remote branches and latest main, merge any earlier unmerged session work, finish committed, pushed and merged to main without force. Publication is authorised. Read the charter/proof protocol, EC-T0010/0011 manifests, S028/S029 proofs/audits, S029 closeout/evidence and `research/S029_STRATEGY_ATTEMPT.md` first.

## What is now proved

Eleven frozen theorem bundles remain; these are not eleven solved material classes. EC-C011 is still PROPOSED. S029 proof-source `3ead1d587f4ff5e129f73666bd466f5eac764223`, core Lean 4.35.0, proves:

- EC-C016: two-file opposed checking, every reply one rank up or actual edge mate. This is not the frozen four-file four-ply king-up theorem.
- EC-C017: bounded lower-band pursuit with explicit `LowerExitWins` interface. Offset one waits with a distinct far/second-far rook move, offset≥2 chases, and margin-two normalization has a bounded return branch. The only recursive pursuit call follows an actual king-file advance.
- EC-C018: **`krk_rank_wall_force` proves ForceMate from exact strong-turn KRK and S.rank<R.rank<W.rank**, with no initial safe-rook margin or legal-arrival hypothesis. Its nested rank/gap induction closes the continuation invariant; `LowerExitWins` is discharged rather than assumed in this flagship. Both colours and arbitrary flags. `krk_phase_image_force` therefore wins from every S028 PhaseImage.
- `krk_vertical_wall_entry_force` proves a setup subfamily: W.rank≥S.rank+2, rook file different from S.file, and rook/lone file margin≥2. It enters the wall directly, or uses the existing wall if already placed.

S028 sources and all seven S029 modules must be imported unchanged to preserve their verified anchors, even while Gate Z is pending. Frozen modules/manifests are immutable. Do not redo lower-band pursuit or weaken the new wall result to a local contraction. No theorem-ledger change in this mathematics session; EC-C014–018 need later separate Gate Z work.

## Principal mathematical obligation

Close safe setup from an **arbitrary strong-to-move legal arrival** in exact KRK, or isolate a genuinely new precise obstruction. The intended target is the strong-turn part of EC-C011:

For either colour σ and any flags, from `IsKRK q σ S R W`, `q.turn=σ` and `∃ p, Legal p q`, prove `ForceMate σ q`.

1. Extract actual king separation and any needed no-incoming-check facts from the kernel arrival, rather than assuming global reachability or a hand-picked geometry. Use the general kernel, not only `StepM`'s cooperative route.
2. Extend the winning wall to the needed axes/directions by a **proved** transport or a direct parameterized construction. Equal-rank kings require another axis; a lone king below the strong king needs reflected rank orientation. Pure `StepM` symmetry does not automatically transport an alternating ForceMate strategy. Account for every weak legal reply and arbitrary castling/en-passant flags.
3. A possible transport route is to establish a non-castling KRK/KK board relation, prove chosen ordinary king/rook moves lift to arbitrary flags and every weak reply projects back, then carry the finite-rank forcing induction through it. If using this route, prove its actual hypotheses and terminal preservation; do not silently assume an arbitrary flags-dependent winning strategy transports. Another route is a fresh generic coordinate-wall proof importing the existing geometry. Choose a supported route based on actual code, not an unsupported full-kernel symmetry claim.
4. Construct a finite all-defences safe rook retreat/setup into a winning oriented wall, or into the direct vertical-entry subfamily. A geometric placement between king coordinates is insufficient if it gives the defender a rook capture. A first rook retreat can let the lone king change which axis has a two-square gap; handle that response rather than assuming the original gap survives. Handle blocked rays, rook/king on the same rank/file, edges, threatened rook, corners and stalemate. Every chosen move must be legal, each required defending reply set nonempty or actual mate, and every reply covered.
5. Supply a terminating setup argument: an explicit bounded phase or well-founded measure with proved progress under all replies. The existing wall proof already handles the subsequent mating strategy; do not replace setup by a cooperative path, a simulation or an assumed winning continuation.

## Required controls and boundaries

Retain the S028 chase cycle and stalemate controls, which the S029 policy now avoids. New S029 control: White Ka1/Rd4, Black Kc3, White to move. Both **Rd2 Kxd2** and **Rb4 Kxb4** are kernel-legal and leave KK. A rank/file wall on a *weak* turn is not enough when the rook can be captured. Do not drop the direct-entry safety margin based solely on visual confinement.

The S029 main theorem admits a threatened rook only on a *strong* turn, before the prescribed repair. Never give the defender an extra move before that repair. Keep the named winning colour and game quantifiers exact. No clock/repetition, exact-distance, full FIDE WDL, seven-piece parity or initial-position claim follows from a clock-free strong-turn result.

If arbitrary strong-turn setup closes, next derive the correct weak-turn terminal/capture classification: zero-ply opponent mate, stalemate non-win, any legal capture to KK obstructing forcing, and nonempty all-noncapturing replies reduced to the strong-turn theorem via finite branching. Keep EC-C011 PROPOSED until every intended branch is established. Do not mark all KRK L2/FIDE WDL solved merely because the strong-turn theorem passes.

No tablebases, engine oracles, class-wide enumeration, retrograde values or per-position proof certificates may supply any general proof. Locally generated fixed controls or a small declared diagnostic set are supplementary only. S029's 64 selected trajectories and observed maximum length are not a DTM theorem.

## Deliverables and verification

Write a standalone paper proof and same-agent adversarial audit before formalisation. Register candidates EC-C019 onward only for exact new statements. Use new modules; add aggregate imports and main declarations to `AxiomCheck.lean`. Preserve all previous proof/definition sources and theorem records. Reuse incremental outputs for changed modules/importers. Gate F requires a published exact proof-source SHA and a new fresh GitHub clone at that SHA with no .lake before build; retain full successful build, exact statements, axiom reports and forbidden-token scan. Allowed axiom subsets: propext, Classical.choice, Quot.sound. Run relevant Python checks and unchanged-ledger validation. State unobserved CI explicitly.

Sustain the strategy attempt. If setup remains incomplete, preserve useful new proved transport/setup lemmas, failed policies with precise local counterexamples, and the exact all-defences/termination gap. Do not silently weaken the target, repeat existing forcing infrastructure, or report EC-C011 solved. Write `sessions/S030_KRK_SAFE_SETUP.md`, update current status and session ledger, install a full actionable S031 prompt around the actual remaining obligation and include it in the closeout. Commit, push session branch, merge main, push main and verify remote SHA.

## Cloud tool activation

Use the existing isolated checkout; no worktree unless requested. `export ELAN_HOME=/workspace/.tools/elan; export PATH="$ELAN_HOME/bin:$PATH"`. Lake commands run in `formal/`; Python checks at root. S029 used the official unmodified Lean 4.35.0 release without a path shim. Use the documented older shim only if its actual host failure occurs.
