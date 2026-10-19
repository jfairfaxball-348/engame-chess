# S036 — Lean fidelity review for EC-C024

Same-agent review, not independent external review. Standalone paper and
adversarial audit saved BEFORE any new Lean source. Official core Lean 4.35.0,
no new dependencies. Gate F pending until published exact-source verification.

| Paper obligation | New RawClock module / declaration | Fidelity |
|---|---|---|
| Source pawn, capture event, Boolean detector and raw fold | Definitions | Imports all five S035 files unchanged. Source pawn uses moving turn, before promotion; capture event is enemy destination OR explicit ep event. Counter reads stored source and Move; root zero. |
| Pawn / occupied / quiet cases | EventCases / event_cases | Universal board/move facts, no fabricated full prefix. Legal domain required to interpret destination occupancy as capture. Source pawn covers promotion, singles/doubles and empty-dst ep. |
| Legal reset-event equivalence | LegalEvent / legal_zero_iff | Legality supplies targetOK; any occupied dst is enemy nonking. Ep is already a pawn move. No material-count lemma assumed; existing human FIDE-to-kernel bridge remains trusted. |
| Castle destination empty | CastleEmpty / castle_empty | Actual canCastle kingside and queenside branches force empty landing square. With source king, event_cases gives no reset. Quiet rights/ep changes do not enter detector. |
| Exact append update | Append / append_clock | For every state/move/legality proof; definition equality, no terminal filter or history truncation. |
| Global clock bound | LengthBound / clock_le_length | Structural Trace induction; zero branch nonnegative and increment branch IH+1; counts moves rather than positions. |
| One-step upper bound | StepBound / append_clock_le | Reset/increment split on exact append law; no uniform future mate bound. |

Six main declarations in six theorem modules plus shared definitions; all exact
statements and axiom reports added to AxiomCheck. Standard-three subset only.
Initial compile failed in EventCases/LegalEvent because simplification left
hypotheses in a different form and one Boolean lemma was addressed incorrectly;
fixed by explicit hypothesis changes and standard simp extraction. The complete
failed log is retained; final incremental build succeeds (66 jobs), runner exits
zero. A preliminary authoring command ran from formal/ with root-relative paths
and wrote no new sources; corrected working directory. No mathematical target
or kernel definition was weakened to fix compilation.

No fixed sample-game/ep/promotion/castling prefix is executed or asserted. The
controls are universal symbolic proofs and paper arguments. Frozen append_spec
retains move/position prefix on reset; no prior modules, manifests, ledger rows
or evidence change. Full no-earlier-terminal rules, repetition and claims,
automatic outcomes/mate priority, Layer instantiation and clock/repetition
lifting remain open. No numerical KRK bound or DTM/DTZ/WDL/Syzygy result.

## Completed Gate F

Published exact source `2d2b40ddaaff2a962bb9f573e8de799b1427d5f8`; new fresh GitHub clone,
no .lake before build. 66 jobs, exit 0, 365.225s; runner exit 0 at 2026-10-19T14:23:42Z.
271 allowed reports (239 standard-three, 18 propext/Quot.sound, 9 propext,
5 axiom-free); event_cases propext, other five mains standard-three.
Full working/clean outputs identical, every Lean source matched, seven-module
forbidden scan zero; 359 protected files and 20 ledger rows unchanged.
EC-C024 FORMAL_VERIFIED, not frozen. Evidence: sessions/evidence/S036/.
Hosted CI unobserved. No extra FIDE/outcome/distance claim.
