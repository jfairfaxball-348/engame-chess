# Session ledger

| Session | Date | Target | Result | Freeze/ledger effect |
|---|---|---|---|---|
| S000 | 2026-10-16 | Bootstrap research repository | Charter, model draft, K-vs-K candidate, protocol, empty immutable ledger, session prompt, hygiene tooling | None — 0 frozen theorems |
| S001 | 2026-10-16 | EC-C001 K-vs-K local proof (Gate L) | Foundations repaired; proof L0–L6 + audit; diagnostic script; EC-C001 → LOCAL_VERIFIED; S002 (Lean) installed. [Closeout](S001_KK_PROOF.md) | None — 0 frozen theorems |
| S002 | 2026-10-16 | EC-C001 Lean 4 formalisation (Gate F) | Pinned core-only Lean 4.34.1 project; L0–L6, R1 and non-vacuity proved; axioms standard only; clean-clone build OK; fidelity audit; EC-C001 → FORMAL_VERIFIED (proof commit `342be5aefe16`); S003 (freeze) installed. [Closeout](S002_KK_LEAN.md) | None — 0 frozen theorems |
| S003 | 2026-10-16 | Freeze EC-C001 (Gate Z) | Fresh-clone re-verification of `342be5a`; manifest `theorems/frozen/EC-T0001/v1.md`; incremental Lean CI + re-checking-obligation rules; S004 (K+B vs K, Gate L) installed. [Closeout](S003_FREEZE_EC-T0001.md) | **+1 → EC-T0001 FROZEN** (1 frozen theorem) |
| S004 | 2026-10-16 | EC-C002 K+B vs K local proof (Gate L) | Proof B0–B5 (colour-complex escape lemma; capture branch → EC-T0001); hostile audit; exhaustive diagnostic + mutation test; EC-C002 → LOCAL_VERIFIED; S005 (Lean) installed. [Closeout](S004_KBK_PROOF.md) | None — 1 frozen theorem |

Full session closeouts live as `sessions/S###_*.md`. New research sessions are installed in the root `NEXT_SESSION.md`. Each closeout must state explicitly which mathematical and formal checks were *actually* run.
