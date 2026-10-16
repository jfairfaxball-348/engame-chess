# Session ledger

| Session | Date | Target | Result | Freeze/ledger effect |
|---|---|---|---|---|
| S000 | 2026-10-16 | Bootstrap research repository | Charter, model draft, K-vs-K candidate, protocol, empty immutable ledger, session prompt, hygiene tooling | None — 0 frozen theorems |
| S001 | 2026-10-16 | EC-C001 K-vs-K local proof (Gate L) | Foundations repaired; proof L0–L6 + audit; diagnostic script; EC-C001 → LOCAL_VERIFIED; S002 (Lean) installed. [Closeout](S001_KK_PROOF.md) | None — 0 frozen theorems |
| S002 | 2026-10-16 | EC-C001 Lean 4 formalisation (Gate F) | Pinned core-only Lean 4.34.1 project; L0–L6, R1 and non-vacuity proved; axioms standard only; clean-clone build OK; fidelity audit; EC-C001 → FORMAL_VERIFIED (proof commit `342be5aefe16`); S003 (freeze) installed. [Closeout](S002_KK_LEAN.md) | None — 0 frozen theorems |

Full session closeouts live as `sessions/S###_*.md`. New research sessions are installed in the root `NEXT_SESSION.md`. Each closeout must state explicitly which mathematical and formal checks were *actually* run.
