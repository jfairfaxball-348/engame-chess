# S040 — Adversarial paper review for EC-C026

Saved BEFORE Lean. Same-agent review, not independent external review.
Paper: proofs/EC-C026_RAW_CLOCK_BUDGET_CERTIFICATE.md. No local gap found.

| Attempted falsification | Resolution |
|---|---|
| n=0 grants a free announced move | k<n is false; only root clock is bounded. |
| k=0 omits a first defender move | For n>0 EVERY RawBoardStep successor is universally covered. |
| k=n includes an extra quiet move from 99 | Prospective clause requires k<n; no terminal-depth guarantee. |
| Sum 100 accepted as safe | Strict budget premise excludes it; sum 99 satisfies it. |
| Clock 99 and n=1 supposedly refutes theorem | Premise fails; no certificate is claimed for that input. |
| Reset needs an extra premise or loses prior trace | Frozen growth handles reset; actual append retains full history. |
| Equal boards substitute different histories | Full-state Extends and RawBoardStep prohibit this substitution. |
| Earlier raw draw invalidates proof | No terminal guard; raw bounds do not certify FIDE continuation. |
| Only selected strategy children covered | Prospective v and actual edge are arbitrary, including adverse children. |
| Announced move must be executed first | The theorem bounds its hypothetical append; no claim action is modeled. |
| Arithmetic safety solves all claim conditions | Rejected: repetition and actual claim semantics remain separate. |
| Budget hypothesis is a uniform KRK mate bound | Rejected: no n or strategy is provided; no numerical bound established. |

Proof uses frozen growth at k and actual snoc at k+1, plus k+1≤n and addition
monotonicity/transitivity. No endpoint-clock premise or erased-history shortcut.
Controls symbolic only, no fabricated compatible full game. Verdict:
LOCAL_VERIFIED for the exact conditional statement; Gate F remains pending.
