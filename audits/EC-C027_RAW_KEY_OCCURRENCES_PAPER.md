# S042 — Adversarial paper review of EC-C027

Saved BEFORE Lean. Same-agent review, not independent external review.
Paper: proofs/EC-C027_RAW_KEY_OCCURRENCES.md. No local gap found.

| Attempted falsification | Resolution |
|---|---|
| Empty move-list implies count zero | Positions contains [initial]; root counts iff its key matches. |
| Current endpoint omitted or double-counted | Frozen positions contains it once; append adds exactly the new endpoint. |
| Absent or newly queried key mishandled | Filtering uses actual propositional equality with explicit decidable equality. |
| Nonconsecutive repeats ignored | Filter processes every stored entry, no adjacent-only test. |
| New current count equals old current count+1 | False generally; query NEW key in old history, as symbolic [A,B,A]→B shows. |
| Different key maps compared | One fixed map is universally quantified and used on both sides. |
| Same erased board forces equal counts | Histories remain full data; erased board alone does not identify endpoint lists. |
| Zeroing discards earlier repetition evidence | Frozen append_spec retains full prior positions, independent of clock resets. |
| Earlier raw draw forbids all appends | Raw relation has no terminal filter; no FIDE continuation theorem claimed. |
| Constant key map supposedly gives FIDE repetitions | It validly counts every endpoint, demonstrating generic rather than FIDE semantics. |
| Arbitrary Boolean equality accepted | Decide uses explicit DecidableEq, hence correct propositional equality. |
| Exact count law supplies low repetition | Rejected: no threshold bound or certificate is supplied. |

Proof is frozen position-list retention, filter-over-append and singleton
length. Generic list arguments only, no engine/tablebase/enumeration or fabricated
full compatible game. Verdict: LOCAL_VERIFIED for exact generic bookkeeping;
Gate F pending; full FIDE key/claims/adjudication remain open.
