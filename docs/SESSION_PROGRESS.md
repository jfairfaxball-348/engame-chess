# Session progress table

Owner reporting rule installed 2026-10-19. Update this table after every session, then copy it into both the session closeout and the final reply. Keep the columns and baseline row order stable so successive reports are easy to compare. Always keep full Syzygy parity last, even when adding detail above it.

Current mathematical evidence: S092 closed at owner request; continuing run stopped. Certified coverage through S091. Forty-eight theorem bundles are frozen, including EC-T0048: whole-wall93, arrivals97/98 and the explicit BOTH-turn RAW clock0 winning criterion. Bundles are not solved material classes.

| Endgames / target | Progress | Remaining |
|---|---|---|
| K vs K | Draw proved and frozen | — |
| K+B vs K | Draw proved and frozen | — |
| K+N vs K | Draw proved and frozen | — |
| K+R vs K | Earlier dead/live, forcing and partial RAW results frozen; wall93, arrivals97/98 and BOTH-turn clock0 RAW winning criterion frozen | Immediate: evaluate the positive-clock/history geometric criterion (barrier reduction paper only); full FIDE correspondence and exact WDL/DTZ |
| K+Q vs K | Open in this project | General proof and formal verification |
| K+P vs K | Open in this project | General proof and formal verification |
| All four-piece endgames | Open in this project | Every material class and legal position |
| All five-piece endgames | Open in this project | Every material class and legal position |
| All six-piece endgames | Open in this project | Every material class and legal position |
| All seven-piece endgames | Open in this project | Every material class and legal position |
| **Full Syzygy parity (through seven pieces)** | **Open** | **Complete class coverage, 50-move WDL and DTZ parity** |

Session change (S092): the necessary exact deadline passes local Lean checks; the all-history reduction to a fixed incoming-key barrier problem is argued on paper. The compact geometric evaluation and matching lower bounds are still missing. No new outcome coverage, own-source F/Z or freeze;48 bundles unchanged; KRK NOT CLOSED.

S090 owner-directed rules update: the direct-obligation/necessary-prerequisite
rule now applies to every research target. This is governance work and changes
no mathematical claim. KRK research is now stopped under the latest owner closeout instruction.

### Movement of the current target's direct obligations

| Closure obligation | Current coverage | Actual movement during S092 |
|---|---|---|
| Global clock-safe geometry | Wall93/arrivals97-98 frozen as EC-T0048 | Unchanged during S092; certified through S091 |
| Complete rule-aware outcomes | High-clock tests frozen; explicit BOTH-turn clock0 winning criterion frozen | Exact deadline locally checked and fixed-barrier reduction on paper; compact positive-clock/history criterion still OPEN |
| Full FIDE correspondence | Partial kernel/history/key/claim interfaces | Full correspondence still OPEN; headline gap unchanged |
| Exact global distances/WDL-DTZ | Partial one-ply optimality and nonoptimal upper bounds | Global optimality/convention coverage still OPEN; headline gap unchanged |

Each future session must update this obligation-level account from actual
evidence. A supporting result is reported under its relevant obligation without implying
that the global certificate or any later obligation has closed.

Piece counts include both kings. The four- through seven-piece rows include all material classes at each size, including mixed material and promotions; they are not claims of completed work. Add individual class rows above their aggregate as work begins, retaining the aggregate rows and the final parity row.

“Formally verified” means Gate F passed; it does not mean frozen. A proved forcing family does not establish the outcome of every position in that class. Full Syzygy parity means proof-based coverage without consulting tablebases, with the relevant 50-move outcome (WDL) and distance-to-zeroing (DTZ) semantics. The base kernel omits clocks/repetition history; additive raw traces and a counter are frozen, while complete history adjudication and distance results remain open. Do not infer percentages from the number of frozen theorem bundles.

Sources: [roadmap](ROADMAP.md), [candidate register](../research/CANDIDATES.md), [frozen ledger](../theorems/LEDGER.csv), and [S031 Gate Z evidence](../theorems/frozen/VERIFICATION-S031/README.md). This table summarises those records; it does not replace them.
