# Session progress table

Owner reporting rule installed 2026-10-19. Update this table after every session, then copy it into both the session closeout and the final reply. Keep the columns and baseline row order stable so successive reports are easy to compare. Always keep full Syzygy parity last, even when adding detail above it.

Current mathematical evidence: through S082. Forty-four theorem bundles are frozen, including universal admitted RAW KRK termination. Bundles are not solved material classes.

| Endgames / target | Progress | Remaining |
|---|---|---|
| K vs K | Draw proved and frozen | — |
| K+B vs K | Draw proved and frozen | — |
| K+N vs K | Draw proved and frozen | — |
| K+R vs K | Dead/live, clock-free forcing, conditional 73-ply RAW family and 442/443 bounds and universal RAW termination frozen; all-history RAW holding frozen; strong nonloss/high-clock criteria frozen; actual winning-policy bridge formally verified | Full FIDE, low-clock geometric coverage and global exact distance |
| K+Q vs K | Open in this project | General proof and formal verification |
| K+P vs K | Open in this project | General proof and formal verification |
| All four-piece endgames | Open in this project | Every material class and legal position |
| All five-piece endgames | Open in this project | Every material class and legal position |
| All six-piece endgames | Open in this project | Every material class and legal position |
| All seven-piece endgames | Open in this project | Every material class and legal position |
| **Full Syzygy parity (through seven pieces)** | **Open** | **Complete class coverage, 50-move WDL and DTZ parity** |

Session change: S082 formally verified independent actual bounded winning policies iff full RAW forcing on every admitted KRK history, exact same-B certificate extraction and actual terminal mate continuations.44 bundles frozen; geometric low-clock coverage, full FIDE and global exact WDL/DTZ remain open.

Piece counts include both kings. The four- through seven-piece rows include all material classes at each size, including mixed material and promotions; they are not claims of completed work. Add individual class rows above their aggregate as work begins, retaining the aggregate rows and the final parity row.

“Formally verified” means Gate F passed; it does not mean frozen. A proved forcing family does not establish the outcome of every position in that class. Full Syzygy parity means proof-based coverage without consulting tablebases, with the relevant 50-move outcome (WDL) and distance-to-zeroing (DTZ) semantics. The base kernel omits clocks/repetition history; additive raw traces and a counter are frozen, while complete history adjudication and distance results remain open. Do not infer percentages from the number of frozen theorem bundles.

Sources: [roadmap](ROADMAP.md), [candidate register](../research/CANDIDATES.md), [frozen ledger](../theorems/LEDGER.csv), and [S031 Gate Z evidence](../theorems/frozen/VERIFICATION-S031/README.md). This table summarises those records; it does not replace them.
