# KRK — status and remaining work toward Syzygy parity

**Status: OPEN.** This is the single KRK status document. The target is
[Syzygy parity](CHARTER.md#parity-target-hard-boundary-owner-2026-10-29) and
nothing beyond it: fresh positions (clock 0, no history, no castling rights),
either side to move, exact WDL50 and DTZ50.

In KRK the strong side has no zeroing move, and a weak rook capture reaches a
dead KK position (a draw). So a won position's DTZ50 is its exact distance to mate
in plies. These distances are well under 100, so no won position is cursed and
the 50-move rule does not change WDL.

## Done (frozen, see [ledger](../theorems/LEDGER.csv))
- **Dead/live** for every KRK position (EC-T0007).
- **WDL.** The strong side wins exactly when it is on move, or the weak king is mated,
  or the rook is safe and the weak side has a legal move. Otherwise the position is drawn
  (rook capture / stalemate). This is proved at clock 0 for every admitted
  history: `KRKCentral.fresh_outcome` (EC-T0048). That already covers
  Syzygy's WDL information for KRK, subject to the bridge item below.
- **Upper bounds**: uniform wall93, strong arrivals97, weak forcing98 (EC-T0048).
- **Exact distances, board level**: `KRKTwelveGlobal.kernel_twelve_iff` and
  predecessors give a complete geometric region for weak-to-move mate within
  2/4/…/12 plies. Thirteen plies is the one-move entry into that region. The
  14-ply geometry is complete on deep and central-first-strip weak squares only
  (EC-T0049).
- **Beyond parity (kept, no further work needed)**: RAW history-aware outcome
  bands at strong h>=86 / weak h>=85, incoming-repetition barriers, claim
  handling, castling exclusions, fixed-barrier paper reduction. See
  [the archived frontier note](../research/KRK_POSITIVE_CLOCK_FRONTIER.md).

## Remaining for parity
1. **Exact distance to mate for every won KRK position.** Do this at board level
   (`MateWithin`), with matching lower bounds against all defences and upper
   bounds by explicit strategy. That means extending the exact regions from 14 plies to the
   maximum KRK depth, and proving that no won position lies beyond it. Open pieces at
   the current frontier: the inward 13-ply compact form (`KRKThirteenInnerRook`
   has necessity, plus sufficiency only at the high profile), then the 14-ply near
   strip, inward corners and edge.
2. **Losing-side DTZ.** For weak-to-move lost positions, DTZ is the same
   distance (the defender maximises). Make sure the exact-distance theorems are
   stated so that this follows directly.
3. **Fresh-position bridge.** One theorem connecting the board-level distance
   to a fresh game (clock 0, empty history, no castling rights). It must show that the
   repetition and 50-move rules do not change the optimal distance; the
   key-simple strategy (EC-T0038) is the likely tool.
4. **Parity interface and freeze.** One public statement giving WDL and DTZ for
   every legal KRK position in both orientations, then certify and freeze per
   [PROOF_PROTOCOL](PROOF_PROTOCOL.md). KRK is then closed.

## Method notes
- Ply-by-ply region layering works but scales badly. Prefer arguments that
  cover many depths at once: an explicit distance formula or potential
  `D(sk, rs, wk)`, proved exact by showing that the best move lowers it by one and no
  defence lowers it by more. Also prefer reusable box/wall lemmas, since KQK should reuse
  them.
- A position-by-position computed table (including one evaluated in Lean) is not an
  acceptable proof. Diagnostics may suggest regions, never certify them.
- Do not extend the RAW history / clock-band modules further; they are outside
  parity.
