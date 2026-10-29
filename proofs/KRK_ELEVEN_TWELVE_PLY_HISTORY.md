# Eleven/twelve-ply original-history KRK criteria

Certification update (2026-10-29): checked results are included in EC-T0049; see the [bundle scope and proof correspondence](KRK_BOUNDED_FRONTIER_CERTIFICATION.md). Any local-build counts or unfrozen/uncommitted statements below describe the pre-certification research checkpoint, not current publication status. Mathematical open obligations remain open.

For every ongoing admitted RAW KRK history, both colours, all board orientations and native flags:

- strong to move with halfmove clock h >= 88: actual win iff `KRKElevenPlyHistory.Clear`;
- weak to move with h >= 87: actual win iff `KRKTwelvePlyHistory.Clear`;
- both players can hold exactly on the complement of the corresponding criterion.

The eleven-ply criterion consists of immediate mate, or one of forty-eight fixed king points / rook-line intersections entering the full ten-ply geometric region, subject to the ten-ply original-history clock and normalized-key tests after the specified move. `KRKElevenSlots.region_rank` proves the six-rank bound used to select those points. The catalogue does not enumerate position outcomes. `KRKCastleTen` excludes all actual castling entries into a nonmating weak-ten win, preserving native legality.

The twelve-ply weak-turn criterion requires a safe rook, no current or intended claim barrier, and the explicit eleven-ply certificate at each legal guarded king reply. `After` and `AfterWeak` quantify over legality proofs of a single specified move, not over alternative future moves. Original trace prefixes are retained; no empty-history replacement occurs.

The necessary deadline leaves at most eleven plies for the weak child of a strong root at h >= 88; weak-turn board parity reduces this to ten. Conversely, explicit ordinary king/rook entries and the prior history certificate construct the winning strategy. At weak roots, every reply and every intended-claim key is checked. Existing force/holding duality proves the complementary draw statement.

`KRKElevenPlyExact.rule_eleven_iff` and `KRKTwelvePlyExact.rule_twelve_iff` hold without a high-clock assumption. Their `distance_cases` establish exact optimal winning distances in {1,3,5,7,9,11} and {2,4,6,8,10,12}. These follow by subtracting earlier certificates and using turn parity, so the lower bounds cover all alternatives. In the stated high-clock bands, every actual win has one of these exact distances.

Local full build: 389 jobs passed; public axiom audit passed with only propext, Classical.choice and Quot.sound. No frozen manifest or ledger entry is changed. This extends bounded clock-band coverage and leaves the entire lower-clock/all-history, FIDE-correspondence and global WDL/DTZ obligations open.
