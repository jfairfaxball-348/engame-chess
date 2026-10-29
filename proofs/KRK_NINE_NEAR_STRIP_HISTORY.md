# Original-history outcomes on the nine-ply near-strip region

Certification update (2026-10-29): checked results are included in EC-T0049; see the [bundle scope and proof correspondence](KRK_BOUNDED_FRONTIER_CERTIFICATION.md). Any local-build counts or unfrozen/uncommitted statements below describe the pre-certification research checkpoint, not current publication status. Mathematical open obligations remain open.

For every admitted ongoing RAW strong-turn KRK history ending with
W=(1,2), both colours and actual native flags, at halfmove clock h>=90,
`KRKNineNearStripHistory.high_clock_actual_iff` characterises actual
strong-side winning by `Clear`. Its complement has holding strategies
for both players (`high_clock_draw_iff`).

The formula has one fixed king destination (3,1), or a rook destination
(x,3), 3<=x<=7. These are exactly the entries admitted by the
[complete nine-ply geometry](KRK_NINE_NEAR_STRIP.md). At each entry,
`After` checks the already evaluated eight-ply clock/key-prefix formula
on the original trace with that specified move appended. The quantifier
in `After` ranges only over proofs that this one move is legal; it is
proof irrelevant and does not search over legal moves. Expanding
`KRKEightPlyHistory.Clear` and its prefix definitions leaves explicit
clock inequalities, native repetition-key equalities, original occurrence
counts and fixed geometric point/ray tests. No future winning predicate
or minimax recurrence is introduced.

For necessity, any actual win supplies a quiet first move. At h>=90,
the child clock is at least 91; the exact deadline gives at most nine
plies there, and weak-turn parity reduces that to eight. The complete
near-strip geometry and castling exclusion force the listed king or
rook entry. The eight-ply history theorem supplies all remaining original
occurrence tests, including weak current and intended claims.

For sufficiency, the specified geometric move is legal. Its eight-ply
region gives forcing and a legal weak reply; its clock and repetition
tests ensure the appended history is ongoing. The existing eight-ply
certificate supplies the rule-aware continuation. The strong side may
decline its own optional claims as required by the RAW winning semantics.

`exact_nine` proves exact rule-aware distance nine for any `Clear` history
with a nonchecking strong root: the constructed nine-ply certificate is
matched by the clock-free exclusion of eight plies. This result currently
uses the canonical weak square (1,2); other orientations require a native
history-preserving transport of the formula. Global nine-ply/history
coverage, lower clocks, FIDE correspondence and class-wide distances
remain open. All new results are unfrozen.
