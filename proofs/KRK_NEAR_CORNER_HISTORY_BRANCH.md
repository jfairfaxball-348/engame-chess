# Near-corner rook interval or fixed king entry

Status: locally Lean-checked, unfrozen. This is a complete RAW outcome
criterion for the specified branch, not full KRK closure.

Assume an ongoing admitted RAW history with strong turn, halfmove clock
h>=96, exact KRK, W=(1,0), S=(2,2), and R.y>=3. Either strong colour is
allowed. Keep the actual incoming trace H and all position flags.

The strong side wins iff either of these tests passes:

1. A clear rook interval on file zero, as in `ClearRay H S R W 0`.
   Its destination is (0,y), y>=2, with y different from the source rank
   for a vertical move, or equal to it for a horizontal crossing. The
   forced weak reply is (1,0)->(2,0). Both resulting position keys must
   occur fewer than twice in H, and h<98.
2. R.x=2 and a fixed king entry passes. Play S=(2,2)->(1,2), then the
   forced weak reply (1,0)->(0,0). Both resulting position keys must occur
   fewer than twice in the same original H, and h<98.

The two tests query `play` on the actual incoming position, retaining
castling flags and the rule model's repetition-key normalization. Neither
uses a freshly constructed history or assumes that history reflects with
the geometric board. The two branches generally query different keys.

For necessity, the complete near-corner three-ply formula excludes immediate
mate and reduces every king entry to (1,2), requiring R.x=2. The full
last-reply formula reduces every rook entry to file zero at rank at least
two. The checked unique-reply theorem identifies each subsequent weak
square. `EntryClear` then evaluates current and intended claims using only
the original two-key tests. The existing complete three-ply history theorem
also excludes castling alternatives.

For sufficiency, the proof constructs the canonical actual legal king or
rook move and its actual legal weak reply, then applies the same checked
history theorem. The complement gives a weak holding policy against every
strong alternative. Whenever winning, the exact rule-game mate distance is
three plies; winning within two is impossible in this domain.

The source is `KRKNearKingBarrier.lean`: `king_history_iff`,
`rook_history_iff`, `high_clock_force_iff`, `high_clock_actual_iff`,
`high_clock_hold_iff`, and `high_clock_exact_three`. The supporting
`king_entry_legal` constructs the actual canonical king move, and
`canonical_king_material` identifies its resulting material.

This evaluates the extra strong branch reached from weak opposition at
W=(2,0). Transporting both barrier alternatives back to that weak root's
original trace and combining all weak replies is still required. The other
near-corner/corner families, lower clocks, full FIDE correspondence and
global WDL/DTZ semantics remain open.
