# Six-point eleven-ply inward-corner criterion

Certification update (2026-10-29): checked results are included in EC-T0049; see the [bundle scope and proof correspondence](KRK_BOUNDED_FRONTIER_CERTIFICATION.md). Any local-build counts or unfrozen/uncommitted statements below describe the pre-certification research checkpoint, not current publication status. Mathematical open obligations remain open.

At weak king (1,1), `KRKElevenInner.kernel_eleven_iff` gives a complete strong-turn board criterion. A king step must enter one of (3,0), (3,1), (3,2), or their transposes, with its evaluated ten-ply rook region. A king already at one of those coordinates may use the explicitly evaluated rook-line conditions.

At (3,1), every admitted nonchecking distinct rook source has a suitable rook destination: use rank three, with a horizontal alternative when the king blocks the source file. At (3,2), the rook condition is rank at least three, file two with rank at most one, file at least four, or square (0,2). The protected diagonal source (2,2) is handled by a king entry rather than an invalid null rook move. At (3,0), the previous rank-two/file-at-least-three condition remains.

The nonchecking and distinct-material hypotheses are retained. In particular, a horizontal-family king on file three cannot conceal a file-one rook check against weak king (1,1); `not_file_one` is used in the rook-line proof. `rook_destination` supplies actual rays, and `rook_line_necessary` covers every possible ray into the ten-ply region. The six-point king catalogue is equivalent to the proved global forty-eight-point geometry.

`kernel_exact_eleven` subtracts the entire nine-ply inward criterion; strong-turn parity excludes ten. `framed_clear_iff` transports the result to all inward corners. These are board results; original-history barriers remain in the history certificates. Full KRK is open, with no freeze or commit.
