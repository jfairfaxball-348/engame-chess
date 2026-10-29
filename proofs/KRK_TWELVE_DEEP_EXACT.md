# Exact twelve-ply deeper-interior KRK region

Certification update (2026-10-29): checked results are included in EC-T0049; see the [bundle scope and proof correspondence](KRK_BOUNDED_FRONTIER_CERTIFICATION.md). Any local-build counts or unfrozen/uncommitted statements below describe the pre-certification research checkpoint, not current publication status. Mathematical open obligations remain open.

For separated kings, weak to move, and weak-king edge depth at least two, `KRKTwelveDeepExact.kernel_twelve_iff` gives the complete twelve-ply winning region. Only the four second interior corners (2,2), (2,5), (5,2), (5,5) survive. Reflect to weak king (2,2). The exact coordinate criterion is

- strong king (4,1), rook (x,3) with x >= 4; or
- the transpose of this configuration.

Every such win has exact distance twelve: there is no eleven-ply win, because weak-turn parity would give a ten-ply win, excluded throughout this deeper domain.

The proof first uses the eleven-ply weak-square domain. Replies on deeper squares or central first-strip squares must be covered. Five bad neighbours of (2,2) force strong king on file four with rook on rank three, or the transpose. The legal escape (2,1), after transposition, lies at weak king (1,2). `KRKElevenNearBoundary.upper_necessary` evaluates all eleven-ply entries there when the strong king has rank four and rook has file three. King entries cannot reach any ten-ply near-strip family. Rook entries force king file zero or one and a corresponding rook height. The remaining covered neighbour and rook-safety constraint eliminate file zero and force the stated x >= 4 family.

Conversely, only three weak replies are legal: (1,1), (1,2), (2,1). The first permits a king step to (3,1), entering the ten-ply inward family. The second permits a king step to (3,2), entering the ten-ply near-strip family. After the third, a transposed rook step enters the ten-ply upper near-strip family. This supplies a strategy against every legal reply and checks nonemptiness explicitly.

For the other twelve squares of edge depth at least two, the four axis-neighbour covering constraints contradict king separation and distinct material. Reflection handles all second corners and preserves native board geometry. Original incoming-history barriers can still prevent these board wins; this theorem does not erase those barriers or claim all-history class closure.

Full local Lean build: 393 jobs passed. Public axiom audit: only propext, Classical.choice and Quot.sound. Source scan found no sorry, admit, unsafe, added axioms or trace_state. No freeze or commit has occurred.
