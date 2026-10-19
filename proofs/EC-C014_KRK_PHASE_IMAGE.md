# EC-C014 — Exact image bounds of the checking phase

S028, standalone Gate L argument, 2026-10-19. Classical finite-board king geometry; no novelty claim. General FIDE 2023 kernel, either colour, arbitrary flags; no clock/repetition result.

Let S,R,W satisfy the EC-T0011 entry hypotheses: exact KRK, strong turn, S and W on the same file, W two ranks above S, rook at least four files from W and off W's rank. Use its chosen checking square C=(R.file,W.rank). If the check does not mate, every first legal reply has lone king T with T.rank=W.rank+1 and file distance from W at most one. The chosen strong king move has S′.file=S.file and S′.rank=S.rank+1. Every second legal reply gives a non-capturing unit king step T→V by EC-T0010, since the rook is at least three files from T.

Define `PhaseImage S′ C V` to mean:

1. C.rank=S′.rank+1;
2. V.rank=C.rank+1 or C.rank+2;
3. |V.file−S′.file|≤2;
4. |C.file−S′.file|≥4;
5. d∞(C,V)≥2.

The first and fourth equalities/bounds follow from the fixed chosen squares and original opposition. A unit second king step gives |V.rank−T.rank|≤1; the barrier theorem rules out V.rank≤C.rank. Since T.rank=C.rank+1, the only remaining ranks are C.rank+1 and C.rank+2. The triangle inequality for the two unit file displacements gives the file-offset bound. The rook remains at distance at least two by the four-file initial margin minus two possible file displacements, also the frozen distant-barrier conclusion. All coordinates are Fin 8; no off-board successor is constructed.

The new kernel-level theorem must retain the alternating quantifiers: a chosen legal check; either actual MateGoal or a nonempty first reply set; every legal first reply; chosen legal king-up; nonempty second reply set; every legal second reply, with exact Matches and PhaseImage. It also retains the frozen strict decrease in 7−V.rank. A separate strengthened follow-up theorem obtains these bounds from the frozen follow-up and extracts the actual arbitrary second reply through safe-reply completeness. No reachability hypothesis is invented: actual Legal ancestry and Matches are retained in the theorem itself.

This proves the *image* of the fixed choices, not a general winning policy from all positions satisfying PhaseImage. The frozen result is imported unchanged. In particular PhaseImage does not imply opposed files or a closed repeated-phase invariant.
