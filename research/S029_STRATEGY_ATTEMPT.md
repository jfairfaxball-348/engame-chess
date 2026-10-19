# S029 — Lower-band pursuit and closed separated-wall forcing

The S028 re-entry obstruction is closed for the separated rank-wall family. The main theorem proves `ForceMate σ q` from exact strong-turn KRK and S.rank<R.rank<W.rank, with no initial rook-safety or king/file-offset assumption. Every S028 PhaseImage is included. A direct vertical-entry subfamily is also proved. This is not arbitrary-arrival KRK setup.

## The successful policy and measure

Use a broad strong-turn rank wall, allowing a threatened rook which is repaired before the next weak turn. First prove the ready case with rook/lone file margin≥2. Upper-band states raise the rook; aligned lower-band states check with a two-file margin, mating at the edge or raising the wall against every reply. These use strictly smaller 7−rookRank. If the strong king is too far below the wall, advance it one rank, using a strictly smaller rook/strong rank gap. The finite lower-band pursuit closes the remaining ready case. Finally normalize any initial margin<2 by a legal far-file rook move and reuse the already proved ready case at unchanged measures.

For lower-band pursuit, orient the file toward the lone king. Offset one uses a distinct far/second-far rook waiting move. Offset≥2 and margin≥3 uses a king-file step, which strictly reduces remaining distance to the approached edge; every non-exit reply retains direction. Margin two is normalized to the far file. Its offset-two→one branch is followed by one explicit waiting move; a non-exit reply returns the original lone file and the new rook margin is≥3. The d/e switch and both physical directions are proved symbolically. There are at most three rook turns before a recursive king advance, so the old chase cycle is not an allowed infinite execution of the new policy.

The conditional `LowerExitWins` interface is discharged in the final theorem by the strictly higher-rank induction cases. No same-measure ForceMate assumption remains. The frozen finite-branching forcing rules combine chosen moves, nonempty defending reply sets and every legal reply into a uniform finite win. The three well-founded pieces are nested wall rank, king/rook gap and oriented king-file distance; bounded rook tempos are finite branches.

The Python coordinate policy independently follows these moves on 64 selected local trajectories: eight fixed wall inputs, both strong colours and four immediate-reply stress selectors. All ended in actual checkmate, including the old chase-cycle start and the protected-corner stalemate trap. This is error finding, not a class graph, minimax computation, value oracle or proof of the general family. General correctness comes from the symbolic Lean proof. Observed ply counts are not a DTM theorem.

## Arbitrary setup remains a separate problem

`krk_vertical_wall_entry_force` covers W at least two ranks above S, rook file distinct from S, rook/lone file distance≥2: move the rook directly to S.rank+1, or use the wall theorem if already there. All replies are legal, non-capturing, nonempty and enter the winning wall family.

A naive direct setup fails outside that domain. White Ka1/Rd4, Black Kc3, White to move: Rd2 Kxd2 and Rb4 Kxb4 are legal and end in KK. Both attempted rook placements create a geometric wall, but the subsequent weak capture destroys it. The current wall theorem deliberately starts on the *strong* turn, so a bare weak-turn wall is insufficient. Fixed kernel witnesses and local ray-walking checks confirm both failures.

Equal-rank kings (e.g. Ka1/Kc1 with a rook off their rank) require choosing another axis; downward separation requires reflection. The current direct policy constructs only physical left/right pursuit within the positive-rank wall. A generic full-kernel rotation/flags-preservation theorem has not been assumed or proved. Extending `StepM`'s cooperative geometry alone does not transport the all-defences ForceMate result.

Promising next work is a proved non-castling KRK transport (with explicit weak-reply completeness and flags handling), or a direct parameterized oriented-wall policy, followed by a safe multi-move rook retreat/setup against every reply. A defender may change which axis has king separation while the rook is being moved; any setup argument must handle that change rather than assuming a cooperative reply or the original gap. Source legality/arrival may supply useful exclusions of incoming check or blocked rays, but must be stated and proved.

EC-C016/017/018 are new prerequisites/results; Gate F status is recorded only after exact-source verification. EC-C011 remains PROPOSED until arbitrary-arrival setup and correct weak-turn terminal/capture cases are closed. No frozen-ledger change, full KRK WDL, clock/repetition, exact-distance or initial-position result is claimed.
