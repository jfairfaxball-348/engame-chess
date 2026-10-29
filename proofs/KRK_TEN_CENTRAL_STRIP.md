# Ten-ply exclusion on the central first strips

Certification update (2026-10-29): checked results are included in EC-T0049; see the [bundle scope and proof correspondence](KRK_BOUNDED_FRONTIER_CERTIFICATION.md). Any local-build counts or unfrozen/uncommitted statements below describe the pre-certification research checkpoint, not current publication status. Mathematical open obligations remain open.

`KRKTenCentralStrip.middle_kernel_no_ten` excludes weak-turn forcing
within ten plies on all eight central first-strip squares: (1,3),
(1,4), (6,3), (6,4) and their transposes. The theorem covers distinct
pieces, separated kings, both colours and actual native flags.

At W=(1,3), four neighbouring squares are outside the strong nine-ply
weak-square domain: (1,4), (2,2), (2,3), (2,4). They must be covered.
The symbolic covering constraints and rook safety leave four families:

* K file 3, rank 2 or 3, R rank 4;
* K rank 5, file at most 2, R file 2;
* K=(3,3), R file 1;
* adjacent protected R=(2,4).

In the first two families the legal escape (1,2) contradicts the exact
nine-ply near-strip criterion. The protected-rook family reduces to
one of those exclusions: rook safety and king separation force K file 3
or rank 5. The protected rook is retained until that argument is applied.

In the opposition family K=(3,3), R file 1, safety forces R rank at
most 1 or at least 5. In the lower case the weak escape (0,3), after
coordinate transposition, leaves a rank-three strong king and a rank-one
rook on file at most 2 at weak square (3,0). In the upper case the weak
escape (0,4), followed by transposition and file reflection, gives the
same obstruction. `KRKNineMiddleLow.no_nine` excludes all such boards.

For that obstruction, a weak eight-ply destination at W=(3,0) cannot
have strong-king rank at least three: its three interior neighbours force
R rank 1, and the legal escape (4,0) then requires K rank 2 by the exact
central-edge seven-ply formula. A strong nine-ply rook entry therefore
cannot keep its king on rank three. A king entry must reach rank two.
If its rook is on rank 1 and file at most 2, the escape (4,0) forces K
file 4, after which the other legal escape (2,0) contradicts the exact
second-edge seven-ply criterion. This treats every strong first move.

Reflection and transposition transport the canonical exclusion to all
eight squares, acting on coordinates only. In particular no rights or
incoming histories are normalized.

`KRKTenCentralStripHolding.high_clock_holding` then proves both-player
RAW holding at strong h>=88 on these squares for every admitted original
history. A win would have budget at most twelve, hence a weak child
within eleven plies; parity reduces eleven to ten and contradicts the
geometric exclusion. The native first move may be any legal move.

A small local covering diagnostic inspected the prison boundary; no
position values, tablebases or engine oracle supplied proof data. The
Lean proof uses symbolic covering and ray inequalities, and includes the
adjacent protected rook case. The full local build and expanded axiom
audit pass with only propext, Classical.choice and Quot.sound. These
results remain unfrozen and do not complete the ten-ply destination
catalogue or the full KRK class.
