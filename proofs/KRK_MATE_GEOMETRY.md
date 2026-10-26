# KRK terminal geometry for the deadline lower-bound argument

Working supporting result for the positive-clock obligation. This does not
evaluate the fixed-history barrier game or close KRK. Coordinates are 0 through
7, with Chebyshev distance d. Assume three distinct squares S (strong king),
R (rook), W (weak king), d(S,W)>=2, and weak to move.

## Complete terminal formula

For a horizontal checking rook, mate is equivalent to all of:

* W_y is 0 or 7 and R_y=W_y;
* S_y=2 if W_y=0, and S_y=5 if W_y=7;
* |R_x-W_x|>=2;
* if 1<=W_x<=6, S_x=W_x;
* if W_x=0, S_x is 0 or 1; if W_x=7, S_x is 6 or 7.

The vertical case exchanges x and y. Their disjunction is the full terminal
formula. It includes the shifted king at a corner; requiring exact opposition
there would be false (for example Kb3, Rh1 versus Ka1).

Proof: because the kings are separated, check is from the rook. Consider the
horizontal case. Each on-board square directly above or below W is off the
rook's file and rank, so it must be controlled by S. If both exist, S is within
one of W, a contradiction. Thus W is on an edge. Its inward neighbour forces
S to be exactly two ranks inward and at most one file away. A rook adjacent
to W could now be captured: S is two ranks from its square. Thus the rook is
at least two files away. Each inward diagonal neighbour is consequently off
the rook's file and rank too; controlling all of them gives the stated file
constraints, including the two corner exceptions. Conversely those constraints
cover every inward escape by S and every edge escape by R, with no obstruction
or legal rook capture. The vertical argument is the transpose.

## Consequence to check before using as a distance lower bound

From a legal strong-turn KRK position with W not in check, an ordinary king
move cannot mate. A new rook check would have to be discovered by vacating a
square strictly between R and W. That source square is on the mating edge,
whereas the final king in the terminal formula is two lines inward. A king
cannot make that displacement in one move. This geometric ordinary-step
statement is checked in `king_step_not_mate`. Castling must be handled separately:
the resulting king and rook on the same back rank do not fit either template.
The full actual-move statement, including castling, is now proved separately
in [KRK_MATING_MOVES.md](KRK_MATING_MOVES.md); the original ordinary-step
theorem alone is not that stronger statement.

## Lean correspondence and proof critique

The new module [KRKMateGeometry.lean](../formal/EndgameChess/Rules/KRKMateGeometry.lean)
uses symbolic coordinate arithmetic, not board enumeration. `Horizontal`
encodes the six horizontal conditions above and `Terminal` is its disjunction
with the coordinate transpose. `mate_iff_terminal` proves equivalence to the
existing geometric `MateM`, under the explicit king-separation premise.
`kernel_mate_iff` proves equivalence to actual kernel `MatedK`, assuming exact
KRK, weak turn and king separation. Its necessity proof constructs a legal
escape whenever the geometric condition fails, including a legal capture of
an unprotected adjacent rook. Its sufficiency uses the frozen `mate_sound`.
Neither direction assumes a chosen strategy, safe rook, or incoming history.

The case split uses a checking rook's rank or file, not a global symmetry claim
for chess: the latter would be unsound with castling flags. Only the existing
geometric isometries are used before passing back to the kernel. Corner king
offsets and adjacent-rook captures are essential. The theorem concerns terminal
boards; it does not prove every such board has a history from the initial
position, and it does not infer an ongoing game's outcome from terminal shape.

Status: locally Lean-checked working result, not frozen. Main declarations are
included in `formal/AxiomCheck.lean`. No frozen proof, manifest or ledger entry
has been changed. A clean pinned-source certification has not been performed.

Local validation on 2026-10-26, Lean `v4.35.0`, core-only Lake project:
`lake build` succeeded (246 jobs, incremental; existing deprecation warnings
only). `lake env lean AxiomCheck.lean` exited 0; each of the seven new named
theorems reports exactly `propext`, `Classical.choice`, and `Quot.sound`.
These checks establish the stated terminal equivalence, not the unfinished
full actual-move/castling consequence or the positive-clock outcome criterion.

This supplies a necessary terminal constraint against every attacker choice,
not just a selected wall policy. It is not a matching minimax lower bound:
defender choices on earlier plies and incoming repetition barriers remain open.
No outcome values, engine output or tablebase are used as proof.
