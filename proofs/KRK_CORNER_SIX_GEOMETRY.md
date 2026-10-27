# Exact six-ply corner geometry (locally checked, unfrozen)

KRK remains open. This result evaluates the clock-free kernel at the canonical
weak corner W=(0,0). It does not clear incoming history barriers, certify FIDE
correspondence, or classify the full material class.

Let K=(a,b) and R=(x,y). Assume exact KRK material, the weak side to move,
and Chebyshev distance d(K,W)>=2. Actual board flags are retained in the kernel
statement. Then the strong side can force mate within six plies if and only if:

* W is already mated (`KRKMateGeometry.Terminal`); or
* the rook is safe, the weak king has a legal reply, and the following region holds.

| Strong king K | Rook condition |
|---|---|
| (0,2) | y>=2, or x=2, or R=(3,1) |
| (2,0) | x>=2, or y=2, or R=(1,3) |
| (1,2) | y>=1 |
| (2,1) | x>=1 |
| (2,2) | any rook, subject to the safety and legal-reply requirements |
| (0,3) | y=1 and x in {2,3} |
| (3,0) | x=1 and y in {2,3} |
| (1,3) | y=1 and x>=2 |
| (2,3) | y=1 and x>=2, or x=1 and y>=4 |
| (3,1) | x=1 and y>=2 |
| (3,2) | x=1 and y>=2, or y=1 and x>=4 |
| (3,3) | x=1 and y>=4, or y=1 and x>=4 |

These are twelve symbolic king points with rook inequalities; no position-value
atlas, tablebase, engine, or exhaustive outcome certificate is used.

## Argument and correspondence

`KRKSixGeometry.kernel_six_iff` reduces a nonmated weak root to a safe rook,
a legal reply, and five-ply forcing after every legal reply. An inward reply at
(1,1) would have positive edge depth, contradicting the proved five-ply depth
bound. The two remaining replies are (1,0) and (0,1). The exact
`KRKFiveNear.Five` formula evaluates each. Strong-king proximity and exact rook
visibility account for replies that are illegal.

`corner_six_necessary` derives the table by symbolic coordinate regions. Exact
visibility matters: a strong king can block a rook that is merely aligned.
`live_not_diagonal_rook` eliminates R=(1,1), since all corner neighbours would
then be occupied or attacked under the separated-king assumption. This is where
the nonempty legal-reply hypothesis is essential; a universal condition alone
would also hold at stalemate.

For sufficiency, `region_excludes_inward` excludes the inward move in every table
family. `region_south_five` proves the explicit five-ply criterion after every
legal (1,0) reply. `region_swap` and pure geometric transport handle (0,1).
`region_replies` assembles all legal replies, and `kernel_six_iff` proves the exact
criterion for the actual kernel position. Mate is handled first, preserving its
precedence; stalemate cannot satisfy the nonempty-reply requirement.

Main source: `formal/EndgameChess/Rules/KRKSixCorner.lean`.
All public main declarations are included in `formal/AxiomCheck.lean`.
Local verification: `lake build` PASS (317 jobs); `lake env lean AxiomCheck.lean` PASS.
Every new public theorem reports only `propext`, `Classical.choice`, and
`Quot.sound`. No `sorry`, `admit`, unsafe proof escape or new axiom is used.
No frozen manifest or historical proof was changed; no hosted CI claim is made.

Remaining near/second-edge six-ply geometry and native history conditions are
still required for the next strong/weak clock bands. This result alone does not
classify those bands or supply global distances.
