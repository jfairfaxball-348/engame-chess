# Incoming-history target for the checked central four-ply region

**NOT YET LEAN-PROVED.** The board region on middle files is checked, and the
[strong rook-ray barrier theorem](../proofs/KRK_ROOK_RAY_BARRIERS.md) is checked.
This note fixes the exact remaining weak-root history formula and proof route.

Fix an ongoing admitted weak-turn root q with W=(x,0), S=(x,2), 3<=x<=4,
R.y>=3, incoming trace H and h>=95. The only possible weak replies are

    L=(x-1,0), allowed iff R.x!=x-1;
    U=(x+1,0), allowed iff R.x!=x+1.

At least one is allowed. Source-rook rank >=3 rules out captures, and the king
controls all inward moves. The strong child after L requires rook file x-2;
after U it requires file x+2. Every winning strong move is a rook relocation,
with landing rank in the checked Allowed interval. The forced final weak reply
returns to the original square W.

The proposed complete RAW forcing criterion in this opposition family is:

1. h<97 and c_H(q)<3;
2. for each allowed t in {L,U}, c_H(play(q,weak_move_t))<2;
3. for each such t, there exists an Allowed landing rank y on the required file
   with both following intermediate keys having c_H<2:
   q2=play(play(q,weak_move_t),rook_move_y), and
   q3=play(q2,weak_return_to_W).

There are two branch-specific rank intervals and three key queries per allowed
branch; the original trace H is fixed throughout. The rank chosen by the
attacker may depend on the actual first weak reply. The formula must not demand
one common rook rank for both branches.

Why prefix counts do not change those future queries: q1 after the first weak
move has strong turn, while q2 has weak turn. Their keys differ. The other
queried strong position q3 has weak king W, whereas q1 has weak king t!=W.
Its key also differs from q1. Thus appending q1 contributes zero to both later
barrier queries. Root current count and q1's intended-claim count are separate
conditions; omitting either would change the outcome.

Suggested Lean steps: prove a key inequality from different exact weak-king
squares; rewrite occurrence counts across the first append; prove the two
actual weak branches and their rook-file guards; apply the checked ray theorem
to every allowed branch, with child ongoingness derived from the supplied
counts, clock and nondead board certificate. The matching defender implication
must retain every legal strong move, using ray necessity rather than failure of
a selected policy. Winning distance here should be four, since LastReply is
disjoint from direct opposition on these central files.

After this wrapper, incorporate the existing LastReply root branch and then
prove the remaining edge files/corners. The full KRK objective remains open.
