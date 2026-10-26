# Exact incoming-key barriers on a KRK rook ray

This result evaluates the rook-entry branches needed after a defender leaves
the middle-file opposition region. It is a full-history RAW outcome theorem
for the stated strong-turn family, not global KRK closure.

Assume an ongoing admitted strong-turn KRK history H, halfmove clock h>=96,
W=(x,0), 2<=x<=5, S.y=2, R.y>=3, and one of the following orientations:

* S.x=x+1 and the required rook destination file f=x-1;
* S.x=x-1 and the required rook destination file f=x+1.

Every winning first move must relocate the rook to file f. Immediate mate is
impossible because S is off W's file. A king entry would require either a
zero-length move to the same king square or a two-file jump. The checked
three-ply theorem excludes castling as an alternative entry.

## An evaluated interval and two key queries

For a candidate landing rank y define

    Allowed(y) iff 2<=y<=7 and
      [(R.x=f and y!=R.y) or (R.x!=f and y=R.y)].

Thus a rook already on file f may choose any rank from two through seven,
excluding its source square. Otherwise there is exactly one possible crossing,
at its present rank. Both kings lie outside a vertical ray. A horizontal
crossing is at rank at least three and therefore passes neither king.

Let m_y be the actual canonical rook move from R to (f,y). Let q1=play(q,m_y).
The unique subsequent weak move is w=(W,(S.x,0),none); write q2=play(q1,w).
Count both normalized RAW keys in the **entire incoming trace H**, before
either move is appended. Then

    ActualWin_strong
      iff h<98 and there exists Allowed(y) with c_H(q1)<2 and c_H(q2)<2.

This criterion contains one rank interval, one excluded source rank, and two
original-history key queries. It contains no unknown outcome value, recursive
game predicate, move search, or per-position value table. The key queries use
actual play, including all castling-right and en-passant updates.

If every available rank violates either incoming-key condition, the defender
has a RAW holding policy against **every** legal strong alternative. If the
criterion holds, the optimal board-ply distance is exactly three; a certificate
of distance at most two is impossible in this family.

## Proof correspondence

The central last-reply formula fixes the landing file and requires y>=2.
Clear rook geometry reduces exactly to Allowed. Both canonical kernel moves
are proved legal. Uniqueness of the weak reply identifies its full source,
destination and promotion data, so no extra intended move is discarded.
The checked three-ply history theorem then reduces to the displayed two key
inequalities, with necessity and sufficiency on the original incoming trace.

`KRKRookRayBarriers.lean` contains Side, AllowedRank, ClearRay, ray_last_iff,
ray_sees_iff, high_clock_force_iff, high_clock_actual_iff,
high_clock_hold_iff and high_clock_exact_three. The focused build
`lake build EndgameChess.Rules.KRKRookRayBarriers` passed.
The aggregate `lake build` passed (264 jobs), and `lake env lean AxiomCheck.lean`
passed. The new public declarations use only `propext`, `Classical.choice`,
and `Quot.sound`.

The supporting weak_move_eq/lone_step_legal and rook_entry_legal lemmas expose
canonical actual moves from the already checked geometry. They preserve the
actual flags through play. Existing frozen sources and manifests are unchanged.

The preceding weak-turn wrapper is now checked separately in
[the central weak history theorem](KRK_CENTRAL_WEAK_HISTORY.md), retaining both
possible first weak replies and reconciling their appended keys with the
earlier incoming trace. Full FIDE correspondence and global WDL/DTZ remain open.
