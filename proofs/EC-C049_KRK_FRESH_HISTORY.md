# EC-C049 — Clock-zero KRK history control and an incoming-history-free wall family

S084,2026-10-21. LOCAL_VERIFIED after the separate pre-Lean paper audit.
Classical material closure, trace induction and least-rank
strategy counting, no novelty claim. Sources: existing actual admitted RAW
histories, full normalized-key counts, all-move KRK closure, frozen key-rank
strategy and73-ply framed-wall geometry. No oracle/tablebase/class enumeration
or stored per-position certificate. Full history is retained in all definitions.

## Exact domain and principal payoff

Write Query_sigma(r) for exact KRK material of colour sigma at raw Position r.
An admitted RAW State retains its entire initial-rooted trace and strict-prefix
ongoing proof. Let H_KRK(sigma,s) mean: for EVERY raw query r, if Query_sigma(r),
clock-free ForceMate(sigma,r), and rank(r)<rank(erase(s)), its full incoming
normalized-key occurrence count is <2. The query restriction is essential:
earlier larger-material winning keys need not satisfy the older ALL-material
LowerRankHistory predicate and cannot match a future exact KRK board.

Main payoff: for every admitted state matching a strong-turn exact KRK wall
in any proved frame g, transformed rook rank6, and stored clock0, prove the
existing RAW RuleMateWithin at73 board plies AND an actual bounded winning
policy. NO root-count or incoming lower-rank histogram premise remains.
Both colours/all actual flags, every legal weak executed/intended reply, full
incoming history. No compatible full-history witness is supplied or assumed
from an arbitrary board/count vector. This is a partial RAW family, not all
low-clock KRK, full FIDE correspondence or exact/global WDL/DTZ.

Exact blocked step: current frozen73 family needs an all-material incoming
histogram not entailed by clock0. Smallest new dependency is actual KRK prefix
closure and absence of earlier KRK keys after a last reset into a nondead
endpoint, followed by KRK-restricted rank-history lifting. Exit is this direct
incoming-assumption removal, not a generic material/history lemma sequence.

## 1. Key equality preserves KRK material

The existing key is normalizeEP(q), which changes only ep. Therefore equal
keys imply equal piece boards. If r has Query_sigma and key(p)=key(r), p has
the same exact KRK board with the same three distinct squares and colour.
No full FIDE key equivalence, rights invariant or raw ep=None theorem is used.

## 2. An earlier KRK prefix forces later admitted Region

For any actual admitted trace t, suppose some stored endpoint p (including
initial/current) has Query_sigma. Prove Region_sigma at the final admitted
state, by induction on t. Initial has a pawn on a2 and cannot be KRK.
At append, an occurrence is either the new current endpoint, giving exact KRK
directly, or lies in the prior trace. In the latter case the parent is itself
admitted and induction gives its Region. The actual typed BoardStep preserves
Region by the frozen all-move theorem. Castling, bad strong moves and rook
captures all remain. A terminal parent cannot be extended by an admitted child.

In particular, if that endpoint is ongoing, the terminal disjunct is impossible
and it must still have exact same-colour KRK. This is not a silent appeal to
general irreversible material counts or a raw extension after a terminal.

## 3. Clock-zero nondead endpoint has no earlier KRK endpoint

Fix an admitted s with stored clock0 and board NONDEAD. At the initial trace
there is no KRK query endpoint. Otherwise write its actual trace as prior plus
last legal m. The parent is admitted and ongoing by strict-prefix admission.
Suppose any endpoint in prior was Query_sigma. Section2 gives parent Region;
ongoing eliminates its terminal disjunct, yielding exact parent KRK. Apply the
actual all-move material/clock law to last m:

* quiet retained KRK forces stored child clock=parent clock+1>0, contradiction;
* dead KK child contradicts the given child nondeadness, regardless of reset.

Thus prior contains NO Query_sigma endpoint. By section1 it also contains NO
endpoint whose key matches ANY Query_sigma query r. The generic full occurrence
definition is a filtered count, so each such old count is0. At append the
actual count law adds at most1 for the current endpoint, hence EVERY KRK query
has full-history count<=1. No history implementation is pruned or reset; the
zero count is proved for these queries while all earlier larger material stays.

Nondeadness is explicit in this lemma. It follows from the clock-free winning
wall theorem at the intended root, not from an unproved claim that clock0
positions always win. A terminal mate is nondead and is handled consistently.

## 4. Restricted rank-history preservation on an actual append

Assume H_KRK at raw s, an actual legal move m whose child is Query_sigma,
clock-free winning and has STRICTLY lower least winning rank. Old query count
at the child is<2 by H_KRK. Exact append_currentOccurrences adds1, giving new
current count<3. For a future Query_sigma winning r of rank<child rank, it is
also lower than parent rank, so its old count<2. Its key differs from child's
key: equal keys have equal least ranks by the frozen strategy-rank-key theorem,
contradicting strict inequality. The generic append count adds0 for that query,
so H_KRK is preserved. Every full prior endpoint is still counted.

Any actual legal move from exact KRK whose child has CLOCK-FREE ForceMate for
sigma has retained exact KRK: the all-move material law's dead-KK branch
contradicts clock-free forceMate_not_dead. This uses an existing clock-free
certificate, NEVER the RAW certificate being proved later, avoiding circularity.

## 5. KRK-restricted same-budget RAW lifting

For an admitted exact KRK root s with supplied MateWithin(sigma,N), assume
clock(s)+N<100, root current count<3 and H_KRK. Prove RAW W(sigma,N,s) by
induction on N, following the existing least-rank strategy. Immediate Goal is
unchanged. At a nonmate winning node, the frozen strategy_progress gives a
chosen strict-lower winning strong move and ALL strict-lower winning weak
replies, plus nonemptiness. Section4 and actual material law put each child
in exact KRK and preserve restricted history/current counts. Parent clock
budget and frozen append upper bound give child clock+N-1<100. Apply induction.

Ongoing at the parent follows clock-free nondeadness/nonempty replies, root
count<3 and clock<100. At a weak node EVERY legal intended move has a lower
winning KRK child, so section4 bounds its prospective count<3, and the clock
bound puts prospective clock<100. Thus NO current OR intended claim, even if
its raw child might otherwise terminate. No defensive child is filtered.
At a strong node own claims can be declined. Rebuild the actual old RAW
recurrence at the SAME N, retaining full initial/prior/current trace.

The older all-material LowerRankHistory theorem is neither rewritten nor
claimed to follow. New additive modules certify precisely this weaker KRK-
restricted sufficient invariant with actual KRK preservation proved.

## 6. General clock-zero supplied-budget lift and the wall family

For ANY admitted exact KRK root of clock0, a supplied clock-free
MateWithin(sigma,N) with N<100 lifts to the SAME RAW W(sigma,N) and ActualWin,
without any supplied incoming counts. Its clock-free certificate gives board
nondeadness; section3 supplies all KRK query counts<=1, hence root count<3 and
H_KRK. Section5 now applies at that same N. No assumption that every KRK root
has such a numeric sub100 certificate is introduced.

For the stated strong-turn framed rank-six wall use the frozen geometric
MateWithin73 theorem on original erasure; history is not transformed by g.
Clock0 gives clock+73<100. Clock-free forcing implies board nondeadness, so
section3 bounds EVERY KRK query count<=1. The current root is KRK, hence its
current count<3; every restricted lower-rank query also has count<2. Section5
gives actual RAW W73 with no supplied incoming histogram. Its F witness and
existing actual winning-policy correspondence on Region give ActualWin.

This is constructive proof-based coverage of the declared family. It supplies
an upper bound73, not optimal DTM or DTZ. No numerical universal sub100 maximum,
full low-clock arbitrary-board classification, FIDE correspondence, global
distance or class closure follows. Continue those direct obligations afterward.

Observed Gate F: OWN source `2469238e2ec6a9aa39c157923c7a03165be48307`; NEW GitHub clone without .lake, full208-job build exit0 in370.859s; COMPLETE390-report runner exit0 at2026-10-21T09:06:45Z. Whole working/clean runner and exact published Git source bytes match. All8 main types/9 complete modules/imports inspected. Official native Windows Lean4.35.0; source/import/executable hashes, commands/exits/times/UTC, clean HEAD/tree/status retained. No source/dependency/shim/TLS/checksum changes; hosted CI unobserved. Separate Gate Z pending.
