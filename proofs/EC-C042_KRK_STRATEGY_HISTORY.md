# EC-C042 — Actual-history strategy lifting and an 84-ply KRK wall family

S071, 2026-10-20. Classical finite-rank strategy/count argument, no novelty claim.
Sources: frozen raw stopped-history Layer (EC-T0036), clock/count/append lemmas,
EC-T0037 coordinate KRK bound and S070 EC-C041 verified rank strategy (freeze
pending). No engine, tablebase, class enumeration or per-position certificates.
Standalone paper and separate same-agent audit precede Lean.

## Domain, exact claim and sufficiency

Use the EXISTING RawHistoryLayer.State: an actual initial-rooted stored trace
with its strict-prefix admissibility proof for the chosen raw classifier. Erasure
q retains actual endpoint. Winner σ and budget N are arbitrary. Define Hσ(s) by:

    for every raw Position r, if ForceMate σ r and dσ(r)<dσ(erase s),
    then occurrences(s.trace,r)<2.

The queried key is the NEW queried position r's normalized raw key, counted in
ALL incoming stored endpoints including initial/current. d is the verified
strategyRank, the least clock-free mate budget for winning inputs. Losing/default
rank-zero positions do not enter H. H is a static predicate on the incoming
full-history histogram, not a premise about all future raw paths.

Assume MateWithin σ N q, clock(s.trace)+N<100, currentOccurrences(s)<3 and Hσ(s).
Then HistoryLayer.RuleMateWithin RawHistoryLayer.layer σ N s holds at the SAME N.
Both colours and arbitrary flags; all legal defensive replies and intended moves
are retained. Strong nodes use a chosen rank-decreasing move only. This statement
is SUFFICIENT, not necessary, and is not asserted for every history. Failure of
any premise proves no draw. The chosen raw classifier/claim semantics are not
a certified full FIDE history implementation.

Concrete partial family: exact strong-turn KRK with S.y<R.y<W.y and R.y=6, an
admitted raw s with that endpoint, clock+84<100 (equivalently clock≤15), current
count<3 and Hσ(s), has raw RuleMateWithin at 84 plies. Use the frozen coordinate
wall bound 84*(7−R.y)=84. Both colours/all flags and ALL defending replies.
No unrestricted KRK outcome or exact distance claim. This is a conditional family;
no witness of a compatible initial-rooted history is supplied by the statement.

## Direct dependency admission

The blocked KRK milestone B step is actual append/current-and-intended count
control along the winning strategy, with earlier history retained. EC-C041 proves
new-line uniqueness but not incoming counts; EC-C039 requires all raw future
continuations, including unchosen losing/cycling strong moves. The smallest
needed helper here is preservation of H under ONE actual rank-decreasing legal
append, together with its new current count<3. It immediately serves this exact
lifting and the rank-six wall corollary. Exit: return to quantitative coverage,
FIDE correspondence and outcomes after this certificate; no unrelated generic
lemma series. No generic rule-budget monotonicity theorem is required: induction
on the supplied N uses the frozen clock-free budget monotonicity at children.

## 1. Actual append certificate

Let s be any raw stored state, m an actual legal move and t=append s m hm.
Assume Hσ(s), child Win(erase t) and d(erase t)<d(erase s).

The frozen append_currentOccurrences law gives currentOccurrences(t) equal to
occurrences(s.trace,erase t)+1. H at this winning lower-rank child bounds the
OLD count by one; adding the NEW endpoint yields at most two, strictly below
three. It is not old-current-count plus one.

For any winning r with d(r)<d(erase t), transitivity puts r below the parent's
rank, so Hσ(s) gives occurrences(s.trace,r)<2. Equal keys of erase t and r
would imply equal ranks by EC-C041, contradicting strict inequality. Therefore
the exact RawOccurrences.append law adds ZERO to this future query. It retains
all previous endpoints and yields occurrences(t.trace,r)<2, proving Hσ(t).
No reset truncates the stored history; all raw flags/effective ep are handled by
the proved key-rank invariant. No field of the actual trace/move is replaced.

## 2. Induction on supplied ply budget

At N=0, MateWithin is the exact named goal; so is RuleMateWithin zero. At N=n+1,
an early named goal is also terminal immediately, without ongoing/claim guards.
Suppose not a named goal. Write Win(q) from the supplied budget. Minimality gives
d(q)≤n+1, and rank progress gives a chosen descending legal strong child or a
nonempty set of ALL descending legal weak children, according to the turn.
Every chosen/defensive child is winning and has rank≤n. Its exact least-budget
certificate pads to MateWithin σ n child by frozen mateWithin_mono.

The parent is nondead by Win and has at least one legal move by progress. Its
clock is<100<150 and current count<3<5. The frozen raw ongoing iff therefore
supplies Ongoing s. An actual legal append from this admissible ongoing parent
is admitted by the existing stopped-history append equivalence, INCLUDING
terminal children. No child-ongoing filter is imposed.

For every retained actual child, the append helper gives current count<3 and H.
The frozen clock step inequality gives clock(child)≤clock(parent)+1, hence
clock(child)+n<100 from the supplied parent budget. Along with its padded
MateWithin n certificate these are exactly the induction hypotheses. The child
raw RuleMateWithin n follows at its actual stored state.

## 3. Strong choices and all defensive claims

If q.turn=σ, use progress to choose one descending legal move, retain its actual
move/legality/append endpoint, obtain the admitted child and apply induction.
The strong rule recurrence requires Ongoing and this chosen child; it does NOT
require noClaim or bounds for unchosen strong legal children. They may repeat,
lose the rook or fail the histogram; none is silently asserted safe.

If q.turn=σ.opp, progress says EVERY legal successor is winning and descending,
with a nonempty legal reply set. Therefore every actual legal intended append
has clock<100 (one ply≤the positive parent budget) and count<3 by the append
helper. Current root clock/count are also below100/3. This excludes both current
and intended RawClaims.AvailableThreshold, yielding noClaim for the DEFENDER.
It is not enough merely to inspect executed replies or the root's old key.

Lift a witness for nonempty BoardStep using the existing full reply interface.
For EVERY BoardStep child, raw step soundness gives Legal, progress supplies
winning/rank descent, and the same actual append certificate and induction apply.
All weak legal replies remain, including children which are terminal in the
raw classifier. A legal rook capture to dead KK cannot coexist with the winning
weak certificate; this is a consequence of forcing, not a Legal-relation filter.
The frozen rule recurrence then gives RuleMateWithin at n+1.

## 4. Concrete quantitative KRK payoff

For the stated admitted rank-six wall, EC-T0037 supplies clock-free MateWithin
at 84*(7−6)=84 with no additional safety assumption on the strong-turn rook.
Apply the same-budget lifting theorem with N=84 and the explicit clock/current/
incoming-histogram hypotheses. This is the promised direct KRK partial family.
The proof uses actual stored histories; it does not use arbitrary unrooted seeds
as if admissible or assume a legal-history compatibility witness.

The global 508 ceiling cannot satisfy clock+508<100 at a nonnegative clock.
Using the coordinate bound is essential. The 84 budget is conservative and not
an evaluated exact mate distance or DTZ. Hypotheses H and current count remain
explicit; this paper does not prove they cover every compatible KRK history.

## 5. Remaining work and status

This establishes a strategy-specific sufficient RAW rule-mate certificate,
provided its exact proof is verified. Full FIDE key/adjudication/claim/rights
correspondence, complete history-dependent outcomes and holding, better broad
clock bounds and exact WDL/DTZ distances remain open. New-line nonrepetition does
not itself replace incoming H. Failure of the sufficient family is not draw.

At paper creation: LOCAL_VERIFIED after the separate same-agent audit; Lean,
Gate F and separate Gate Z pending. EC-C041 also awaits freeze. 37 frozen bundles;
partial raw-family progress must not be reported as complete KRK closure.

S071 verification addendum: exact statements FORMAL_VERIFIED at `c6e62cc4b2c96061bdb7465eb99f9cc901941b0c`; [observed evidence](../sessions/evidence/S071/README.md). Separate Gate Z pending. Earlier paper-creation status is historical.
