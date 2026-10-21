# EC-C047 — All-history strong nonloss and exact high-clock RAW KRK forcing

S080,2026-10-21. LOCAL_VERIFIED after the separate adversarial paper audit.
Classical king-safety, material and claim
arguments, no novelty claim. All statements refer to the EXISTING admitted RAW
history layer. Sources are actual Legal/play, all-move KRK closure, raw current/
intended claims and frozen holding/forcing interfaces. No oracle, tablebase,
board enumeration or stored per-position certificate.

## Exact targets and domain

For any admitted state s of exact KRK material colour sigma, both turns,
all actual flags and EVERY incoming full history/clock/key count:

1. Strong side sigma has an actual legal RAW holding policy. The lone side
   cannot force mate under RAW rules. This is universal strong nonloss, not
   universal strong winning.
2. If s is ongoing, weak to move and h(s)>=99, sigma has NO RAW forcing
   certificate, and the weak side has a legal holding policy. Both sides hold.
3. If s is ongoing, strong to move and h(s)>=98, sigma forces mate IFF an
   ACTUAL admitted board child is immediate named mate. If there is no such
   immediate move, both sides hold. Incoming counts remain entirely unrestricted.

These are exact high-clock criteria, not merely sufficient certificates. The
boundary is intentionally 98/99, reflecting an intended claim before execution.
An immediate strong mate at child clock150 still wins. The root ongoing guard
already rules out an automatic root draw; no h<150 assumption is invented.
Forcing as a finite certificate remains the existing named objective; no
new geometric optimal-distance or full FIDE/WDL/DTZ claim is made.

## 1. Strong cannot already be mated at an arisen exact KRK endpoint

An actual KRK trace is not initial (initial has a pawn on a2), so its endpoint
has an actual last legal predecessor p. If endpoint turn is strong, p.turn is
weak. The last move left weak king safe by Legal's mover-safety theorem. On
exact KRK, weak in-check iff kings adjacent OR rook sees the weak king. Thus
kings are not adjacent. Strong in-check iff the weak king is adjacent, using
symmetry of king distance. Therefore strong is NOT in check and cannot be
mated. If endpoint turn is weak, named weak Goal already fails the turn guard.
No general full-board king-count invariant is needed; exact material supplies
the two kings and the sole rook.

Every actual step from KRK either retains exact KRK or yields dead KK. Let
Good_sigma(s) be exact KRK OR DeadK(erase(s)). A typed step from Good cannot
start in its dead disjunct, since parent is ongoing and hence nondead. From
its KRK disjunct the actual material closure gives KRK or dead KK. Thus Good
is preserved by EVERY admitted board move, all flags including strong castling.
At a dead endpoint no colour's Goal is possible (zero-length ReachK contradicts
DeadK). At an exact KRK endpoint the preceding argument excludes weak Goal.

Choose ANY globally legal strong policy (the S078 policy existence theorem
provides one without needing a nonforcing root). Induction along every compliant
prefix preserves Good and excludes weak Goal. Thus it is a strong holding
policy. The S078 converse refutes every weak forcing certificate. Clocks,
incoming repetitions and optional claims only stop more plays; none creates
a weak mating branch. This holds at all admitted exact KRK roots.

## 2. Elementary rule-certificate inversions

At a terminal admitted state t, a finite rule-win certificate for sigma implies
Goal(sigma,t): budget0 is the goal; a positive n has goal OR ongoing, and the
latter contradicts terminal. On an ongoing state Goal(any colour) is impossible,
since ongoing supplies a legal reply whereas actual MatedK forbids any reply.

At an ongoing weak-turn state a putative strong certificate therefore uses
the defender branch, which has NO CanClaim and covers EVERY admitted child.
Its wrong winner-turn branch contradicts opposite colours. At an ongoing
strong-turn state a certificate uses a chosen actual child with a smaller
certificate. Conversely any actual immediate goal child gives a one-ply
certificate from the ongoing strong root, even if that child reaches150.

## 3. Weak-turn h>=99: quiet intended claim or dead capture

Assume a strong certificate at ongoing weak-turn s. Choose any actual legal
move m from ongoing reply existence and its admitted child t by full lifting.
The certificate covers t. Actual all-move KRK closure says either quiet retained
KRK or dead KK. In the dead case, certificate projection gives clock-free
ForceMate at a dead child, contradicting frozen forceMate_not_dead.

Thus the chosen actual move is quiet. Exact append_clock gives h(child)=h(s)+1,
so h(child)>=100. This is CurrentThreshold at the actual prospective append,
hence an IntendedThreshold at s and CanClaim(s). It contradicts the certificate's
NO claim condition. The proof needs no repetition premise; additional repetition
claims can only help the defender. In a nonwinning position the S078 theorem
extracts a real weak holding policy. Section1 supplies strong holding, so both
hold. It is not inferred from failure of the earlier sufficient73 family.

An immediate weak rook capture may also draw without a quiet claim. The proof
does not falsely assert every ongoing weak KRK state has a quiet legal move;
it derives quietness only under the putative forcing certificate, excluding
dead children by that certificate. This guards the forced-capture boundary.

## 4. Strong-turn h>=98: exact immediate-mate criterion

Any strong certificate at ongoing s chooses an admitted child t. Actual legal
strong material closure retains exact KRK, and strong legal targets are empty
and nonpawn, so exact quiet append gives h(t)=h(s)+1>=99. Turns alternate to weak.

If t is ongoing, section3 excludes its strong certificate. If t is terminal,
section2 shows its certificate must already be Goal(sigma,t). Therefore the
chosen move mates immediately. Conversely any immediate goal child gives
the one-ply certificate from section2. This proves necessity AND sufficiency
with no incoming-count restriction. If no immediate goal child exists, strong
nonforcing gives weak holding via S078, while section1 gives strong holding.

No next turn is fabricated after automatic draw, deadness, stalemate or mate.
A legal strong move that immediately draws is retained and cannot satisfy the
child certificate. A child at149 or150 that mates is Goal and allowed; a claim
would have stopped at its parent if the claimant had chosen one, but sigma
may decline its own claims in favour of mate. Policy/certificate semantics
therefore preserve mate-first precedence and zero-ply intended claims.

## 5. Local exact one-ply budget

On this ongoing strong high-clock family, F(sigma,s) iff W(sigma,1,s), while
W(sigma,0,s) is false because ongoing excludes actual mate. The forward
direction takes the actual immediate mate from section4; the converse uses
its one-ply certificate. Hence any win in this family has exact optimal budget
one BOARD ply. This corollary was also stated and audited in the pre-Lean paper
audit. It supplies no global DTM or DTZ convention comparison.

## Closure limits and next direct obligation

All-history strong holding and these high-clock forcing iff statements are
new RAW coverage, not an evaluation of low-clock arbitrary-history positions.
In the remaining region (weak h<99, strong h<98), repetition availability can
still stop strategically important lines and exact optimal geometry matters.
Neither the large442/443 ceiling nor key simplicity controls all incoming keys.
Full FIDE correspondence and exact WDL/DTZ are also still open. Continue the
direct low-clock/history classification rather than declaring KRK complete.

Observed Gate F: OWN source `6d295929f2e42aad5729fbe09083095d1dc37c89`; NEW GitHub clone without .lake, full190-job build exit0 in360.484s; COMPLETE374-report AxiomCheck exit0 at2026-10-21T08:24:51Z. Whole working/clean runner and published Git source bytes match. All10 public types/11 complete modules and transitive imports inspected. Official native Windows Lean4.35.0; source/import/executable hashes, commands/exits/times/UTC and clean HEAD/tree/status retained. No dependency/shim/TLS/checksum change. Hosted CI unobserved. Separate Gate Z pending.
