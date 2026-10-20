# EC-C041 — Lean fidelity audit (S070)

Separate same-agent review, not independent external review. The paper and separate
paper audit preceded Lean. Source attribution and four-part admission against the
blocked direct KRK repetition step are in the paper. No oracle/tablebase/class
enumeration or stored position certificate; classical finite-attractor argument.

KeyInterface proves equal turn, all-colour check, EXACT Legal successor sets and
named MateGoal iff from normalized raw-key equality. Board/turn extraction explicitly
unfolds key/normalizeEP; raw ep equality is not assumed. key_legal_congr is the
frozen all-move kernel theorem. Same actual moves and full played endpoints are
retained, not merely equal child keys. KeyBudget handles zero/early goal and
strong/weak successors directly. Fixed-budget constructors establish target
nondeadness from common winning children; no DeadK key congruence is assumed.

LeastBudget proves a minimal natural witness by strong induction and classical
existence cases; it does not enumerate a class or execute a solver. RankDefinitions
chooses that witness only under ForceMate, with total default zero otherwise.
RankSpec retains the win premise for its zero iff mate. RankKey proves equal
keys imply equal least rank using exact budget congruence, and handles both
nonwinning defaults with the Win iff. No default-zero draw/mate claim.

Definitions.StrategyStep stores actual Legal, parent/child ForceMate and strict
rank decrease. StrategyLine is a nonempty list, singleton winning input or actual
adjacent policy edges. Progress inverts the minimal-rank certificate: strong node
has a descending choice; weak node has nonempty legal replies and EVERY legal
reply descends, including every potential intended move. No child-ongoing or
outcome filter. Captures to dead KK cannot satisfy the winning premise and are
not removed from Legal. Unchosen strong legal moves are intentionally unrestricted.

Line proves winning vertices and ALL-later rank decrease, yielding List.Pairwise
raw-key inequality over the FULL list and length≤rootRank+1. The proof generalises
the indexed list before induction, then recovers its head/tail equality; no
prefix is dropped. Terminal proves no policy edge iff named mate at a WINNING
node. No maximality or terminal conclusion is applied to a truncated line.
KRK combines EC-T0037 with minimality: root rank≤508 and every policy line has
pairwise distinct keys and ≤509 vertices (≤508 plies), both colours/all flags.
This is a new minimal-budget strategy, not a claim that the frozen geometric
policy or arbitrary raw play is key-simple. No optimal distance evaluation or
FIDE/Syzygy distance convention correspondence is asserted.

11 new modules, one main per module and shared definitions separate; all 9 public
declarations in AxiomCheck, full private/helper source retained. Earlier frozen
modules and records unchanged; aggregate/runner only extended. Authoring failures
were endpoint-equality orientation/explicit normalization unfolding, unavailable
by_contra tactic, indexed-list induction, explicit Colour.opp simplification;
new-module fixes preserve exact paper statements. Deprecation warnings replaced
with the core dite_eq_left/right lemmas. Full logs/commands/exits/times retained.

Observed Gate F and source hashes are authoritative in sessions/evidence/S070.
This audit is not itself a Gate F result. Actual stored-trace/incoming-history
counts and rule-layer lifting remain the next direct obligation: pairwise new
keys do not prevent a future key already occurring twice in incoming history.
508 exceeds100; full clock/FIDE outcomes, holding and exact distance remain open.
