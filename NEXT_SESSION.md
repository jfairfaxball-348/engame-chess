# NEXT SESSION — S076: Universal RAW KRK clock-bounded termination

Owner requests consecutive sessions until asked to stop. KRK only; stop before
KQK. Follow AGENTS/charter/protocol, ALL-head fetch/merge prior unmerged work,
latest main in existing checkout; commit/push branch, merge/push main, compare
remote identities. Stable full progress table, Syzygy last and immediate delta.

Starting evidence: 41 frozen bundles, not solved classes. EC-T0040: credited
wall 73*(7−rookRank), pursuit 8*m−6+E/uniform 50+E, same-budget frames and conditional
73-ply RAW frame-wall family clock≤26 with original current/incoming conditions.
EC-T0041: actual KRK WallBudget(B)→B+4/B+5, proved 438 wall instantiation, global 442
strong legal arrivals and 443 weak FORCING inputs, both colours/all flags/all weak
replies. OWN sources: C043 f462629793680fc0b9cb21ce5e9fb15393722c93;
C044 7179a31d2a6fcb166c20e850e394b8cf15336031. Read actual S073–S075 evidence,
complete sources/papers/audits and roadmap. C039 remains backlog. Full FIDE
correspondence, complete all-history outcomes/holding and exact distances open.

Principal direct step toward outcome/holding: prove universal clock-bounded
termination for ACTUAL admitted RAW histories from exact KRK, both turns, either
strong colour, arbitrary kernel flags, EVERY legal board move including unchosen
strong moves. This is not the chosen rank strategy or all-raw-past-terminal play.
No complete classification/optimal distance claim from a termination lemma.

Target exact invariant: an actual legal step from exact KRK either retains exact
KRK and is nonzeroing, or is a weak king's rook capture giving dead KK and a
terminal raw child. In particular every ONGOING child stays KRK and its stored
halfmove clock is exactly parent's+1. No pawns/promotions or nonterminal zeroing
branch may be assumed away; derive them from the exact material and legality.
STRONG-SIDE CASTLING MUST BE INCLUDED. Existing krk_strong_reply assumes noRights
and is insufficient for arbitrary raw/admitted flags. Actual KRK histories can
retain castling rights: do not silently exclude them.

Read actual play/isPseudo/canCastle, targetOK, own_of_isPseudo, krkBoard_some,
play_board_simple, frozen strong ordinary completeness and lone_move_cases,
RawClock zeroing/legal_zero_iff/append/step-bound/castle_empty, dead-KK arrival,
RawAdjudication.ongoing_iff and stopped-history append iff. A useful all-flag
strong lemma can return exact KRK material after play (no need to force a castle
into the ordinary StepM relation) plus quiet-clock fact. Ordinary king/rook
branches reuse existing geometry; actual castling moves the sole rook from its
required home square to the crossed square and preserves the lone king. Derive
empty destination/crossing squares and distinct endpoints from canCastle, no
board enumeration or assumed material-count oracle. Legal target cannot be an
own piece or the enemy king. Weak legal rook capture is the only capture/reset,
and its KK child is dead by the frozen kernel theorem, regardless of flags.

Use existing RawHistoryLayer.State with actual initial-rooted trace/admission.
Any BoardStep s t between typed admitted states forces parent Ongoing via child
admission and exact append iff. Thus no typed path continues after mate/dead/
stalemate/automatic draw. RawTrace.Extends alone permits continuation past such
terminals: DO NOT substitute it without the needed admitted-state guards.
Define a typed finite path and region (exact KRK OR terminal). Exact potential
P(s)=if Ongoing s then 150−clock(s.trace) else 0. Prove EVERY actual typed step from
that region preserves region and strictly decreases P, with P(child)+1≤P(parent).
At ongoing KRK parent clock<150; ongoing child increments clock 1; terminal child
has potential 0 even if a rook capture reset it. At terminal parent no typed step.
Then derive P(endpoint)+length≤P(root), hence at most 150−h board plies from an
ongoing KRK root of clock h and 0 from a terminal root. Nonempty ongoing replies
mean a MAXIMAL path ends terminal; truncated finite prefixes need not be terminal.
Claims consume no board ply and can only stop earlier; do not invent claim passes.
Handle root mate/clock≥150/mate-first precedence and all counts/flags honestly.

Four-part prerequisite admission if needed: exact blocked KRK all-branch clock/
material step; why frozen noRights interface/clock≤old+1 do not discharge it;
smallest all-flag material/quiet/capture-to-terminal statement; exit directly to
this typed potential/termination proof. No generic prerequisite series. A blocked
castling or history case is recorded precisely and carried forward; do not
replace it with an unrelated easier theorem or silently restrict flags.

Standalone exact paper and separate SAME-AGENT adversarial audit BEFORE Lean.
Only select new candidate after exact claim fixed. Audit both turns/colours,
king/rook ordinary/castle branches, zeroing/KK terminal, actual move/append/full
history, parent/child admissibility, n0 and root-terminal, no vacuous nonempty,
clock 149/150 and reset 0 terminal, prospective/actual endpoints and every move.
No tablebase/engine/class enumeration/per-position certificates/novelty claim.

If proof closes: new one-main-per-module Lean/shared definitions, all mains/
helpers AxiomCheck, appropriate incremental/importer build/full runner, own
published FULL source SHA then ONE NEW GitHub clone/.lake absent/full build/
complete runner. Standard-three only; full logs/commands/exits/times/UTC,
source/import/executable hashes, clean identity and working/clean equality.
Official core Lean4.35.0, ELAN_HOME=/workspace/.tools/elan, inherited proxy/CA;
no dependency/shim/TLS/checksum changes. No promotion before observed success;
Gate Z separate. Preserve failures and every frozen module/record.

Update candidate/roadmap/README/completion/progress/session ledger and
sessions/S076_KRK_CLOCK_TERMINATION.md with actual evidence, full-domain or exact
unchanged/blocked coverage and FULL next prompt. Commit/push/merge/push, compare
remotes, continue until asked to stop. After this direct termination step, a
genuine all-history RAW holding/outcome proof still needs every legal/claim
branch and terminal semantics; merely renaming RuleMateWithin or failing the
sufficient histogram is NOT a draw classification. Full FIDE key/rights/claim/
adjudication correspondence and exact WDL/DTZ remain separate. No KQK.
