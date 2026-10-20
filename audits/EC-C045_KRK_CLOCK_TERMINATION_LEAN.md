# EC-C045 — Lean fidelity audit (S076)

Separate same-agent fidelity/adversarial pass, not external review. Standalone
paper and its separate paper audit preceded Lean. Reviewed every new source in
`formal/EndgameChess/Rules/KRKTermination/`, all ten statements in AxiomCheck,
and their actual frozen dependencies. No frozen source or record changed.

- Targets derives no pawn and the sole capturable rook directly from krkBoard
  and targetOK. Castle symbolically splits the two canCastle schemas, identifies
  the unique home rook and empty king/crossed-rook destinations, and proves the
  entire actual play board equal to KRK. Weak king remains universally quantified.
- Strong includes ordinary king/rook and actual castle, with no noRights premise.
  Closure quantifies the actual legal Move, both turns/colours and all flags.
  Strong target is empty; surviving weak branch retains the old rook square,
  so an occupied destination contradicts the actual arriving king. The other
  branch is actual dead KK via the frozen legal-into-KK theorem. No pawn/EP reset
  or unchosen strong move is discarded.
- State/BoardStep are the existing initial-rooted admitted RAW subtype and its
  exact append relation. Guard uses CHILD admission and exact append iff to
  force parent ongoing. Terminal-parent raw moves cannot become typed steps.
- Region includes exact KRK OR terminal; fuel is zero for every terminal. Step
  uses exact append_clock with the same actual Move. Ongoing children increment
  the clock; terminal reset children spend fuel by parent clock<150. No claim
  that a clock150 mate is a draw, or that a bad strong move remains live.
- Path is forward typed cons/refl. PathBound proves end-region plus end-fuel+n
  for every path. ClockCap gives ≤150−h for ongoing exact KRK roots and length0
  for terminal roots. Maximal iff terminal holds on all admitted states through
  full legal-reply lifting, including ending children. TerminalExists uses strong
  natural induction on fuel, actual nonempty replies and strict decrease; no
  outcome oracle or per-position/class enumeration.
- This proves universal RAW board-play termination only. Claims can stop earlier;
  no claim strategy/terminal outcome classification, full FIDE correspondence,
  all-history holding, exact WDL or DTZ theorem is inferred. No failed sufficient
  histogram is treated as a draw.

Working full incremental library build and COMPLETE 354-report AxiomCheck passed,
standard three only. Ten theorem modules plus shared definitions; all ten main
statements audited, no sorry/admit/axiom/unsafe/native_decide/custom primitives.
Fresh exact published-source Gate F is required before FORMAL_VERIFIED; separate
Gate Z still pending. See session evidence for actual results and retained failures.
