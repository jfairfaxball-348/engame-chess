# S035 — adversarial paper review for EC-C023

Same-agent review saved before Lean; not independent external review. Paper:
`proofs/EC-C023_RAW_TRACE_APPEND.md`. Scope is the raw move-data component,
not FIDE history adjudication. The exact local argument has no open gap.

| Attempted falsification | Resolution |
|---|---|
| Wrap Arisen in a structure and call it a history | Trace is an indexed Type with prior Trace and actual Move data, not just a Prop witness. It supports ordered moves/positions recursors. |
| Start from an arbitrary KRK board/flags | Only Trace.start at standard initial is available. No arbitrary root constructor or unproved prefix is assumed. |
| Append a different history to an equal erased board | RawBoardStep is actual append equality, not merely Legal between two endpoints. Entire prefix is retained. |
| Empty trace loses the initial endpoint | Empty moves=[], positions=[initial], endpoint=initial; root explicitly represented. |
| Skip or reorder a move | Append-spec equations preserve exact ordered prefix and add one singleton; move length increases by one. |
| Lose promotion/flags or mishandle black turn | Full Move and Position values retained; legality and play are the existing colour-generic kernel definitions. No material/turn case filter is added. |
| Wrong equality orientation in completeness | Legal supplies r=play; selected append erases to play, hence erase t=r. Paper explicitly substitutes the target equality. |
| Universal reply coverage only for friendly moves | The input is an arbitrary kernel Legal successor, with no outcome or strategy premise. Captures and future terminal-draw children are not excluded. |
| A child must remain ongoing | No such guard exists. Future terminal classification must not prune children; parent admissibility is a later obligation. |
| Kernel reachability means FIDE play never previously ended | Rejected. The support lemma uses frozen Arisen only. Raw traces may continue past rule draws whenever kernel Legal allows. |
| A/B alone instantiate the frozen abstract layer | Rejected. C, claims, terminal semantics and concrete admissibility are not proved here. |

Append validity is a typing fact of snoc with its legal-move proof; endpoint
and retention equations follow by unfolding; step soundness and complete lifting
use exactly the kernel Move witness, without a graph, enumeration or a winning
assumption. The origin support lemma is structural trace induction. No diagnostic
run or particular complete chess-game history is claimed by this audit.

Verdict: eligible for LOCAL_VERIFIED at Gate L for these exact statements;
formal verification and the published-source Gate F evidence remain pending.
