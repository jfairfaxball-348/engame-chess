# EC-C051 paper audit — S087

Separate same-agent adversarial pass; not external independent review.
Read the complete normalized statement and each move/reply witness before Lean.

* Domain checked: a is1 or2; b is1..6; S,R,W distinct and kings separated;
  exact strong-turn KRK with arbitrary flags, no invented initial history.
* First king move cannot approach W within one rank. R is protected before
  every weak turn. Weak castling is impossible because the weak side has no rook.
* Rook move is non-null, one square, and unblocked. Both rook-check and quiet
  children are included. Capture exclusion uses the NEW king/rook coordinates.
* ALL second replies split into right>=a+2 or left=a, not merely a favourable
  selected continuation. Rank b and file a+1 are attacked without an intervening
  strong king. Unit movement rules out jumping either ray.
* Nonemptiness is constructive at every weak node. All horizontal witnesses
  keep rank>b, hence distance>=2 from the supporting king. The smallest left
  interval has TWO files, the smallest shifted right interval FOUR. No 1x1
  witness or continuation after stalemate is used.
* Escape is paid for with TWO extra king/reply pairs. The new NW box includes
  files0..a; its width is a+1, not a. At a<=2 it is<=3, below old width>=5.
* Four/eight actual plies fit eight times the decrease in the large-side excess.
  The height does not change, and both endpoint kings are diagonally outside
  their actual weak quadrant. This closes this phase's cost/potential inequality.
* The width4 extension is invalid: its reflected eight-ply escort can return
  the same geometry after16 plies. The disclosed selected ray-model cycle and
  all six local phase trees passed; an independently written direct edge check
  also passed. These are diagnostics, not the universal proof or RAW histories.
* The geometric reflected/axis paper corollary requires pointwise StepM mapping
  and safe-reply completeness; full history/castling symmetry is not assumed.
  Formal statements must clearly distinguish normalized coverage from transport.
* Critical limitation: no arbitrary-entry theorem, <=4x4 mating finish, global
  sub100 certificate, all-history classification, FIDE bridge or exact WDL/DTZ.
  The <=32 bound ends at a guarded small box, NOT at mate.
* External primary paper was consulted for methodological context only. Its
  Isabelle theorem, strategy implementation and termination are not accepted
  as this project's proof, and no numerical game value is imported.

Verdict: normalized large-box phase is LOCAL_VERIFIED on paper. Its direct
geometric symmetry/large-side-excess corollary is paper-level only until the
corresponding actual Lean declarations and verification exist. EC-C050 stays
PROPOSED/open. No ledger change at this gate.
