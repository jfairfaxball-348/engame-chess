# EC-C037 — Lean fidelity review

S062, same-agent audit, not independent external review. Paper and separate
adversarial audit completed before Lean. Definitions and AppendLifting are NEW;
all frozen sources remain byte-identical. Admissible recurses on the actual
indexed Trace, with True at start and exact parent State at snoc.

Main append_and_reply_lifting states the exact requested conjunction. For EVERY
s/m/hm, destructing s makes the append guard definitional (Iff.rfl), preserving
all trace data. The second conjunct extracts actual m/hm from Legal and chooses
append; its admissibility uses the guard's reverse implication and its step and
endpoint witnesses are reflexive. There is no child classifier filter, material
or colour restriction, arbitrary history reconstruction or changed legality.

Terminal children lift, terminal parents cannot append; optional claims may be
declined. Relative raw classifier semantics only, no certified FIDE correspondence
or complete Layer/strategy/distance theorem. No enumeration/oracle/certificates,
full-game diagnostic or novelty claim. Gate F evidence pending.
