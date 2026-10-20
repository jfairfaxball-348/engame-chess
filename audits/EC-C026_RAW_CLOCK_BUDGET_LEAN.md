# S040 — Lean fidelity review for EC-C026

Same-agent review, not independent external review. Paper and adversarial
review saved BEFORE Lean. Official core Lean4.35.0, no new dependency.

One new theorem module RawClock/BudgetCertificate imports frozen ExtensionBound.
The statement has explicit root budget clock(s)+n<100, arbitrary k,u, k≤n,
and actual full-state Extends k s u. Its first conjunct bounds the current
prefix. Its second requires k<n and quantifies over EVERY actual RawBoardStep
u v, without strategy/material/side/terminal filters. The prospective child is
not asserted to be executed in a claim action. No other definitions or redundant
prefix/length/arithmetic lemmas added. Aggregate import and AxiomCheck additive.

Proof: frozen clock_le_extension and addition monotonicity give the first
bound. Extends.snoc path step gives the exact prospective k+1 extension; strict
interior inequality gives k+1≤n. Frozen growth, monotonicity and transitivity
finish. Both reset and quiet edges already fall under frozen growth. Complete
traces retained. No endpoint-clock hypothesis or erased-board shortcut.

Incremental lake build passed first attempt, 69 jobs; complete AxiomCheck exit 0.
Exact statement inspected: main uses [propext, Classical.choice, Quot.sound].
No finite diagnostic or fixed full promotion/ep/castling/threshold game was run.
No FIDE claim predicate, repetition control, sufficient-budget lifting or numeric
KRK bound follows. Gate F pending until published exact-source fresh verification.
