# S030 sustained setup attempt — completed clock-free target

The active principal goal was arbitrary strong-turn legal-arrival KRK forcing,
not another local confinement result. It is now proved in `SafeSetup.lean`, with
weak-turn terminal/capture classification in `OutcomeClassification.lean`.

The setup proof required three genuine repairs beyond the S029 wall:

1. StepM symmetry alone was insufficient for alternating forcing. New
   `krk_force_transport` proves actual strategy transport, restricting source
   castling and covering all destination weak replies. Capture safety is derived
   from a dead-KK obstruction, not assumed at winning weak nodes.
2. A far retreat can reduce a two-rank king gap to one. `OffRankSetup` uses the
   resulting horizontal separation and proves a perpendicular safety margin;
   it does not retry a now-invalid original-axis entry.
3. Rook and strong king on the same rank obstruct the free horizontal retreat.
   Retreating the king solves positive ranks. On the back rank, a protected
   rank-one rook entry needs a witnessed reply to rule out stalemate. A close
   rook two files from the strong king needs a preparatory king alignment before
   that entry. Every legal reply stays high enough for it.

There is no recursive setup policy and no unproved continuation assumption.
At most a preparation/retreat pair and entry pair precede the S029 wall. The
wall's finite strategy then applies; no numerical optimal distance is claimed.

Preserved controls: the old chase cycle is already solved by S029; the old
checking-stalemate control still warns against empty universal reply sets. S029
Ka1/Rd4/Kc3 is now formally forcing BEFORE either naive move; after Rd2 or Rb4
there is an actual legal capture to KK and therefore no strong ForceMate.
Back-rank Ka1/Rc1/Kb3 and a black equal-rank/file-axis board with all rights and
an ep flag are fixed new formal controls. These are examples, not enumeration
or evidence replacing the symbolic proof.

EC-C011 can advance only once exact-source Gate F succeeds. The final
paper and same-agent audits record that the first attempted saved extension
append used the wrong working directory; the mathematics was developed before
source generation, and the subsequent retreat/completion paper/audit were saved
before their formalisation. No failed intermediate build is reported as passing.

The remaining KRK work is Gate Z and clock/repetition/distance semantics. No
full FIDE WDL, DTZ, seven-piece or initial-position claim follows. No theorem
ledger row changes in this session. See the S030 evidence and final closeout for
observed verification, rather than treating this development note as a certificate.

Final observation: exact-source Gate F passed at `4acc3e8638a916f329788d4c2b5f0db6f2c9bf67`; EC-C011 and C019–021 are FORMAL_VERIFIED. See the complete evidence.
