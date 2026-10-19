# S030 same-agent Lean fidelity audit

The final paper is `proofs/EC-C019_C021_KRK_SAFE_SETUP.md`. Development paper and
pre-formalisation adversarial notes are retained separately. This is a same-agent
review, not an external independent audit. No general claim relies on examples.

| Obligation | Module | Fidelity check |
|---|---|---|
| Actual unprotected capture, necessary weak safety | CaptureSafety | Legal ordinary king capture; exact KK board; legal-arrival KK deadness; no live⇒forcing substitution |
| Strong move completeness | OrdinaryMoves | Source noRights explicit; own targets and king captures excluded; exact board after play; post-check separation |
| Alternating transport | StrategyTransport | Induction on source MateWithin; all target weak replies project back; nonempty witnesses; actual terminal mate; no deadness symmetry assumption |
| Coordinate coverage | AxisWalls | Swap and anti-reflection are BoardSym; rank/file orientation chosen from distance≥2; actual arrival geometry |
| Extended direct entry | ClearEntry | Source king outside ray or distinct file; safety before weak turn; witnessed legal reply; every reply enters wall |
| Far retreat/axis switch | OffRankSetup | Source rank outside king interval; far file margin4, after reply≥3; lost vertical gap switches to perpendicular entry |
| Same-rank/back-rank | SameRankSetup | Actual king retreat, protected rook entry, preparatory alignment; explicit replies avoid stalemate; no recursive setup call |
| Full strong target | SafeSetup | No-check geometric result then legal-arrival extraction; named colour and arbitrary flags preserved; canonical source needs no predecessor |
| Weak target | OutcomeClassification | Zero-ply mate, no-reply inversion, ANY capture obstruction; all noncapture replies reduce to flagship; finite branching |
| Fixed controls | SetupExamples | Back-rank preparation; black equal-rank/file-axis case with all rights/ep flags; old naive capture setup wins before and fails after both unsafe moves |

All frozen sources and all S028/S029 anchored modules are imported unchanged.
The main strong theorem has exactly IsKRK, strong turn and existence of an
incoming Legal move; the stronger intermediate uses weak no-check instead.
The weak theorem needs only exact material and weak turn. It does not assume
all replies win: it proves that from the no-capture condition using the strong
theorem. The safety form is an alternative interface, not a new game semantics.

No forbidden proof escapes, enumerated oracle, tablebase, native reduction or
extra axiom is permitted. Full public axiom/statement checks and fresh exact-
source build evidence will be attached after the published-source run. Gate Z
and human kernel-encoding review remain separate. Hosted CI is unobserved unless
explicitly recorded.
