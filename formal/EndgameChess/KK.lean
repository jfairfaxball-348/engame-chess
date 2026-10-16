/-!
# EC-C001 — King versus king is a dead position (Lean 4 formalisation)

Faithful formalisation of `proofs/EC-C001_KK.md` (S001, Gate L) and the two-king
layer of `docs/FOUNDATIONS.md`. Core Lean only (no mathlib).

Lean checks the *mathematical model*. The bridge from FIDE 2023 Laws of Chess
(Articles 1.2, 1.4.1, 3.1–3.9, 5.2.2; https://handbook.fide.com/chapter/E012023)
to these definitions is the prose argument of the local proof (assumption A1 and
lemma L3a). Lean does not verify FIDE's normative text.

Board convention: a square is `(file, rank)` with `(0,0)` = a1 and `(7,7)` = h8.
-/

namespace EndgameChess.KK

/-- A square of the 8×8 board: `(file, rank)`, both in `0…7`. -/
abbrev Square := Fin 8 × Fin 8

/-- `|a − b|` on natural numbers, via truncated subtraction. -/
def absDiff (a b : Nat) : Nat := (a - b) + (b - a)

/-- Chebyshev distance `d∞`. -/
def dInf (s q : Square) : Nat :=
  max (absDiff s.1.val q.1.val) (absDiff s.2.val q.2.val)

/-- FIDE 3.8.1 "adjoining square" under assumption A1: a different on-board square
whose file and rank each differ by at most one. Stated by coordinates, *not* via
`dInf`, so that `attack_iff_dInf_one` (L1) is a genuine equivalence. -/
def Adjoining (s q : Square) : Prop :=
  s ≠ q ∧ s.1.val ≤ q.1.val + 1 ∧ q.1.val ≤ s.1.val + 1 ∧
    s.2.val ≤ q.2.val + 1 ∧ q.2.val ≤ s.2.val + 1

/-- FIDE 3.1.2–3.1.3: a king on `s` attacks `q` iff it could capture on `q` by an
Article 3.8 move, ignoring self-check. Castling (3.8.2) never captures, so these
are exactly the adjoining squares. -/
def kingAttacks (s q : Square) : Prop := Adjoining s q

inductive Colour
  | white
  | black
  deriving DecidableEq, Repr

/-- The opposite colour `c̄`. -/
def Colour.opp : Colour → Colour
  | .white => .black
  | .black => .white

/-- A KK configuration `(w, b, t)`: White king, Black king, side to move.
No other pieces exist. (Configurations with `wk = bk` are representable but are
never admissible; every theorem below is about admissible or reached states.) -/
structure KKState where
  wk : Square
  bk : Square
  turn : Colour
  deriving DecidableEq, Repr

/-- `K_c(p)`: the square of the colour-`c` king. -/
def KKState.king (p : KKState) : Colour → Square
  | .white => p.wk
  | .black => p.bk

/-- FIDE 3.9.1: the colour-`c` king is attacked by an opposing piece. In a KK
configuration the only opposing piece is the other king. -/
def inCheck (p : KKState) (c : Colour) : Prop :=
  kingAttacks (p.king c.opp) (p.king c)

/-- `Admissible(p) :⇔ d∞(w,b) ≥ 2`. -/
def Admissible (p : KKState) : Prop := 2 ≤ dInf p.wk p.bk

/-- The side to move puts its king on `s`; the other king stays; the turn flips
(FIDE 1.2). -/
def KKState.moveKing (p : KKState) (s : Square) : KKState :=
  match p.turn with
  | .white => { wk := s, bk := p.bk, turn := .black }
  | .black => { wk := p.wk, bk := s, turn := .white }

/-- `LegalKK p q`: the FIDE-legal moves of a KK configuration, stated as the rule
conditions of lemma L3a: (i) the mover's king goes to an adjoining square (3.8.1),
(ii) not onto the opposing king (1.4.1: no king capture), and the move leaves the
mover's king not in check (3.9.2). Lemma `legalKK_iff_prose` shows this is exactly
conditions (i)–(iii) of the local proof. -/
def LegalKK (p q : KKState) : Prop :=
  ∃ s, Adjoining (p.king p.turn) s ∧ s ≠ p.king p.turn.opp ∧
    q = p.moveKing s ∧ ¬ inCheck q p.turn

/-- Checkmate of colour `c`: `c` is to move, in check, and has no legal move. -/
def Checkmate (c : Colour) (p : KKState) : Prop :=
  p.turn = c ∧ inCheck p c ∧ ¬ ∃ q, LegalKK p q

/-- Finite series of legal moves, length `n ≥ 0` (reflexive–transitive closure of
`LegalKK`). No stopping rule is applied: the counterfactual move graph. -/
inductive Reach : KKState → KKState → Prop
  | refl (p : KKState) : Reach p p
  | tail {p q r : KKState} : Reach p q → LegalKK q r → Reach p r

/-- FIDE 5.2.2 (mathematical predicate): no finite series of legal moves from `p`
ends in a checkmate of either colour. -/
def Dead (p : KKState) : Prop :=
  ¬ ∃ q, Reach p q ∧ (Checkmate .white q ∨ Checkmate .black q)

/-! ## Arithmetic of the board -/

theorem square_eq_iff {s q : Square} :
    s = q ↔ s.1.val = q.1.val ∧ s.2.val = q.2.val := by
  constructor
  · intro h; subst h; exact ⟨rfl, rfl⟩
  · intro ⟨h1, h2⟩
    exact Prod.ext (Fin.ext h1) (Fin.ext h2)

theorem dInf_comm (s q : Square) : dInf s q = dInf q s := by
  simp only [dInf, absDiff]; omega

theorem dInf_eq_zero_iff {s q : Square} : dInf s q = 0 ↔ s = q := by
  rw [square_eq_iff]; simp only [dInf, absDiff]; omega

/-- **L1.** King attack is Chebyshev adjacency. -/
theorem attack_iff_dInf_one (s q : Square) : kingAttacks s q ↔ dInf s q = 1 := by
  simp only [kingAttacks, Adjoining, Ne, square_eq_iff, dInf, absDiff]
  omega

theorem king_opp_white (p : KKState) : p.king Colour.white.opp = p.bk := rfl
theorem king_opp_black (p : KKState) : p.king Colour.black.opp = p.wk := rfl

/-- **L2′.** In any KK configuration, either king is in check iff `d∞(w,b) = 1`. -/
theorem inCheck_iff (p : KKState) (c : Colour) : inCheck p c ↔ dInf p.wk p.bk = 1 := by
  cases c
  · simp only [inCheck, KKState.king, Colour.opp]
    rw [attack_iff_dInf_one, dInf_comm]
  · simp only [inCheck, KKState.king, Colour.opp]
    rw [attack_iff_dInf_one]

/-- **L2.** No check in an admissible configuration. -/
theorem not_inCheck_of_admissible {p : KKState} (h : Admissible p) (c : Colour) :
    ¬ inCheck p c := by
  rw [inCheck_iff]; unfold Admissible at h; omega

theorem moveKing_turn (p : KKState) (s : Square) :
    (p.moveKing s).turn = p.turn.opp := by
  unfold KKState.moveKing; cases p.turn <;> rfl

/-- After a move, the mover's king is on `s` and the other king is where it was. -/
theorem moveKing_kings (p : KKState) (s : Square) :
    (p.moveKing s).king p.turn = s ∧ (p.moveKing s).king p.turn.opp = p.king p.turn.opp := by
  unfold KKState.moveKing; cases p.turn <;> exact ⟨rfl, rfl⟩

/-- Distance between the kings of `p`, read from colour `c`'s side. -/
theorem dInf_king (p : KKState) (c : Colour) :
    dInf (p.king c) (p.king c.opp) = dInf p.wk p.bk := by
  cases c
  · rfl
  · exact dInf_comm _ _

/-- `LegalKK` is exactly conditions (i)–(iii) of the local proof. -/
theorem legalKK_iff_prose (p q : KKState) :
    LegalKK p q ↔ ∃ s, dInf (p.king p.turn) s = 1 ∧ s ≠ p.king p.turn.opp ∧
      2 ≤ dInf s (p.king p.turn.opp) ∧ q = p.moveKing s := by
  constructor
  · rintro ⟨s, hadj, hne, rfl, hchk⟩
    refine ⟨s, (attack_iff_dInf_one _ _).1 hadj, hne, ?_, rfl⟩
    have hk := moveKing_kings p s
    have h1 : dInf s (p.king p.turn.opp) ≠ 1 := by
      intro h1; apply hchk
      unfold inCheck; rw [hk.1, hk.2, attack_iff_dInf_one, dInf_comm]; exact h1
    have h0 : dInf s (p.king p.turn.opp) ≠ 0 := fun h0 => hne (dInf_eq_zero_iff.1 h0)
    omega
  · rintro ⟨s, h1, hne, h2, rfl⟩
    refine ⟨s, (attack_iff_dInf_one _ _).2 h1, hne, rfl, ?_⟩
    have hk := moveKing_kings p s
    unfold inCheck; rw [hk.1, hk.2, attack_iff_dInf_one, dInf_comm]; omega

/-- **L3.** One-step closure. Note: no admissibility of the source is needed. -/
theorem admissible_of_legal_step {p q : KKState} (h : LegalKK p q) : Admissible q := by
  obtain ⟨s, _, _, h2, rfl⟩ := (legalKK_iff_prose p q).1 h
  have hk := moveKing_kings p s
  unfold Admissible
  rw [← dInf_king (p.moveKing s) p.turn, hk.1, hk.2]
  exact h2

/-- **L0 (core).** Any configuration produced by a legal KK move is admissible. -/
theorem admissible_of_last_move_legal (q : KKState) (h : ∃ p, LegalKK p q) :
    Admissible q := by
  obtain ⟨p, hp⟩ := h
  exact admissible_of_legal_step hp

/-- **L3 (turn).** A legal move flips the side to move. -/
theorem turn_of_legal_step {p q : KKState} (h : LegalKK p q) : q.turn = p.turn.opp := by
  obtain ⟨s, _, _, rfl, _⟩ := h
  exact moveKing_turn p s

/-- **L4.** Finite-path closure, by induction on `Reach` (length zero included). -/
theorem admissible_of_reach {p q : KKState} (hp : Admissible p) (h : Reach p q) :
    Admissible q := by
  induction h with
  | refl => exact hp
  | tail _ hstep _ => exact admissible_of_legal_step hstep

/-- **L5.** No reachable checkmate of either colour. -/
theorem not_checkmate_of_reach {p q : KKState} (hp : Admissible p) (h : Reach p q)
    (c : Colour) : ¬ Checkmate c q := by
  rintro ⟨_, hchk, _⟩
  exact not_inCheck_of_admissible (admissible_of_reach hp h) c hchk

/-- **L6 / Theorem EC-C001.** Every admissible KK configuration is dead. -/
theorem dead_of_admissible {p : KKState} (hp : Admissible p) : Dead p := by
  rintro ⟨q, hr, hm | hm⟩
  · exact not_checkmate_of_reach hp hr .white hm
  · exact not_checkmate_of_reach hp hr .black hm

/-- **Theorem EC-C001, arisen form.** A configuration produced by a legal KK move
is dead. -/
theorem dead_of_last_move_legal (q : KKState) (h : ∃ p, LegalKK p q) : Dead q :=
  dead_of_admissible (admissible_of_last_move_legal q h)

/-! ## Remark R1 and non-vacuity checks -/

/-- **R1.** Every admissible configuration has a legal move (so no stalemate). -/
theorem exists_legal_move_of_admissible {p : KKState} (hp : Admissible p) :
    ∃ q, LegalKK p q := by
  have hd : 2 ≤ dInf (p.king p.turn) (p.king p.turn.opp) := by
    rw [dInf_king]; exact hp
  generalize hm : p.king p.turn = m at hd
  generalize ho : p.king p.turn.opp = o at hd
  have key : ∃ s : Square, dInf m s = 1 ∧ 2 ≤ dInf s o := by
    simp only [dInf, absDiff] at hd
    by_cases hx : 2 ≤ (m.1.val - o.1.val) + (o.1.val - m.1.val)
    · -- vary the rank, keep the file
      have hy := m.2.isLt
      by_cases hy0 : m.2.val = 0
      · refine ⟨(m.1, ⟨1, by omega⟩), ?_, ?_⟩ <;> simp only [dInf, absDiff] <;> omega
      · refine ⟨(m.1, ⟨m.2.val - 1, by omega⟩), ?_, ?_⟩ <;> simp only [dInf, absDiff] <;> omega
    · have hx' := m.1.isLt
      by_cases hx0 : m.1.val = 0
      · refine ⟨(⟨1, by omega⟩, m.2), ?_, ?_⟩ <;> simp only [dInf, absDiff] <;> omega
      · refine ⟨(⟨m.1.val - 1, by omega⟩, m.2), ?_, ?_⟩ <;> simp only [dInf, absDiff] <;> omega
  obtain ⟨s, h1, h2⟩ := key
  have hne : s ≠ o := by
    intro h; subst h; rw [(dInf_eq_zero_iff).2 rfl] at h2; omega
  refine ⟨p.moveKing s, (legalKK_iff_prose p _).2 ⟨s, ?_, ?_, ?_, rfl⟩⟩
  · rw [hm]; exact h1
  · rw [ho]; exact hne
  · rw [ho]; exact h2

/-- Squares used in the examples. -/
def a1 : Square := (0, 0)
def a2 : Square := (0, 1)
def b1 : Square := (1, 0)
def b2 : Square := (1, 1)
def c3 : Square := (2, 2)

/-- Non-vacuity: `Checkmate` is satisfiable. White Ka1, Black Kb2 (an
*inadmissible*, adjacent placement), White to move: White is in check and has no
legal move. Hence `Dead` is not true merely because `Checkmate` is empty. -/
theorem checkmate_satisfiable :
    Checkmate .white { wk := a1, bk := b2, turn := .white } := by
  refine ⟨rfl, ?_, ?_⟩
  · rw [inCheck_iff]; decide
  · rintro ⟨q, hq⟩
    obtain ⟨s, h1, hne, h2, _⟩ := (legalKK_iff_prose _ q).1 hq
    simp only [KKState.king, Colour.opp, a1, b2] at h1 hne h2
    rw [Ne, square_eq_iff] at hne
    simp only [dInf, absDiff] at h1 h2
    revert h1 h2 hne
    obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := s
    simp only [Fin.val_zero, Fin.val_one]
    omega

/-- Non-vacuity: `Reach` contains non-trivial paths, e.g. Ka1/Kc3 → Ka2/Kc3. -/
theorem reach_nontrivial :
    Reach { wk := a1, bk := c3, turn := .white } { wk := a2, bk := c3, turn := .black } := by
  refine Reach.tail (Reach.refl _) ((legalKK_iff_prose _ _).2 ⟨a2, ?_, ?_, ?_, rfl⟩) <;> decide

end EndgameChess.KK
