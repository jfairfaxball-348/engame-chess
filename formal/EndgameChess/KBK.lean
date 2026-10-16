import EndgameChess.KK

/-!
# EC-C002 — King and bishop versus king is a dead position (Lean 4)

Faithful formalisation of `proofs/EC-C002_KBK.md` (S004, Gate L). Core Lean only.
Imports the frozen EC-T0001 module `EndgameChess.KK` and does not modify it.

Lean checks the mathematical model. The bridge from FIDE 2023 (Articles 1.2,
1.4.1, 3.1–3.2, 3.5, 3.8–3.10, 5.2.2; https://handbook.fide.com/chapter/E012023)
to these definitions is the prose of the local proof.

The strong side (king + bishop) has colour `strongColour`; the weak side has a
lone king. Colour names play no role except when a captured-bishop position is
embedded into `KKState`.
-/

namespace EndgameChess.KBK

open EndgameChess.KK

inductive Side
  | strong
  | weak
  deriving DecidableEq, Repr

def Side.opp : Side → Side
  | .strong => .weak
  | .weak => .strong

/-- A K+B vs K configuration: strong king `sk`, bishop `bs`, weak king `wk`. -/
structure KBKState where
  strongColour : Colour
  sk : Square
  bs : Square
  wk : Square
  turn : Side
  deriving DecidableEq, Repr

/-! ## Bishop geometry (FIDE 3.2, 3.5) -/

/-- `q` lies on a diagonal through `X` (and differs from `X`). -/
def onDiag (X q : Square) : Prop :=
  X ≠ q ∧ absDiff X.1.val q.1.val = absDiff X.2.val q.2.val

/-- `r` lies strictly between `X` and `q` on a common diagonal. (S005 cross-checked
this arithmetic form against square-by-square ray walking for every triple: no
mismatch; see `audits/EC-C002_KBK_LEAN.md`.) -/
def between (X r q : Square) : Prop :=
  onDiag X r ∧ onDiag r q ∧ dInf X r + dInf r q = dInf X q

/-- 3.1.2 + 3.2 + 3.5: a bishop on `X` attacks `q` iff `q` is on a diagonal of `X`
and no occupied square lies strictly between them. -/
def bishopAttacks (occ : Square → Prop) (X q : Square) : Prop :=
  onDiag X q ∧ ∀ r, between X r q → ¬ occ r

/-- Occupancy by the two kings (the only possible blockers of the bishop). -/
def kingsOcc (a b : Square) : Square → Prop := fun r => r = a ∨ r = b

/-- 3.9.1 for the weak king: attacked by the strong king or by the bishop. -/
def weakInCheck (p : KBKState) : Prop :=
  kingAttacks p.sk p.wk ∨ bishopAttacks (kingsOcc p.sk p.wk) p.bs p.wk

/-- 3.9.1 for the strong king: only the weak king can attack it. -/
def strongInCheck (p : KBKState) : Prop :=
  kingAttacks p.wk p.sk

def KBKState.inCheck (p : KBKState) : Side → Prop
  | .strong => strongInCheck p
  | .weak => weakInCheck p

/-- Locally legal configuration: distinct squares, and the side not to move is not in
check (3.9.2 applied to the move that produced it). -/
def LKBK (p : KBKState) : Prop :=
  p.sk ≠ p.bs ∧ p.sk ≠ p.wk ∧ p.bs ≠ p.wk ∧ ¬ p.inCheck p.turn.opp

/-- Embedding of a two-king position, with the strong king in its own colour's slot. -/
def toKK (c : Colour) (sk wk : Square) (turn : Colour) : KKState :=
  match c with
  | .white => { wk := sk, bk := wk, turn := turn }
  | .black => { wk := wk, bk := sk, turn := turn }

/-- Positions of the material class: K+B vs K, or (after the bishop is captured) K vs K. -/
inductive Pos
  | kbk (p : KBKState)
  | kk (a : KKState)

/-- The FIDE-legal moves (3.1–3.9, 1.4.1), one constructor per kind of move. In each
case the mover's king must not be in check in the resulting position (3.9.2). -/
inductive Step : Pos → Pos → Prop
  /-- Strong king to an adjoining square, not onto its own bishop or the enemy king. -/
  | strongKing {p : KBKState} {s : Square} :
      p.turn = .strong → Adjoining p.sk s → s ≠ p.bs → s ≠ p.wk →
      ¬ strongInCheck { p with sk := s, turn := .weak } →
      Step (.kbk p) (.kbk { p with sk := s, turn := .weak })
  /-- Bishop along an unobstructed diagonal, not onto its own king or the enemy king. -/
  | bishop {p : KBKState} {s : Square} :
      p.turn = .strong → bishopAttacks (kingsOcc p.sk p.wk) p.bs s → s ≠ p.sk → s ≠ p.wk →
      ¬ strongInCheck { p with bs := s, turn := .weak } →
      Step (.kbk p) (.kbk { p with bs := s, turn := .weak })
  /-- Weak king to an adjoining empty square. -/
  | weakKing {p : KBKState} {s : Square} :
      p.turn = .weak → Adjoining p.wk s → s ≠ p.sk → s ≠ p.bs →
      ¬ weakInCheck { p with wk := s, turn := .strong } →
      Step (.kbk p) (.kbk { p with wk := s, turn := .strong })
  /-- Weak king captures the bishop (3.1.1); only the strong king can then attack it.
  The result is K vs K with the strong side to move. -/
  | weakCaptures {p : KBKState} :
      p.turn = .weak → Adjoining p.wk p.bs → ¬ kingAttacks p.sk p.bs →
      Step (.kbk p) (.kk (toKK p.strongColour p.sk p.bs p.strongColour))
  /-- K vs K moves (EC-T0001's `LegalKK`). -/
  | kk {a b : KKState} : LegalKK a b → Step (.kk a) (.kk b)

/-- Checkmate of the side to move. -/
def Mated : Pos → Prop
  | .kbk p => p.inCheck p.turn ∧ ¬ ∃ q, Step (.kbk p) q
  | .kk a => Checkmate .white a ∨ Checkmate .black a

/-- Finite series of legal moves, length `n ≥ 0`, with no stopping rule. -/
inductive Reach : Pos → Pos → Prop
  | refl (p : Pos) : Reach p p
  | tail {p q r : Pos} : Reach p q → Step q r → Reach p r

/-- FIDE 5.2.2 (mathematical predicate): no series of legal moves reaches a checkmate. -/
def Dead (p : Pos) : Prop :=
  ¬ ∃ q, Reach p q ∧ Mated q

/-- The class `LKBK ∪ AdmKK` that is closed under legal moves. -/
def Closed : Pos → Prop
  | .kbk p => LKBK p
  | .kk a => Admissible a

/-! ## B1: colour complex -/

/-- Square colour (Art. 2.1): parity of file + rank. -/
def col (s : Square) : Nat := (s.1.val + s.2.val) % 2

/-- **B1a.** A bishop attacks only squares of its own colour, for every occupancy. -/
theorem colour_of_bishopAttacks {occ : Square → Prop} {X q : Square}
    (h : bishopAttacks occ X q) : col q = col X := by
  obtain ⟨⟨_, hd⟩, _⟩ := h
  simp only [col]; simp only [absDiff] at hd; omega

/-- **B1b.** Orthogonal neighbours have opposite colours. -/
theorem colour_orth_neighbour {s q : Square}
    (h : (s.2.val = q.2.val ∧ absDiff s.1.val q.1.val = 1) ∨
         (s.1.val = q.1.val ∧ absDiff s.2.val q.2.val = 1)) : col s ≠ col q := by
  simp only [col]; simp only [absDiff] at h; omega

/-! ## B0′: kings apart, strong side never in check -/

theorem dInf_ne_zero_of_ne {s q : Square} (h : s ≠ q) : dInf s q ≠ 0 :=
  fun h0 => h (dInf_eq_zero_iff.1 h0)

/-- **B0′.** In a locally legal configuration the kings are at distance ≥ 2. -/
theorem kings_apart_of_LKBK {p : KBKState} (h : LKBK p) : 2 ≤ dInf p.sk p.wk := by
  obtain ⟨_, hne, _, hchk⟩ := h
  have h0 := dInf_ne_zero_of_ne hne
  have h1 : dInf p.sk p.wk ≠ 1 := by
    intro h1
    apply hchk
    cases ht : p.turn
    · simp only [Side.opp, KBKState.inCheck, weakInCheck]
      exact Or.inl ((attack_iff_dInf_one _ _).2 h1)
    · simp only [Side.opp, KBKState.inCheck, strongInCheck]
      rw [attack_iff_dInf_one, dInf_comm]; exact h1
  omega

/-- **B0′.** The strong king is never in check in a locally legal configuration. -/
theorem strong_not_inCheck_of_LKBK {p : KBKState} (h : LKBK p) : ¬ strongInCheck p := by
  have := kings_apart_of_LKBK h
  unfold strongInCheck; rw [attack_iff_dInf_one, dInf_comm]; omega

/-! ## B2: the lone king always escapes a check -/

/-- Orthogonal neighbours of `k` in both directions always exist on the board. -/
theorem exists_orth_neighbours (k : Square) :
    ∃ h v : Square, (h.2.val = k.2.val ∧ absDiff h.1.val k.1.val = 1) ∧
      (v.1.val = k.1.val ∧ absDiff v.2.val k.2.val = 1) := by
  have hx := k.1.isLt
  have hy := k.2.isLt
  have hh : ∃ h : Square, h.2.val = k.2.val ∧ absDiff h.1.val k.1.val = 1 := by
    by_cases h0 : k.1.val = 0
    · exact ⟨(⟨1, by omega⟩, k.2), rfl, by simp only [absDiff]; omega⟩
    · exact ⟨(⟨k.1.val - 1, by omega⟩, k.2), rfl, by simp only [absDiff]; omega⟩
  have hv : ∃ v : Square, v.1.val = k.1.val ∧ absDiff v.2.val k.2.val = 1 := by
    by_cases h0 : k.2.val = 0
    · exact ⟨(k.1, ⟨1, by omega⟩), rfl, by simp only [absDiff]; omega⟩
    · exact ⟨(k.1, ⟨k.2.val - 1, by omega⟩), rfl, by simp only [absDiff]; omega⟩
  obtain ⟨h, hh⟩ := hh
  obtain ⟨v, hv⟩ := hv
  exact ⟨h, v, hh, hv⟩

/-- A weak-king step to `s` is legal when `s` is adjoining, at distance ≥ 2 from the
strong king, and of the opposite colour to the bishop. -/
theorem weak_step_of_far {p : KBKState} {s : Square} (ht : p.turn = .weak)
    (hadj : Adjoining p.wk s) (hfar : 2 ≤ dInf p.sk s) (hcol : col s ≠ col p.bs) :
    Step (.kbk p) (.kbk { p with wk := s, turn := .strong }) := by
  refine Step.weakKing ht hadj ?_ ?_ ?_
  · intro he; rw [he, (dInf_eq_zero_iff).2 rfl] at hfar; omega
  · intro he; rw [he] at hcol; exact hcol rfl
  · rintro (hk | hb)
    · have := (attack_iff_dInf_one _ _).1 hk; simp only at this; omega
    · exact hcol (colour_of_bishopAttacks hb)

/-- **B2.** If the weak king is to move and in check, it has a legal move. -/
theorem weak_has_move_of_inCheck {p : KBKState} (hl : LKBK p) (ht : p.turn = .weak)
    (hc : weakInCheck p) : ∃ q, Step (.kbk p) q := by
  have hapart := kings_apart_of_LKBK hl
  -- The checker is the bishop, so the weak king stands on the bishop's colour.
  have hb : bishopAttacks (kingsOcc p.sk p.wk) p.bs p.wk := by
    rcases hc with hk | hb
    · have := (attack_iff_dInf_one _ _).1 hk; omega
    · exact hb
  have hcolk := colour_of_bishopAttacks hb
  obtain ⟨h, v, ⟨hh2, hh1⟩, ⟨hv1, hv2⟩⟩ := exists_orth_neighbours p.wk
  have adj_of : ∀ s : Square,
      (s.2.val = p.wk.2.val ∧ absDiff s.1.val p.wk.1.val = 1) ∨
      (s.1.val = p.wk.1.val ∧ absDiff s.2.val p.wk.2.val = 1) → Adjoining p.wk s := by
    intro s hs
    refine ⟨?_, ?_⟩
    · intro he; rw [square_eq_iff] at he; simp only [absDiff] at hs; omega
    · simp only [absDiff] at hs; omega
  -- The strong king cannot be within distance 1 of both `h` and `v`.
  have hfar : 2 ≤ dInf p.sk h ∨ 2 ≤ dInf p.sk v := by
    simp only [dInf, absDiff] at hapart ⊢
    simp only [absDiff] at hh1 hv2
    omega
  rcases hfar with hf | hf
  · refine ⟨_, weak_step_of_far ht (adj_of h (Or.inl ⟨hh2, hh1⟩)) hf ?_⟩
    rw [← hcolk]; exact colour_orth_neighbour (Or.inl ⟨hh2, hh1⟩)
  · refine ⟨_, weak_step_of_far ht (adj_of v (Or.inr ⟨hv1, hv2⟩)) hf ?_⟩
    rw [← hcolk]; exact colour_orth_neighbour (Or.inr ⟨hv1, hv2⟩)

/-! ## B3–B5: closure, induction, no checkmate -/

/-- After a bishop capture, the resulting K vs K position is admissible. -/
theorem admissible_of_capture {c : Colour} {sk bs : Square} (hne : sk ≠ bs)
    (hna : ¬ kingAttacks sk bs) (t : Colour) : Admissible (toKK c sk bs t) := by
  have h0 := dInf_ne_zero_of_ne hne
  have h1 : dInf sk bs ≠ 1 := fun h1 => hna ((attack_iff_dInf_one _ _).2 h1)
  cases c
  · simp only [toKK, Admissible]; omega
  · simp only [toKK, Admissible]; rw [dInf_comm]; omega

/-- **B3.** One-step closure of `LKBK ∪ AdmKK`. -/
theorem closed_of_step {p q : Pos} (hs : Step p q) (hp : Closed p) : Closed q := by
  cases hs with
  | strongKing _ _ hb hw hchk =>
    obtain ⟨_, _, hbw, _⟩ := hp
    exact ⟨hb, hw, hbw, hchk⟩
  | bishop _ _ hk hw hchk =>
    obtain ⟨_, hkw, _, _⟩ := hp
    exact ⟨fun h => hk h.symm, hkw, hw, hchk⟩
  | weakKing _ _ hk hb hchk =>
    obtain ⟨hkb, _, _, _⟩ := hp
    exact ⟨hkb, fun h => hk h.symm, fun h => hb h.symm, hchk⟩
  | weakCaptures _ _ hna =>
    obtain ⟨hkb, _, _, _⟩ := hp
    exact admissible_of_capture hkb hna _
  | kk hl => exact admissible_of_legal_step hl

/-- **B4.** Path closure, by induction on `Reach` (length zero included). -/
theorem closed_of_reach {p q : Pos} (hp : Closed p) (h : Reach p q) : Closed q := by
  induction h with
  | refl => exact hp
  | tail _ hs ih => exact closed_of_step hs ih

/-- **B5.** No position of the class is a checkmate. -/
theorem not_mated_of_closed {q : Pos} (hq : Closed q) : ¬ Mated q := by
  cases q with
  | kk a =>
    rintro (⟨_, hc, _⟩ | ⟨_, hc, _⟩)
    · exact not_inCheck_of_admissible hq _ hc
    · exact not_inCheck_of_admissible hq _ hc
  | kbk p =>
    rintro ⟨hc, hno⟩
    cases ht : p.turn
    · rw [ht] at hc; exact strong_not_inCheck_of_LKBK hq hc
    · rw [ht] at hc; exact hno (weak_has_move_of_inCheck hq ht hc)

/-- Every position of the class is dead. -/
theorem dead_of_closed {p : Pos} (hp : Closed p) : Dead p := by
  rintro ⟨q, hr, hm⟩
  exact not_mated_of_closed (closed_of_reach hp hr) hm

/-- **Theorem EC-C002.** Every locally legal K+B vs K configuration is dead. -/
theorem dead_of_LKBK {p : KBKState} (hp : LKBK p) : Dead (.kbk p) :=
  dead_of_closed hp

/-- **B0 (in-model).** A K+B vs K configuration produced by a legal move from any
K+B vs K configuration, with its three pieces on distinct squares, is locally legal. -/
theorem LKBK_of_step {p q : KBKState} (hs : Step (.kbk p) (.kbk q))
    (hd : q.sk ≠ q.bs ∧ q.sk ≠ q.wk ∧ q.bs ≠ q.wk) : LKBK q := by
  obtain ⟨h1, h2, h3⟩ := hd
  cases hs with
  | strongKing _ _ _ _ hchk => exact ⟨h1, h2, h3, hchk⟩
  | bishop _ _ _ _ hchk => exact ⟨h1, h2, h3, hchk⟩
  | weakKing _ _ _ _ hchk => exact ⟨h1, h2, h3, hchk⟩

/-- **Theorem EC-C002, last-move form.** Such a configuration is dead. -/
theorem dead_of_step {p q : KBKState} (hs : Step (.kbk p) (.kbk q))
    (hd : q.sk ≠ q.bs ∧ q.sk ≠ q.wk ∧ q.bs ≠ q.wk) : Dead (.kbk q) :=
  dead_of_LKBK (LKBK_of_step hs hd)

/-! ## Non-vacuity -/

def sqA1 : Square := (⟨0, by omega⟩, ⟨0, by omega⟩)
def sqB2 : Square := (⟨1, by omega⟩, ⟨1, by omega⟩)
def sqC3 : Square := (⟨2, by omega⟩, ⟨2, by omega⟩)
def sqH8 : Square := (⟨7, by omega⟩, ⟨7, by omega⟩)
def sqA8 : Square := (⟨0, by omega⟩, ⟨7, by omega⟩)
def sqB8 : Square := (⟨1, by omega⟩, ⟨7, by omega⟩)
def sqB6 : Square := (⟨1, by omega⟩, ⟨5, by omega⟩)
def sqC7 : Square := (⟨2, by omega⟩, ⟨6, by omega⟩)

/-- Weak Ka1, bishop c3, strong Kh8, weak to move. -/
def checkState : KBKState :=
  { strongColour := .white, sk := sqH8, bs := sqC3, wk := sqA1, turn := .weak }

/-- A bishop check exists (Bc3 checks Ka1 along the long diagonal). -/
theorem bishop_check_exists : weakInCheck checkState := by
  refine Or.inr ⟨by unfold onDiag absDiff; decide, ?_⟩
  intro r hbet hocc
  obtain ⟨_, ⟨hrq, _⟩, hsum⟩ := hbet
  unfold kingsOcc at hocc
  rcases hocc with he | he <;> subst he
  · revert hsum; decide
  · exact hrq rfl

/-- Weak Ka8, strong Kb6, bishop c7, weak to move. -/
def staleState : KBKState :=
  { strongColour := .white, sk := sqB6, bs := sqC7, wk := sqA8, turn := .weak }

/-- A stalemate exists, so the theorem does not rest on "there is always a move":
the weak king is not in check and has no legal move. -/
theorem stalemate_exists : ¬ weakInCheck staleState ∧ ¬ ∃ q, Step (.kbk staleState) q := by
  constructor
  · rintro (hk | ⟨⟨_, hd⟩, _⟩)
    · have := (attack_iff_dInf_one _ _).1 hk
      revert this; decide
    · revert hd; decide
  · rintro ⟨q, hs⟩
    cases hs with
    | strongKing ht => exact absurd ht (by decide)
    | bishop ht => exact absurd ht (by decide)
    | weakCaptures _ hadj => revert hadj; unfold Adjoining; decide
    | @weakKing _ s _ hadj _ _ hchk =>
      apply hchk
      obtain ⟨hne, h1, h2, h3, h4⟩ := hadj
      rw [Ne, square_eq_iff] at hne
      dsimp only [staleState, sqA8] at h1 h2 h3 h4 hne
      by_cases hb8 : s.1.val = 1 ∧ s.2.val = 7
      · -- b8 is attacked by the bishop on c7 (adjacent diagonal, nothing between).
        have hs : s = sqB8 := by rw [square_eq_iff]; dsimp only [sqB8]; omega
        subst hs
        refine Or.inr ⟨by unfold onDiag absDiff; decide, ?_⟩
        intro r hbet _
        obtain ⟨⟨hXr, _⟩, ⟨hrq, _⟩, hsum⟩ := hbet
        have a := dInf_ne_zero_of_ne hXr
        have b := dInf_ne_zero_of_ne hrq
        have c : dInf sqC7 sqB8 = 1 := by decide
        dsimp only [staleState] at hsum a b
        omega
      · -- a7 and b7 are adjacent to the strong king on b6.
        left
        refine (attack_iff_dInf_one _ _).2 ?_
        dsimp only [staleState, sqB6]
        simp only [dInf, absDiff]
        omega

/-- Weak Ka1, strong Kb2 (adjacent: an illegal, non-`LKBK` state), bishop h8. -/
def matedState : KBKState :=
  { strongColour := .white, sk := sqB2, bs := sqH8, wk := sqA1, turn := .weak }

/-- `Mated` is satisfiable, so `Dead` is not vacuous. That it happens only outside
`LKBK` is the content of the theorem. -/
theorem mated_satisfiable : Mated (.kbk matedState) := by
  refine ⟨Or.inl ((attack_iff_dInf_one _ _).2 (by decide)), ?_⟩
  rintro ⟨q, hs⟩
  cases hs with
  | strongKing ht => exact absurd ht (by decide)
  | bishop ht => exact absurd ht (by decide)
  | weakCaptures _ hadj => revert hadj; unfold Adjoining; decide
  | @weakKing _ s _ hadj hk _ hchk =>
    apply hchk; left
    refine (attack_iff_dInf_one _ _).2 ?_
    obtain ⟨hne, h1, h2, h3, h4⟩ := hadj
    rw [Ne, square_eq_iff] at hne hk
    dsimp only [matedState, sqA1, sqB2] at h1 h2 h3 h4 hne hk ⊢
    simp only [dInf, absDiff]
    omega

end EndgameChess.KBK
