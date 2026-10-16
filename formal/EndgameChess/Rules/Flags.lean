import EndgameChess.Rules.AgreeKBK

/-!
# Rules kernel K3 — castling and en-passant flags are irrelevant without rooks and pawns

A kernel position carries castling rights and an en-passant target. On a board with no
rooks and no pawns (`NRP`), neither can influence anything:
- castling needs a rook (Art. 3.8.2);
- en passant and two-square advances need pawns (Art. 3.7).

This module proves that, then shows that normalising the flags (`normFlags`) preserves
`DeadK`. So a low-material position reached by *any* legal move — whatever flags it
carries — can be compared with the flag-free embeddings `ofKK` / `ofKBK` of K2.
-/

namespace EndgameChess.Rules

open EndgameChess.KK

/-- No rooks and no pawns on the board. -/
def NRP (p : Position) : Prop :=
  ∀ s pc, p.board s = some pc → pc.kind ≠ .rook ∧ pc.kind ≠ .pawn

/-- The same position with no castling rights and no en-passant target. -/
def normFlags (p : Position) : Position := { p with castling := noRights, ep := none }

theorem inCheck_of_board {p q : Position} (h : p.board = q.board) (c : Colour) :
    inCheck p c = inCheck q c := by
  unfold inCheck; rw [h]

theorem nrp_noRook {p : Position} (h : NRP p) (s : Square) :
    p.board s ≠ some ⟨p.turn, .rook⟩ := fun e => (h s _ e).1 rfl

theorem nrp_normFlags {p : Position} (h : NRP p) : NRP (normFlags p) := h

/-- On an `NRP` board, a pseudo-legal move never promotes, and a king move is a
one-square step. -/
theorem nrp_pseudo {p : Position} {m : Move} (h : NRP p) (hp : isPseudo p m = true) :
    ∃ pc, p.board m.src = some pc ∧ pc.colour = p.turn ∧ m.promo = none ∧
      (pc.kind = .king → dInf m.src m.dst = 1) := by
  obtain ⟨⟨col, kind⟩, hb, hc⟩ := own_of_isPseudo hp
  simp only at hc; subst hc
  refine ⟨_, hb, rfl, ?_⟩
  obtain ⟨hnr, hnp⟩ := h _ _ hb
  cases kind with
  | king =>
    rw [isPseudo_of_king hb, canCastle_false_of_noRook (nrp_noRook h)] at hp
    simp only [Bool.or_false, Bool.and_eq_true, Option.isNone_iff_eq_none] at hp
    exact ⟨hp.2.1, fun _ => kingGeom_iff.1 hp.2.2⟩
  | pawn => exact absurd rfl hnp
  | rook => exact absurd rfl hnr
  | queen | bishop | knight =>
    unfold isPseudo at hp
    rw [hb] at hp
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hp
    exact ⟨hp.2.1, fun e => by cases e⟩

/-- The position after a pseudo-legal move on an `NRP` board: the moving piece arrives,
its square empties, and there is no castling, promotion, en passant or new en-passant
target. -/
theorem play_nrp {p : Position} {m : Move} (h : NRP p) (hp : isPseudo p m = true) :
    play p m = { board := fun s => if s = m.dst then p.board m.src
                                   else if s = m.src then none else p.board s,
                 turn := p.turn.opp,
                 castling := updateCastling p.castling p.turn
                   (p.board m.src == some ⟨p.turn, .king⟩) m.src m.dst,
                 ep := none } := by
  obtain ⟨⟨col, kind⟩, hb, hc, hpro, hk⟩ := nrp_pseudo h hp
  simp only at hc; subst hc
  obtain ⟨_, hnp⟩ := h _ _ hb
  have hpawn : (some (⟨p.turn, kind⟩ : Piece) == some ⟨p.turn, .pawn⟩) = false := by
    rw [Bool.eq_false_iff]; simpa using hnp
  -- the castling branches of `play` are inactive
  have hcas : ¬ (kind = .king ∧ m.src = ((4 : Fin 8), homeRank p.turn) ∧
        m.dst = ((6 : Fin 8), homeRank p.turn)) ∧
      ¬ (kind = .king ∧ m.src = ((4 : Fin 8), homeRank p.turn) ∧
        m.dst = ((2 : Fin 8), homeRank p.turn)) := by
    constructor
    · rintro ⟨hkk, hs, hd⟩; exact (not_castle_of_step (c := p.turn) (hk hkk)).1 ⟨hs, hd⟩
    · rintro ⟨hkk, hs, hd⟩; exact (not_castle_of_step (c := p.turn) (hk hkk)).2 ⟨hs, hd⟩
  apply Position.ext'
  · intro s
    simp only [play, hb, hpro, hpawn, Bool.false_and, Bool.false_eq_true, ite_false,
      beq_iff_eq, Option.some.injEq, Piece.mk.injEq, true_and, Bool.and_eq_true]
    by_cases h1 : s = m.dst
    · simp [h1]
    · by_cases h2 : s = m.src
      · simp [h2]
      · simp only [h1, h2, ite_false]
        by_cases hkk : kind = .king
        · have hn1 : ¬ (m.src = ((4 : Fin 8), homeRank p.turn) ∧
              m.dst = ((6 : Fin 8), homeRank p.turn)) := fun hh => hcas.1 ⟨hkk, hh.1, hh.2⟩
          have hn2 : ¬ (m.src = ((4 : Fin 8), homeRank p.turn) ∧
              m.dst = ((2 : Fin 8), homeRank p.turn)) := fun hh => hcas.2 ⟨hkk, hh.1, hh.2⟩
          subst hkk
          simp [hn1, hn2]
        · simp [hkk]
  · rfl
  · simp [play, hb]
  · simp [play, hb, hpawn]

theorem isPseudo_normFlags {p : Position} (h : NRP p) (m : Move) :
    isPseudo (normFlags p) m = isPseudo p m := by
  have htg : targetOK (normFlags p) m.dst = targetOK p m.dst := rfl
  have hc1 : canCastle (normFlags p) m = false :=
    canCastle_false_of_noRook (nrp_noRook (nrp_normFlags h))
  have hc2 : canCastle p m = false := canCastle_false_of_noRook (nrp_noRook h)
  cases hb : p.board m.src with
  | none =>
    have hb' : (normFlags p).board m.src = none := hb
    simp only [isPseudo, hb, hb']
  | some pc =>
    have hb' : (normFlags p).board m.src = some pc := hb
    obtain ⟨hnr, hnp⟩ := h _ _ hb
    obtain ⟨col, kind⟩ := pc
    cases kind with
    | pawn => exact absurd rfl hnp
    | rook => exact absurd rfl hnr
    | king => simp only [isPseudo, hb, hb', hc1, hc2, htg]; rfl
    | queen | bishop | knight => simp only [isPseudo, hb, hb', htg]; rfl

theorem play_normFlags {p : Position} {m : Move} (h : NRP p) (hp : isPseudo p m = true) :
    play (normFlags p) m = normFlags (play p m) := by
  have hp' : isPseudo (normFlags p) m = true := by rw [isPseudo_normFlags h]; exact hp
  rw [play_nrp (nrp_normFlags h) hp', play_nrp h hp]
  apply Position.ext'
  · intro s; rfl
  · rfl
  · simp [normFlags, updateCastling_noRights]
  · rfl

theorem isLegal_normFlags {p : Position} (h : NRP p) (m : Move) :
    isLegal (normFlags p) m = isLegal p m := by
  unfold isLegal
  rw [isPseudo_normFlags h]
  cases hp : isPseudo p m with
  | false => simp only [Bool.false_and]
  | true =>
    rw [play_normFlags h hp]
    have e1 : (normFlags p).turn = p.turn := rfl
    have e2 : inCheck (normFlags (play p m)) p.turn = inCheck (play p m) p.turn :=
      inCheck_of_board (show (normFlags (play p m)).board = (play p m).board from rfl) _
    rw [e1, e2]

theorem nrp_of_legal {p q : Position} (h : NRP p) (hl : Legal p q) : NRP q := by
  obtain ⟨m, hm, rfl⟩ := hl
  have hp : isPseudo p m = true := by
    unfold isLegal at hm; simp only [Bool.and_eq_true] at hm; exact hm.1
  rw [play_nrp h hp]
  intro s pc hs
  simp only at hs
  by_cases h1 : s = m.dst
  · simp only [h1, ite_true] at hs; exact h _ _ hs
  · simp only [h1, ite_false] at hs
    by_cases h2 : s = m.src
    · simp only [h2, ite_true] at hs; cases hs
    · simp only [h2, ite_false] at hs; exact h _ _ hs

theorem legal_normFlags_iff {a : Position} (h : NRP a) (q : Position) :
    Legal (normFlags a) q ↔ ∃ b, Legal a b ∧ q = normFlags b := by
  constructor
  · rintro ⟨m, hm, rfl⟩
    rw [isLegal_normFlags h] at hm
    have hp : isPseudo a m = true := by
      unfold isLegal at hm; simp only [Bool.and_eq_true] at hm; exact hm.1
    exact ⟨play a m, ⟨m, hm, rfl⟩, play_normFlags h hp⟩
  · rintro ⟨b, ⟨m, hm, rfl⟩, rfl⟩
    have hp : isPseudo a m = true := by
      unfold isLegal at hm; simp only [Bool.and_eq_true] at hm; exact hm.1
    exact ⟨m, by rw [isLegal_normFlags h]; exact hm, (play_normFlags h hp).symm⟩

theorem chain_legal_iff_reachK {p q : Position} : Chain Legal p q ↔ ReachK p q := by
  constructor
  · intro h; induction h with
    | refl => exact ReachK.refl _
    | tail _ hs ih => exact ReachK.tail ih hs
  · intro h; induction h with
    | refl => exact Chain.refl _
    | tail _ hs ih => exact Chain.tail ih hs

/-- **Flag irrelevance for deadness.** On a board with no rooks and no pawns, castling
rights and the en-passant target do not affect whether the position is dead. -/
theorem deadK_normFlags_iff {q : Position} (h : NRP q) : DeadK (normFlags q) ↔ DeadK q := by
  have := dead_transfer normFlags Legal NRP MatedK
    (fun a ha q => legal_normFlags_iff ha q)
    (fun _ _ ha hl => nrp_of_legal ha hl)
    (fun a ha => by
      unfold MatedK
      rw [inCheck_of_board (q := a) rfl]
      constructor
      · rintro ⟨hc, hn⟩
        exact ⟨hc, fun ⟨b, hb⟩ => hn ⟨normFlags b, (legal_normFlags_iff ha _).2 ⟨b, hb, rfl⟩⟩⟩
      · rintro ⟨hc, hn⟩
        refine ⟨hc, fun ⟨r, hr⟩ => ?_⟩
        obtain ⟨b, hb, _⟩ := (legal_normFlags_iff ha r).1 hr
        exact hn ⟨b, hb⟩)
    q h
  rw [this]
  simp only [DeadK, chain_legal_iff_reachK]

end EndgameChess.Rules
