import EndgameChess.Rules.Moves

/-!
# Rules kernel K2 — general lemmas about the kernel, and deadness transfer

Builds on the K1 kernel modules and does not modify them.
- characterisations of `attacked`, `inCheck` and `isPseudo` for king moves;
- kernel-level `ReachK`, `MatedK`, `DeadK`;
- `dead_transfer`: if a model's step relation corresponds exactly to kernel `Legal`
  under an embedding, then "dead" means the same thing in both.
-/

namespace EndgameChess.Rules

open EndgameChess.KK

/-! ## List / square lemmas -/

theorem any_allSquares {f : Square → Bool} : allSquares.any f = true ↔ ∃ s, f s = true := by
  rw [List.any_eq_true]
  exact ⟨fun ⟨s, _, h⟩ => ⟨s, h⟩, fun ⟨s, h⟩ => ⟨s, mem_allSquares s, h⟩⟩

theorem all_allSquares {f : Square → Bool} : allSquares.all f = true ↔ ∀ s, f s = true := by
  rw [List.all_eq_true]
  exact ⟨fun h s => h s (mem_allSquares s), fun h s _ => h s⟩

theorem attacked_iff {b : Board} {t : Square} {c : Colour} :
    attacked b t c = true ↔ ∃ s pc, b s = some pc ∧ pc.colour = c ∧ attacksFrom b pc s t = true := by
  unfold attacked
  rw [any_allSquares]
  constructor
  · rintro ⟨s, hs⟩
    revert hs
    cases hb : b s with
    | none => simp
    | some pc =>
      intro hs
      simp only [Bool.and_eq_true, beq_iff_eq] at hs
      exact ⟨s, pc, hb, hs.1, hs.2⟩
  · rintro ⟨s, pc, hb, hc, ha⟩
    refine ⟨s, ?_⟩
    rw [hb]; simp [hc, ha]

theorem inCheck_iff {p : Position} {c : Colour} :
    inCheck p c = true ↔ ∃ s, p.board s = some ⟨c, .king⟩ ∧ attacked p.board s c.opp = true := by
  unfold inCheck
  rw [any_allSquares]
  simp only [Bool.and_eq_true, beq_iff_eq]

theorem kingGeom_iff {s t : Square} : kingGeom s t = true ↔ dInf s t = 1 := by
  simp [kingGeom]

/-- Structure extensionality for positions. -/
theorem Position.ext' {p q : Position} (hb : ∀ s, p.board s = q.board s)
    (ht : p.turn = q.turn) (hc : p.castling = q.castling) (he : p.ep = q.ep) : p = q := by
  obtain ⟨b1, t1, c1, e1⟩ := p
  obtain ⟨b2, t2, c2, e2⟩ := q
  have hbb : b1 = b2 := funext hb
  simp only at ht hc he
  subst hbb ht hc he
  rfl

def noRights : CastlingRights := ⟨false, false, false, false⟩

theorem updateCastling_noRights (c : Colour) (k : Bool) (s t : Square) :
    updateCastling noRights c k s t = noRights := by
  simp [updateCastling, noRights]

/-- With no rook of the mover's colour on the board, castling is impossible. -/
theorem canCastle_false_of_noRook {p : Position} {m : Move}
    (h : ∀ s, p.board s ≠ some ⟨p.turn, .rook⟩) : canCastle p m = false := by
  unfold canCastle
  have h7 := h ((7 : Fin 8), homeRank p.turn)
  have h0 := h ((0 : Fin 8), homeRank p.turn)
  simp [h7, h0]

/-- A pseudo-legal move by a king: the king rules only. -/
theorem isPseudo_of_king {p : Position} {m : Move} (hsrc : p.board m.src = some ⟨p.turn, .king⟩) :
    isPseudo p m = (targetOK p m.dst && (m.promo.isNone && (kingGeom m.src m.dst || canCastle p m))) := by
  unfold isPseudo
  rw [hsrc]
  simp

/-- A castling move needs Chebyshev distance 2; a one-square king step never triggers
the castling branches of `play`. -/
theorem not_castle_of_step {c : Colour} {s t : Square} (hd : dInf s t = 1) :
    ¬ (s = ((4 : Fin 8), homeRank c) ∧ t = ((6 : Fin 8), homeRank c)) ∧
    ¬ (s = ((4 : Fin 8), homeRank c) ∧ t = ((2 : Fin 8), homeRank c)) := by
  constructor <;> rintro ⟨rfl, rfl⟩ <;> revert hd <;> cases c <;> decide

/-- The board after a one-square king step (no promotion, en passant or castling). -/
theorem play_kingStep {p : Position} {m : Move} (hsrc : p.board m.src = some ⟨p.turn, .king⟩)
    (hpro : m.promo = none) (hd : dInf m.src m.dst = 1) :
    play p m = { board := fun s => if s = m.dst then some ⟨p.turn, .king⟩
                                   else if s = m.src then none else p.board s,
                 turn := p.turn.opp,
                 castling := updateCastling p.castling p.turn true m.src m.dst,
                 ep := none } := by
  obtain ⟨hK, hQ⟩ := not_castle_of_step (c := p.turn) hd
  apply Position.ext'
  · intro s
    simp only [play, hsrc, hpro, beq_iff_eq, Option.some.injEq, Piece.mk.injEq,
      reduceCtorEq, Bool.and_eq_true]
    have hsd : m.src ≠ m.dst := by
      intro h; rw [h, (dInf_eq_zero_iff).2 rfl] at hd; exact absurd hd (by decide)
    by_cases h1 : s = m.dst
    · simp [h1]
    · by_cases h2 : s = m.src
      · subst h2; simp [hsd]
      · simp [h1, h2, hK, hQ]
  · rfl
  · simp [play, hsrc]
  · simp [play, hsrc]

/-! ## Kernel-level reachability, checkmate and dead position -/

/-- Finite series of kernel-legal moves (length `n ≥ 0`). -/
inductive ReachK : Position → Position → Prop
  | refl (p : Position) : ReachK p p
  | tail {p q r : Position} : ReachK p q → Legal q r → ReachK p r

/-- Kernel checkmate: the side to move is in check and has no legal move (Art. 1.4). -/
def MatedK (p : Position) : Prop := inCheck p p.turn = true ∧ ¬ ∃ q, Legal p q

/-- Kernel dead position (Art. 5.2.2, mathematical predicate): no series of legal moves
reaches a checkmate. -/
def DeadK (p : Position) : Prop := ¬ ∃ q, ReachK p q ∧ MatedK q

/-- Reflexive–transitive closure of a model's step relation. -/
inductive Chain {α : Type} (S : α → α → Prop) : α → α → Prop
  | refl (a : α) : Chain S a a
  | tail {a b c : α} : Chain S a b → S b c → Chain S a c

/-- **Deadness transfer.** Suppose a model's step relation `S`, restricted to an invariant
`I`, corresponds exactly to kernel `Legal` under `emb` (`hsim`), and kernel checkmate
corresponds to the model's checkmate `M` (`hmated`). Then kernel-dead and model-dead
agree on `I`. -/
theorem dead_transfer {α : Type} (emb : α → Position) (S : α → α → Prop) (I : α → Prop)
    (M : α → Prop)
    (hsim : ∀ a, I a → ∀ q, Legal (emb a) q ↔ ∃ b, S a b ∧ q = emb b)
    (hinv : ∀ a b, I a → S a b → I b)
    (hmated : ∀ a, I a → (MatedK (emb a) ↔ M a)) (a : α) (ha : I a) :
    DeadK (emb a) ↔ ¬ ∃ b, Chain S a b ∧ M b := by
  -- every kernel-reachable position is the image of a model-reachable one
  have back : ∀ q, ReachK (emb a) q → ∃ b, Chain S a b ∧ I b ∧ q = emb b := by
    intro q h
    induction h with
    | refl => exact ⟨a, Chain.refl a, ha, rfl⟩
    | tail _ hl ih =>
      obtain ⟨b, hc, hb, rfl⟩ := ih
      obtain ⟨b', hs, rfl⟩ := (hsim b hb _).1 hl
      exact ⟨b', Chain.tail hc hs, hinv b b' hb hs, rfl⟩
  have fwd : ∀ b, Chain S a b → I b ∧ ReachK (emb a) (emb b) := by
    intro b h
    induction h with
    | refl => exact ⟨ha, ReachK.refl _⟩
    | tail _ hs ih =>
      obtain ⟨hb, hr⟩ := ih
      exact ⟨hinv _ _ hb hs, ReachK.tail hr ((hsim _ hb _).2 ⟨_, hs, rfl⟩)⟩
  constructor
  · rintro hd ⟨b, hc, hm⟩
    obtain ⟨hb, hr⟩ := fwd b hc
    exact hd ⟨emb b, hr, (hmated b hb).2 hm⟩
  · rintro hd ⟨q, hr, hm⟩
    obtain ⟨b, hc, hb, rfl⟩ := back q hr
    exact hd ⟨b, hc, (hmated b hb).1 hm⟩

end EndgameChess.Rules
