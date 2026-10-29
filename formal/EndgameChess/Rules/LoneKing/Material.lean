import EndgameChess.Rules.KRKLive.Basic

/-! Shared material and king-attack interface for K+X versus a lone king.
No forcing, distance or outcome conclusion is built into these definitions. -/
namespace EndgameChess.Rules.LoneKing
open EndgameChess.KK

def board (k : PieceType) (σ : Colour) (sk xs wk : Square) : Board := fun s =>
  if s = sk then some ⟨σ, .king⟩
  else if s = xs then some ⟨σ, k⟩
  else if s = wk then some ⟨σ.opp, .king⟩
  else none

def Material (k : PieceType) (q : Position) (σ : Colour) (sk xs wk : Square) : Prop :=
  sk ≠ xs ∧ sk ≠ wk ∧ xs ≠ wk ∧ q.board = board k σ sk xs wk

theorem board_some {k : PieceType} {σ : Colour} {sk xs wk s : Square} {pc : Piece}
    (h : board k σ sk xs wk s = some pc) :
    (s = sk ∧ pc = ⟨σ, .king⟩) ∨ (s = xs ∧ pc = ⟨σ, k⟩) ∨
      (s = wk ∧ pc = ⟨σ.opp, .king⟩) := by
  unfold board at h
  by_cases h1 : s = sk
  · subst h1; simp at h; exact Or.inl ⟨rfl, h.symm⟩
  · by_cases h2 : s = xs
    · subst h2; simp [h1] at h; exact Or.inr (Or.inl ⟨rfl, h.symm⟩)
    · by_cases h3 : s = wk
      · subst h3; simp [h1, h2] at h; exact Or.inr (Or.inr ⟨rfl, h.symm⟩)
      · simp [h1, h2, h3] at h

theorem board_none {k : PieceType} {σ : Colour} {sk xs wk s : Square} :
    board k σ sk xs wk s = none ↔ s ≠ sk ∧ s ≠ xs ∧ s ≠ wk := by
  unfold board
  by_cases h1 : s = sk <;> by_cases h2 : s = xs <;>
    by_cases h3 : s = wk <;> simp_all

theorem board_sk {k : PieceType} {σ : Colour} {sk xs wk : Square} :
    board k σ sk xs wk sk = some ⟨σ, .king⟩ := by simp [board]

theorem board_xs {k : PieceType} {σ : Colour} {sk xs wk : Square} (h : sk ≠ xs) :
    board k σ sk xs wk xs = some ⟨σ, k⟩ := by simp [board, Ne.symm h]

theorem board_wk {k : PieceType} {σ : Colour} {sk xs wk : Square}
    (h1 : sk ≠ wk) (h2 : xs ≠ wk) :
    board k σ sk xs wk wk = some ⟨σ.opp, .king⟩ := by
  simp [board, Ne.symm h1, Ne.symm h2]

theorem king_at {k : PieceType} (nk : k ≠ .king)
    {σ : Colour} {sk xs wk s : Square} {c : Colour}
    (h13 : sk ≠ wk) (h23 : xs ≠ wk) :
    board k σ sk xs wk s = some ⟨c, .king⟩ ↔
      (c = σ ∧ s = sk) ∨ (c = σ.opp ∧ s = wk) := by
  constructor
  · intro h
    rcases board_some h with ⟨e, he⟩ | ⟨_, he⟩ | ⟨e, he⟩
    · simp only [Piece.mk.injEq] at he; exact Or.inl ⟨he.1, e⟩
    · have hh := congrArg Piece.kind he
      exact False.elim (nk hh.symm)
    · simp only [Piece.mk.injEq] at he; exact Or.inr ⟨he.1, e⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact board_sk
    · exact board_wk h13 h23

theorem attacked_iff {k : PieceType} {σ : Colour} {sk xs wk : Square}
    (h12 : sk ≠ xs) (h13 : sk ≠ wk) (h23 : xs ≠ wk) (t : Square) (c : Colour) :
    attacked (board k σ sk xs wk) t c = true ↔
      (c = σ ∧ (dInf sk t = 1 ∨
        attacksFrom (board k σ sk xs wk) ⟨σ,k⟩ xs t = true)) ∨
      (c = σ.opp ∧ dInf wk t = 1) := by
  rw [EndgameChess.Rules.attacked_iff]
  constructor
  · rintro ⟨s, pc, hb, hc, ha⟩
    rcases board_some hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨hc.symm, Or.inl (by simpa [attacksFrom, kingGeom_iff] using ha)⟩
    · exact Or.inl ⟨hc.symm, Or.inr ha⟩
    · exact Or.inr ⟨hc.symm, by simpa [attacksFrom, kingGeom_iff] using ha⟩
  · rintro (⟨rfl, hk | hx⟩ | ⟨rfl, hk⟩)
    · exact ⟨sk, _, board_sk, rfl, by simpa [attacksFrom, kingGeom_iff] using hk⟩
    · exact ⟨xs, _, board_xs h12, rfl, hx⟩
    · exact ⟨wk, _, board_wk h13 h23, rfl, by simpa [attacksFrom, kingGeom_iff] using hk⟩

theorem strong_check {k : PieceType} (nk : k ≠ .king)
    {q : Position} {σ : Colour} {sk xs wk : Square}
    (h : Material k q σ sk xs wk) :
    inCheck q σ = true ↔ dInf wk sk = 1 := by
  obtain ⟨h12,h13,h23,hb⟩ := h
  rw [inCheck_iff, hb]
  constructor
  · rintro ⟨s, hs, hat⟩
    rcases (king_at nk h13 h23).1 hs with ⟨_, rfl⟩ | ⟨e, _⟩
    · rcases (attacked_iff h12 h13 h23 _ _).1 hat with ⟨e, _⟩ | ⟨_, hk⟩
      · exact absurd e.symm (opp_ne _)
      · exact hk
    · exact absurd e (opp_ne _)
  · intro hh
    refine ⟨sk, (king_at nk h13 h23).2 (Or.inl ⟨rfl,rfl⟩), ?_⟩
    rw [attacked_iff h12 h13 h23]
    exact Or.inr ⟨rfl,hh⟩

theorem weak_check {k : PieceType} (nk : k ≠ .king)
    {q : Position} {σ : Colour} {sk xs wk : Square}
    (h : Material k q σ sk xs wk) :
    inCheck q σ.opp = true ↔ dInf sk wk = 1 ∨
      attacksFrom (board k σ sk xs wk) ⟨σ,k⟩ xs wk = true := by
  obtain ⟨h12,h13,h23,hb⟩ := h
  rw [inCheck_iff, hb]
  constructor
  · rintro ⟨s, hs, hat⟩
    rcases (king_at nk h13 h23).1 hs with ⟨e, _⟩ | ⟨_, rfl⟩
    · exact absurd e.symm (opp_ne _)
    · rw [opp_opp] at hat
      rcases (attacked_iff h12 h13 h23 _ _).1 hat with ⟨_, hh⟩ | ⟨e, _⟩
      · exact hh
      · exact absurd e (opp_ne _)
  · intro hh
    refine ⟨wk, (king_at nk h13 h23).2 (Or.inr ⟨rfl,rfl⟩), ?_⟩
    rw [opp_opp, attacked_iff h12 h13 h23]
    exact Or.inl ⟨rfl,hh⟩

end EndgameChess.Rules.LoneKing
