import EndgameChess.Rules.KRKTermination.Targets
import EndgameChess.Rules.RawClock.CastleEmpty
namespace EndgameChess.Rules
open EndgameChess.KK
set_option maxHeartbeats 3000000

/-- Actual strong castling moves the sole rook, preserving exact KRK with all flags. -/
theorem krk_castle_material {q : Position} {σ : Colour} {sk rs wk : Square} {m : Move}
    (hk : IsKRK q σ sk rs wk) (ht : q.turn = σ) (src : m.src = sk)
    (castle : canCastle q m = true) : ∃ ns nr, IsKRK (play q m) σ ns nr wk := by
  have uniqueRook : ∀ s, q.board s = some ⟨σ, .rook⟩ → s = rs := by
    intro s rook
    rw [hk.2.2.2] at rook
    rcases krkBoard_some rook with ⟨_, bad⟩ | ⟨squareEq, _⟩ | ⟨_, bad⟩
    · have badKind := congrArg Piece.kind bad
      cases badKind
    · exact squareEq
    · have badKind := congrArg Piece.kind bad
      cases badKind
  have atWeak : q.board wk = some ⟨σ.opp, .king⟩ := by
    rw [hk.2.2.2]
    exact krkBoard_wk hk.2.1 hk.2.2.1
  have emptyNotWeak : ∀ s, q.board s = none → s ≠ wk := by
    intro s empty equal
    rw [equal, atWeak] at empty
    cases empty
  have actual := castle
  unfold canCastle at actual
  rw [ht] at actual
  simp only [ Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    Option.isNone_iff_eq_none] at actual
  rcases actual with ⟨⟨⟨start, row⟩, promo⟩, king | queen⟩
  · have file := king.1.1.1.1.1.1.1
    have rook := king.1.1.1.1.1.2
    have cross := king.1.1.1.1.2
    have dest := king.1.1.1.2
    have kingSquare : sk = ((4 : Fin 8), homeRank σ) := src.symm.trans start
    have rookSquare : rs = ((7 : Fin 8), homeRank σ) := (uniqueRook _ rook).symm
    have destination : m.dst = ((6 : Fin 8), homeRank σ) := Prod.ext file row
    have move : m = ⟨((4 : Fin 8), homeRank σ), ((6 : Fin 8), homeRank σ), none⟩ := by
      cases m
      simp only [Move.mk.injEq]
      exact ⟨start, destination, promo⟩
    have oldBoard : q.board = krkBoard σ ((4 : Fin 8), homeRank σ)
        ((7 : Fin 8), homeRank σ) wk := by simpa only [kingSquare, rookSquare] using hk.2.2.2
    have oldKingWeak : ((4 : Fin 8), homeRank σ) ≠ wk := by simpa only [kingSquare] using hk.2.1
    have oldRookWeak : ((7 : Fin 8), homeRank σ) ≠ wk := by simpa only [rookSquare] using hk.2.2.1
    have newKingWeak := emptyNotWeak _ dest
    have newRookWeak := emptyNotWeak _ cross
    refine ⟨((6 : Fin 8), homeRank σ), ((5 : Fin 8), homeRank σ), ?_⟩
    refine ⟨by simp, newKingWeak, newRookWeak, ?_⟩
    rw [move]
    funext x
    by_cases e1 : x = ((6 : Fin 8), homeRank σ)
    · subst x; simp [play, ht, oldBoard, krkBoard]
    · by_cases e2 : x = ((4 : Fin 8), homeRank σ)
      · subst x; simp [play, ht, oldBoard, krkBoard, oldKingWeak]
      · by_cases e3 : x = ((7 : Fin 8), homeRank σ)
        · subst x; simp [play, ht, oldBoard, krkBoard, oldRookWeak]
        · by_cases e4 : x = ((5 : Fin 8), homeRank σ)
          · subst x; simp [play, ht, oldBoard, krkBoard]
          · simp [play, ht, oldBoard, krkBoard, e1, e2, e3, e4]
  · have file := queen.1.1.1.1.1.1.1.1
    have rook := queen.1.1.1.1.1.1.2
    have cross := queen.1.1.1.2
    have dest := queen.1.1.1.1.2
    have kingSquare : sk = ((4 : Fin 8), homeRank σ) := src.symm.trans start
    have rookSquare : rs = ((0 : Fin 8), homeRank σ) := (uniqueRook _ rook).symm
    have destination : m.dst = ((2 : Fin 8), homeRank σ) := Prod.ext file row
    have move : m = ⟨((4 : Fin 8), homeRank σ), ((2 : Fin 8), homeRank σ), none⟩ := by
      cases m
      simp only [Move.mk.injEq]
      exact ⟨start, destination, promo⟩
    have oldBoard : q.board = krkBoard σ ((4 : Fin 8), homeRank σ)
        ((0 : Fin 8), homeRank σ) wk := by simpa only [kingSquare, rookSquare] using hk.2.2.2
    have oldKingWeak : ((4 : Fin 8), homeRank σ) ≠ wk := by simpa only [kingSquare] using hk.2.1
    have oldRookWeak : ((0 : Fin 8), homeRank σ) ≠ wk := by simpa only [rookSquare] using hk.2.2.1
    have newKingWeak := emptyNotWeak _ dest
    have newRookWeak := emptyNotWeak _ cross
    refine ⟨((2 : Fin 8), homeRank σ), ((3 : Fin 8), homeRank σ), ?_⟩
    refine ⟨by simp, newKingWeak, newRookWeak, ?_⟩
    rw [move]
    funext x
    by_cases e1 : x = ((2 : Fin 8), homeRank σ)
    · subst x; simp [play, ht, oldBoard, krkBoard]
    · by_cases e2 : x = ((4 : Fin 8), homeRank σ)
      · subst x; simp [play, ht, oldBoard, krkBoard, oldKingWeak]
      · by_cases e3 : x = ((0 : Fin 8), homeRank σ)
        · subst x; simp [play, ht, oldBoard, krkBoard, oldRookWeak]
        · by_cases e4 : x = ((3 : Fin 8), homeRank σ)
          · subst x; simp [play, ht, oldBoard, krkBoard]
          · simp [play, ht, oldBoard, krkBoard, e1, e2, e3, e4]
end EndgameChess.Rules
