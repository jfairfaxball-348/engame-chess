import EndgameChess.Rules.KPK.Progress

namespace EndgameChess.Rules.KPK
open EndgameChess.KK

/-- Construct a square by file and oriented height, for either pawn colour. -/
def atHeight (σ : Colour) (file rank : Fin 8) : Square :=
  (file, match σ with | .white => rank | .black => ⟨7 - rank.val, by omega⟩)

theorem height_atHeight (σ : Colour) (file rank : Fin 8) :
    height σ (atHeight σ file rank) = rank.val := by
  cases σ <;> simp only [height, atHeight] <;> omega

theorem dInf_oriented (σ : Colour) (s t : Square) :
    dInf s t = max (absDiff s.1.val t.1.val) (absDiff (height σ s) (height σ t)) := by
  cases σ <;> simp only [height, dInf, absDiff] <;> omega

theorem square_eq_oriented {σ : Colour} {s t : Square} :
    s = t ↔ s.1 = t.1 ∧ height σ s = height σ t := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨files, ranks⟩
    apply Prod.ext files
    apply Fin.ext
    cases σ <;> simp only [height] at ranks <;> omega

theorem pawn_sees_oriented (σ : Colour) (ps t : Square) :
    PawnSees σ ps t ↔ height σ t = height σ ps + 1 ∧ absDiff ps.1.val t.1.val = 1 := by
  cases σ <;> simp only [PawnSees, height, dy, dx, forward, absDiff] <;> omega

end EndgameChess.Rules.KPK
