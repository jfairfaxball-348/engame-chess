import EndgameChess.Rules.KPK.Coord.Game

/-! The lone king is short of moves only on its last rank, next to a pawn on the
sixth or seventh rank. A promoted rook leaves a reply except in one corner trap. -/
namespace EndgameChess.Rules.KPK.Coord

/-- The eight neighbours of `(e,f)`, as the possible targets of a king step. -/
theorem weak_reply {a b c d e f : Nat} (D : Dom a b c d e f) (open_top : f ≤ 6 ∨ d ≤ 4 ∨ c + 2 < e ∨ e + 2 < c)
    (keep : ¬ Capture a b c d e f) :
    ∃ x y, WeakStep a b c d e f x y := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  have k1 := D.k1
  have k3 := D.k3
  unfold Capture Near at keep
  apply Classical.byContradiction
  intro no
  have t (x y : Nat) : ¬ WeakStep a b c d e f x y := fun s => no ⟨x, y, s⟩
  have h1 := t (e + 1) f
  have h2 := t (e - 1) f
  have h3 := t e (f + 1)
  have h4 := t e (f - 1)
  have h5 := t (e + 1) (f - 1)
  have h6 := t (e - 1) (f - 1)
  have h7 := t (e + 1) (f + 1)
  have h8 := t (e - 1) (f + 1)
  unfold WeakStep Near Apart Att at h1 h2 h3 h4 h5 h6 h7 h8
  rcases k1 with k | k | k | k <;>
    rcases Nat.lt_trichotomy e c with g | g | g <;>
    rcases Nat.lt_trichotomy f d with j | j | j <;> omega

end EndgameChess.Rules.KPK.Coord
