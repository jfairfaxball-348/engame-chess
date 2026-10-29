import EndgameChess.Rules.KRKCastleEight

namespace EndgameChess.Rules.KRKSevenMiddle
open EndgameChess.KK
set_option maxHeartbeats 300000

/-- At the two central edge files, seven-ply strong forcing adds no
boards to five-ply forcing, because every weak six-ply child is already four. -/
theorem kernel_seven_five_iff {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ) (rank : wk.2.val = 0)
    (low : 3 ≤ wk.1.val) (high : wk.1.val ≤ 4) : MateWithin σ 7 q ↔ MateWithin σ 5 q := by
  constructor
  · intro win
    rcases win with goal | ⟨_,chosen | defended⟩
    · exact Or.inl goal
    · obtain ⟨_,r,⟨m,legal,rfl⟩,child⟩ := chosen
      obtain ⟨ns,nr,next⟩ := krk_strong_material material turn legal
      have nextTurn : (play q m).turn = σ.opp := by rw [play_turn,turn]
      have four := (KRKSixMiddle.kernel_six_four_iff next nextTurn
        (KRKEdgeDepth.arrival_far ⟨m,legal,rfl⟩ next) rank low high).mp child
      exact mateWithin_choose turn ⟨m,legal,rfl⟩ four
    · exact False.elim (opp_ne σ (turn.symm.trans defended.1))
  · intro win; exact mateWithin_mono win (by decide)

theorem bottom_clear_iff {sk rs wk : Square} (rank : wk.2.val = 0)
    (low : 3 ≤ wk.1.val) (high : wk.1.val ≤ 4)
    (distinct : sk ≠ rs) (notKing : sk ≠ wk) (notRook : rs ≠ wk)
    (far : 2 ≤ dInf sk wk) (notCheck : ¬RookSees rs wk sk wk) :
    KRKSevenGeometry.Clear sk rs wk ↔ KRKFiveMiddle.BottomFive sk rs wk := by
  let q := krkPos .white sk rs wk .white
  have material : IsKRK q .white sk rs wk := ⟨distinct,notKing,notRook,rfl⟩
  exact (KRKSevenGeometry.kernel_seven_iff material rfl far notCheck).symm.trans
    ((kernel_seven_five_iff material rfl rank low high).trans
      ((KRKFiveGeometry.kernel_five_iff material rfl far notCheck).trans
        (KRKFiveMiddle.bottom_clear_iff rank (by omega) (by omega) distinct notKing notRook far notCheck)))

theorem low_rook_clear_iff {sk rs wk : Square} (rank : wk.2.val = 0)
    (low : 3 ≤ wk.1.val) (high : wk.1.val ≤ 4) (height : rs.2.val ≤ 1)
    (distinct : sk ≠ rs) (notKing : sk ≠ wk) (notRook : rs ≠ wk)
    (far : 2 ≤ dInf sk wk) (notCheck : ¬RookSees rs wk sk wk) :
    KRKSevenGeometry.Clear sk rs wk ↔ KRKFiveMiddle.LowRookFive sk rs wk :=
  (bottom_clear_iff rank low high distinct notKing notRook far notCheck).trans
    (KRKFiveMiddle.low_rook_bottom_iff (by omega) (by omega) height)

end EndgameChess.Rules.KRKSevenMiddle
