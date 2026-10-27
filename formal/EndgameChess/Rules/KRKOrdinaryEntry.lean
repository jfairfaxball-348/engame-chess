import EndgameChess.Rules.KRKStrongPrefix

namespace EndgameChess.Rules.KRKOrdinaryEntry
open EndgameChess.KK KRKThreePly
set_option maxHeartbeats 300000

theorem king_legal {q : Position} {σ : Colour} {sk rs wk t : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ)
    (distance : dInf sk t = 1) (notRook : t ≠ rs) (far : 2 ≤ dInf t wk) :
    isLegal q ⟨sk,t,none⟩ = true := by
  have next := canonical_king_material material turn distance notRook far
  have notOld : t ≠ sk := Ne.symm (ne_of_dInf_pos (by omega))
  have notWeak : t ≠ wk := ne_of_dInf_pos (by omega)
  have atKing : q.board sk = some ⟨q.turn,.king⟩ := by rw [turn,material.2.2.2]; exact krkBoard_sk
  have empty : q.board t = none := by rw [material.2.2.2]; exact krkBoard_eq_none.2 ⟨notOld,notRook,notWeak⟩
  have pseudo : isPseudo q ⟨sk,t,none⟩ = true := by
    rw [isPseudo_of_king atKing]
    simp [targetOK,empty,kingGeom_iff.mpr distance]
  have noCheck : inCheck (play q ⟨sk,t,none⟩) q.turn = false := by
    rw [turn]
    cases check : inCheck (play q ⟨sk,t,none⟩) σ with
    | false => rfl
    | true =>
      have close := (inCheck_strong_krk next.1 next.2.1 next.2.2.1 next.2.2.2).mp check
      rw [dInf_comm] at close
      omega
  simp [isLegal,pseudo,noCheck]

theorem rook_legal {q : Position} {σ : Colour} {sk rs wk t : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ)
    (sees : RookSees rs t sk wk) (notKing : t ≠ sk) (notWeak : t ≠ wk)
    (far : 2 ≤ dInf sk wk) : isLegal q ⟨rs,t,none⟩ = true := by
  have atRook : q.board rs = some ⟨q.turn,.rook⟩ := by rw [turn,material.2.2.2]; exact krkBoard_rs material.1
  have notOld : t ≠ rs := ne_of_rookLine sees.1
  have empty : q.board t = none := by rw [material.2.2.2]; exact krkBoard_eq_none.2 ⟨notKing,notOld,notWeak⟩
  have attack : attacksFrom q.board ⟨q.turn,.rook⟩ rs t = true := by
    rw [material.2.2.2,turn]; exact (rook_attacks_krk material.1 t).mpr sees
  have pseudo : isPseudo q ⟨rs,t,none⟩ = true := by
    unfold isPseudo; rw [atRook]; simp [targetOK,empty,attack]
  have board : (play q ⟨rs,t,none⟩).board = krkBoard σ sk t wk := by
    rw [play_board_simple atRook (by decide) rfl (by intro h; cases h)]
    funext x
    rw [material.2.2.2,turn]
    unfold krkBoard
    by_cases a : x = t
    · subst x; simp [notKing]
    · by_cases b : x = rs
      · subst x; simp [a,material.1.symm,material.2.2.1]
      · simp [a,b]
  have noCheck : inCheck (play q ⟨rs,t,none⟩) q.turn = false := by
    rw [turn]
    cases check : inCheck (play q ⟨rs,t,none⟩) σ with
    | false => rfl
    | true =>
      have close := (inCheck_strong_krk notKing.symm material.2.1 notWeak board).mp check
      rw [dInf_comm] at close
      omega
  simp [isLegal,pseudo,noCheck]

end EndgameChess.Rules.KRKOrdinaryEntry
