import EndgameChess.Rules.KRKCastleEight

namespace EndgameChess.Rules.KRKNineEntry
open EndgameChess.KK
set_option maxHeartbeats 300000

theorem eight_entry_move {q : Position} {σ : Colour} {sk rs wk ns nr : Square}
    {m : Move} (material : IsKRK q σ sk rs wk) (turn : q.turn = σ)
    (legal : isLegal q m = true) (next : IsKRK (play q m) σ ns nr wk)
    (notMate : ¬MatedK (play q m)) (win : MateWithin σ 8 (play q m)) :
    (m.src = sk ∧ m.promo = none ∧ dInf sk m.dst = 1 ∧
      IsKRK (play q m) σ m.dst rs wk ∧
      KRKEightGeometry.Clear m.dst rs wk) ∨
    (m.src = rs ∧ m.promo = none ∧ RookSees rs m.dst sk wk ∧
      IsKRK (play q m) σ sk m.dst wk ∧
      KRKEightGeometry.Clear sk m.dst wk) := by
  have nextTurn : (play q m).turn = σ.opp := by rw [play_turn,turn]
  have geometry := (KRKEightGeometry.kernel_eight_iff next nextTurn notMate).mp win
  have pseudo : isPseudo q m = true := by
    simp only [isLegal, Bool.and_eq_true] at legal; exact legal.1
  obtain ⟨piece, source, colour⟩ := own_of_isPseudo pseudo
  rw [material.2.2.2] at source
  rcases krkBoard_some source with ⟨src, rfl⟩ | ⟨src, rfl⟩ | ⟨_, rfl⟩
  · by_cases castle : canCastle q m = true
    · exact False.elim (KRKCastleEight.castle_not_eight material turn legal notMate src castle next win)
    · obtain ⟨moved, distance⟩ := KRKThreePly.king_move_model material turn src legal castle
      have nsEq := KRKCastleFour.king_square next (t := m.dst) (by rw [moved.2.2.2]; exact krkBoard_sk)
      have nrEq := KRKCastleFour.rook_square next (t := rs) (by rw [moved.2.2.2]; exact krkBoard_rs moved.1)
      rw [←nsEq, ←nrEq] at geometry
      have atKing : q.board m.src = some ⟨q.turn, .king⟩ := by
        rw [src, turn, material.2.2.2]; exact krkBoard_sk
      rw [isPseudo_of_king atKing] at pseudo
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at pseudo
      exact Or.inl ⟨src, pseudo.2.1, distance, moved, geometry⟩
  · obtain ⟨moved, sees⟩ := KRKMatingMove.rook_move_model material turn legal src
    have nsEq := KRKCastleFour.king_square next (t := sk) (by rw [moved.2.2.2]; exact krkBoard_sk)
    have nrEq := KRKCastleFour.rook_square next (t := m.dst) (by rw [moved.2.2.2]; exact krkBoard_rs moved.1)
    rw [←nsEq, ←nrEq] at geometry
    have atRook : q.board m.src = some ⟨q.turn, .rook⟩ := by
      rw [src, turn, material.2.2.2]; exact krkBoard_rs material.1
    unfold isPseudo at pseudo
    rw [atRook] at pseudo
    simp only [beq_self_eq_true, Bool.true_and, Bool.and_eq_true,
      Option.isNone_iff_eq_none] at pseudo
    exact Or.inr ⟨src, pseudo.2.1, sees, moved, geometry⟩
  · exact False.elim (opp_ne σ (colour.trans turn).symm)

end EndgameChess.Rules.KRKNineEntry
