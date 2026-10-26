import EndgameChess.Rules.KRKMateGeometry
import EndgameChess.Rules.KRKTermination.Castle

namespace EndgameChess.Rules.KRKMatingMove
open EndgameChess.KK KRKMateGeometry
set_option maxHeartbeats 200000

private theorem king_square {q : Position} {σ : Colour} {sk rs wk t : Square}
    (hk : IsKRK q σ sk rs wk) (atKing : q.board t = some ⟨σ, .king⟩) : t = sk := by
  rw [hk.2.2.2] at atKing
  rcases krkBoard_some atKing with ⟨e, _⟩ | ⟨_, bad⟩ | ⟨_, bad⟩
  · exact e
  · have := congrArg Piece.kind bad; cases this
  · have := congrArg Piece.colour bad; exact False.elim (opp_ne σ this)

private theorem rook_square {q : Position} {σ : Colour} {sk rs wk t : Square}
    (hk : IsKRK q σ sk rs wk) (atRook : q.board t = some ⟨σ, .rook⟩) : t = rs := by
  rw [hk.2.2.2] at atRook
  rcases krkBoard_some atRook with ⟨_, bad⟩ | ⟨e, _⟩ | ⟨_, bad⟩
  · have := congrArg Piece.kind bad; cases this
  · exact e
  · have := congrArg Piece.kind bad; cases this

private theorem separated_after {q : Position} {σ : Colour} {sk rs wk : Square}
    (hk : IsKRK q σ sk rs wk) (safe : inCheck q σ = false) : 2 ≤ dInf sk wk := by
  have nz : dInf sk wk ≠ 0 := fun h => hk.2.1 (dInf_eq_zero_iff.mp h)
  have noOne : dInf sk wk ≠ 1 := by
    intro h
    have check := (inCheck_strong_krk hk.1 hk.2.1 hk.2.2.1 hk.2.2.2).mpr
      (by rwa [dInf_comm])
    rw [check] at safe
    cases safe
  omega

theorem castle_not_mate {q : Position} {σ : Colour} {sk rs wk : Square} {m : Move}
    (hk : IsKRK q σ sk rs wk) (turn : q.turn = σ) (src : m.src = sk)
    (legal : isLegal q m = true) (castle : canCastle q m = true) :
    ¬MatedK (play q m) := by
  obtain ⟨ns, nr, material⟩ := krk_castle_material hk turn src castle
  have safe := not_inCheck_after_legal legal
  rw [turn] at safe
  have far := separated_after material safe
  have source : q.board m.src = some ⟨σ, .king⟩ := by
    rw [src, hk.2.2.2]; exact krkBoard_sk
  have actual := castle
  simp only [canCastle, turn, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    Option.isNone_iff_eq_none] at actual
  rcases actual with ⟨⟨⟨start, row⟩, promo⟩, king | queen⟩
  · have file := king.1.1.1.1.1.1.1
    have dest : m.dst = ((6 : Fin 8), homeRank σ) := Prod.ext file row
    have move : m = ⟨((4 : Fin 8), homeRank σ), ((6 : Fin 8), homeRank σ), none⟩ := by
      cases m; simp only [Move.mk.injEq]; exact ⟨start, dest, promo⟩
    rw [start] at source
    have nsEq := king_square material (t := ((6 : Fin 8), homeRank σ))
      (by rw [move]; simp [play, turn, source])
    have nrEq := rook_square material (t := ((5 : Fin 8), homeRank σ))
      (by rw [move]; simp [play, turn, source])
    intro mate
    have terminal := (kernel_mate_iff material (by simp [play_turn, turn]) far).mp mate
    rw [← nsEq, ← nrEq] at terminal
    cases σ <;> simp only [Terminal, Horizontal, homeRank, absDiff] at terminal <;> omega
  · have file := queen.1.1.1.1.1.1.1.1
    have dest : m.dst = ((2 : Fin 8), homeRank σ) := Prod.ext file row
    have move : m = ⟨((4 : Fin 8), homeRank σ), ((2 : Fin 8), homeRank σ), none⟩ := by
      cases m; simp only [Move.mk.injEq]; exact ⟨start, dest, promo⟩
    rw [start] at source
    have nsEq := king_square material (t := ((2 : Fin 8), homeRank σ))
      (by rw [move]; simp [play, turn, source])
    have nrEq := rook_square material (t := ((3 : Fin 8), homeRank σ))
      (by rw [move]; simp [play, turn, source])
    intro mate
    have terminal := (kernel_mate_iff material (by simp [play_turn, turn]) far).mp mate
    rw [← nsEq, ← nrEq] at terminal
    cases σ <;> simp only [Terminal, Horizontal, homeRank, absDiff] at terminal <;> omega

theorem king_move_not_mate {q : Position} {σ : Colour} {sk rs wk : Square} {m : Move}
    (hk : IsKRK q σ sk rs wk) (turn : q.turn = σ) (src : m.src = sk)
    (legal : isLegal q m = true) (notCheck : ¬RookSees rs wk sk wk) :
    ¬MatedK (play q m) := by
  by_cases castle : canCastle q m = true
  · exact castle_not_mate hk turn src legal castle
  obtain ⟨h12, h13, h23, hb⟩ := hk
  have hp : isPseudo q m = true := by
    have h := legal
    unfold isLegal at h
    simp only [Bool.and_eq_true] at h
    exact h.1
  have hsrc : q.board m.src = some ⟨q.turn, .king⟩ := by
    rw [hb, turn, src]; exact krkBoard_sk
  rw [isPseudo_of_king hsrc] at hp
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, Bool.or_eq_true] at hp
  obtain ⟨target, promo, geom⟩ := hp
  have step : dInf sk m.dst = 1 := by
    rw [←src]; exact kingGeom_iff.mp (geom.resolve_right castle)
  have dstKing : m.dst ≠ sk := Ne.symm (ne_of_dInf_pos (by omega))
  have dstRook : m.dst ≠ rs := by
    intro e
    have h := (targetOK_some target (by rw [hb, e]; exact krkBoard_rs h12)).1
    exact h turn.symm
  have dstWeak : m.dst ≠ wk := by
    intro e
    exact (targetOK_some target (by rw [hb, e]; exact krkBoard_wk h13 h23)).2 rfl
  have board := play_board_simple hsrc (by decide) promo (fun _ => by rwa [src])
  have material : IsKRK (play q m) σ m.dst rs wk := by
    refine ⟨dstRook, dstWeak, h23, ?_⟩
    rw [board]; funext x; rw [hb, turn, src]; unfold krkBoard
    by_cases e1 : x = m.dst
    · subst x; simp
    · by_cases e2 : x = sk
      · subst x; simp [e1, h12, h13]
      · simp [e1, e2]
  have safe := not_inCheck_after_legal legal
  rw [turn] at safe
  have far := separated_after material safe
  intro mate
  exact king_step_not_mate step far notCheck
    (kernel_mate_model material (by simp [play_turn, turn]) far mate)

/-- Every actual mating move comes from the rook, including when castling
rights are present. No legal strong alternative has been discarded. -/
theorem mating_source {q : Position} {σ : Colour} {sk rs wk : Square} {m : Move}
    (hk : IsKRK q σ sk rs wk) (turn : q.turn = σ)
    (legal : isLegal q m = true) (notCheck : ¬RookSees rs wk sk wk)
    (mate : MatedK (play q m)) : m.src = rs := by
  have hp : isPseudo q m = true := by
    have h := legal
    unfold isLegal at h
    simp only [Bool.and_eq_true] at h
    exact h.1
  obtain ⟨pc, source, colour⟩ := own_of_isPseudo hp
  rw [hk.2.2.2] at source
  rcases krkBoard_some source with ⟨king, rfl⟩ | ⟨rook, _⟩ | ⟨_, rfl⟩
  · exact False.elim (king_move_not_mate hk turn king legal notCheck mate)
  · exact rook
  · rw [turn] at colour
    exact False.elim (opp_ne σ colour.symm)

theorem rook_move_model {q : Position} {σ : Colour} {sk rs wk : Square} {m : Move}
    (hk : IsKRK q σ sk rs wk) (turn : q.turn = σ)
    (legal : isLegal q m = true) (src : m.src = rs) :
    IsKRK (play q m) σ sk m.dst wk ∧ RookSees rs m.dst sk wk := by
  obtain ⟨h12, h13, h23, hb⟩ := hk
  have hp : isPseudo q m = true := by
    have h := legal
    unfold isLegal at h
    simp only [Bool.and_eq_true] at h
    exact h.1
  have hsrc : q.board m.src = some ⟨q.turn, .rook⟩ := by
    rw [hb, turn, src]; exact krkBoard_rs h12
  unfold isPseudo at hp
  rw [hsrc] at hp
  simp only [beq_self_eq_true, Bool.true_and, Bool.and_eq_true,
    Option.isNone_iff_eq_none] at hp
  obtain ⟨target, promo, attack⟩ := hp
  have sees : RookSees rs m.dst sk wk := by
    rw [hb, turn, src] at attack
    exact (rook_attacks_krk h12 _).mp attack
  have dstKing : m.dst ≠ sk := by
    intro e
    exact (targetOK_some target (by rw [hb, e]; exact krkBoard_sk)).2 rfl
  have dstRook : m.dst ≠ rs := ne_of_rookLine sees.1
  have dstWeak : m.dst ≠ wk := by
    intro e
    exact (targetOK_some target (by rw [hb, e]; exact krkBoard_wk h13 h23)).2 rfl
  have board := play_board_simple hsrc (by decide) promo (by intro h; cases h)
  refine ⟨⟨Ne.symm dstKing, h13, dstWeak, ?_⟩, sees⟩
  rw [board]; funext x; rw [hb, turn, src]; unfold krkBoard
  by_cases e1 : x = m.dst
  · subst x; simp [dstKing]
  · by_cases e2 : x = rs
    · subst x; simp [e1, Ne.symm h12, h23]
    · simp [e1, e2]

end EndgameChess.Rules.KRKMatingMove
