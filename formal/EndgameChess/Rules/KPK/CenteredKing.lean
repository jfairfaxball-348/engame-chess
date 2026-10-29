import EndgameChess.Rules.KPK.KingEntry

namespace EndgameChess.Rules.KPK
open EndgameChess.KK

/-- A non-rook pawn on the sixth, with its king directly ahead on the seventh. -/
def CenteredSeventh (σ : Colour) (sk ps : Square) : Prop :=
  height σ sk = 6 ∧ height σ ps = 5 ∧ sk.1 = ps.1 ∧
    1 ≤ ps.1.val ∧ ps.1.val ≤ 6

theorem centered_pawn_protected {σ : Colour} {sk ps : Square}
    (center : CenteredSeventh σ sk ps) : dInf sk ps = 1 := by
  rw [dInf_oriented σ, center.1, center.2.1, center.2.2.1]
  simp [absDiff]

theorem centered_not_corner {σ : Colour} {sk ps wk : Square}
    (center : CenteredSeventh σ sk ps) (far : 2 ≤ dInf sk wk) :
    ¬ SixthCornerStalemate σ ps wk := by
  rintro ⟨top, _, adjacent⟩
  rw [dInf_oriented σ, center.1, top, center.2.2.1, adjacent] at far
  simp [absDiff] at far

/-- Two flank squares exist for a non-rook pawn; choose the one away from
the defending king. Separation guarantees that this choice is legal. -/
theorem centered_flank_entry {σ : Colour} {sk ps wk : Square}
    (center : CenteredSeventh σ sk ps) (far : 2 ≤ dInf sk wk) :
    ∃ t, dInf sk t = 1 ∧ t ≠ ps ∧ 2 ≤ dInf t wk ∧ SeventhKing σ t ps := by
  obtain ⟨kingRank, pawnRank, files, low, high⟩ := center
  let x : Fin 8 := ⟨if wk.1.val ≤ ps.1.val then ps.1.val + 1 else ps.1.val - 1, by split <;> omega⟩
  let t := atHeight σ x 6
  have rank : height σ t = 6 := height_atHeight σ x 6
  have adjacent : absDiff x.val ps.1.val = 1 := by
    dsimp [x]; split <;> simp only [absDiff] <;> omega
  refine ⟨t, ?_, ?_, ?_, ⟨rank, pawnRank, adjacent⟩⟩
  · rw [dInf_oriented σ, kingRank, rank, files]
    simp only [t, atHeight, x, absDiff]
    split <;> omega
  · intro same; rw [same, pawnRank] at rank; cases rank
  · have bound := height_le σ wk
    rw [dInf_oriented σ, kingRank, files] at far
    rw [dInf_oriented σ, rank]
    simp only [t, atHeight, x, absDiff] at far ⊢
    split <;> omega

theorem centered_weak_has_move {q : Position} {σ : Colour} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (turn : q.turn = σ.opp)
    (center : CenteredSeventh σ sk ps) (far : 2 ≤ dInf sk wk) : ∃ r, Legal q r := by
  have bound := height_le σ wk
  let y : Fin 8 := ⟨if height σ wk = 0 then 1 else height σ wk - 1, by split <;> omega⟩
  let t := atHeight σ wk.1 y
  have rank : height σ t = y.val := height_atHeight σ wk.1 y
  have step : dInf wk t = 1 := by
    rw [dInf_oriented σ, rank]
    simp only [t, atHeight, y, absDiff]
    split <;> omega
  have apart : 2 ≤ dInf sk t := by
    rw [dInf_oriented σ, center.1] at far
    rw [dInf_oriented σ, center.1, rank]
    simp only [t, atHeight, y, absDiff] at far ⊢
    split <;> omega
  have notPawn : t ≠ ps := by
    intro same
    have protect := centered_pawn_protected center
    rw [same] at apart
    omega
  have notAttack : ¬ PawnSees σ ps t := by
    intro attack
    have shape := (pawn_sees_oriented σ ps t).mp attack
    rw [rank, center.2.1] at shape
    have top : height σ wk = 7 := by
      dsimp [y] at shape
      split at shape <;> omega
    have adjacent : absDiff ps.1.val wk.1.val = 1 := shape.2
    rw [dInf_oriented σ, center.1, center.2.2.1, top, adjacent] at far
    simp [absDiff] at far
  obtain ⟨r, legal, _⟩ := weak_move h turn step notPawn apart notAttack
  exact ⟨r, legal⟩

theorem centered_weak_reply {q r : Position} {σ : Colour} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (turn : q.turn = σ.opp)
    (center : CenteredSeventh σ sk ps) (legal : Legal q r) :
    ∃ t, IsKPK r σ sk ps t ∧ r.turn = σ ∧ 2 ≤ dInf sk t := by
  obtain ⟨t, material, nextTurn, _⟩ := LoneKing.safe_reply h turn
    (Or.inr (centered_pawn_protected center)) legal
  exact ⟨t, material, nextTurn, LoneKing.kings_apart_after (by decide) material legal⟩

theorem centered_strong_bound {q : Position} {σ : Colour} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (turn : q.turn = σ)
    (center : CenteredSeventh σ sk ps) (far : 2 ≤ dInf sk wk) : MateWithin σ 103 q := by
  obtain ⟨t, step, notPawn, apart, band⟩ := centered_flank_entry center far
  obtain ⟨r, legal, material, nextTurn⟩ := king_move h turn step notPawn apart
  exact choose_bound turn legal
    (seventh_king_weak_board_bound material nextTurn band apart (centered_not_corner center far))

theorem fresh_centered_strong {q : Position} {σ : Colour} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk) (turn : q.turn = σ)
    (center : CenteredSeventh σ sk ps) : FreshGame.Within σ 103 (FreshGame.fresh q) := by
  obtain ⟨t, step, notPawn, apart, band⟩ := centered_flank_entry center fresh.kings
  exact fresh_seventh_king_entry h fresh turn step notPawn apart band
    (centered_not_corner center fresh.kings)

theorem fresh_centered_weak {q : Position} {σ : Colour} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk) (turn : q.turn = σ.opp)
    (center : CenteredSeventh σ sk ps) : FreshGame.Within σ 104 (FreshGame.fresh q) := by
  have moves := centered_weak_has_move h turn center fresh.kings
  have allBoard : ∀ r, Legal q r → MateWithin σ 103 r := by
    intro r legal
    obtain ⟨t, material, nextTurn, apart⟩ := centered_weak_reply h turn center legal
    exact centered_strong_bound material nextTurn center apart
  have live : ¬ DeadK q := by
    obtain ⟨r, legal⟩ := moves
    obtain ⟨t, reach, goal⟩ := mateWithin_sound (allBoard r legal)
    exact fun dead => dead ⟨t, reachK_cons legal reach, goal.2⟩
  have count := FreshGame.occurrences_le_past (FreshGame.fresh q)
  have ongoing : FreshGame.Ongoing (FreshGame.fresh q) := by
    refine ⟨live, moves, ?_, ?_⟩
    · change 0 < 150; decide
    · change FreshGame.occurrences (FreshGame.fresh q) ≤ 0 + 1 at count; omega
  have all : ∀ s, FreshGame.BoardStep (FreshGame.fresh q) s → FreshGame.Within σ 103 s := by
    intro s actual
    have legal := FreshGame.step_legal actual
    obtain ⟨w, material, nextTurn, apart⟩ := centered_weak_reply h turn center legal
    obtain ⟨_, a, ha, rfl⟩ := actual
    obtain ⟨t, step, notPawn, targetFar, band⟩ := centered_flank_entry center apart
    obtain ⟨r, entry, entered, weakTurn⟩ := king_move material nextTurn step notPawn targetFar
    obtain ⟨b, hb, rfl⟩ := entry
    have clock1 := FreshGame.afterMove_clock_le (FreshGame.fresh q) a
    have clock2 := FreshGame.afterMove_clock_le (FreshGame.afterMove (FreshGame.fresh q) a) b
    change (FreshGame.afterMove (FreshGame.fresh q) a).clock ≤ 0 + 1 at clock1
    have length1 : (FreshGame.afterMove (FreshGame.fresh q) a).past.length = 1 := rfl
    have count1 := FreshGame.occurrences_le_past (FreshGame.afterMove (FreshGame.fresh q) a)
    have bound1 := centered_strong_bound material nextTurn center apart
    have ongoing1 : FreshGame.Ongoing (FreshGame.afterMove (FreshGame.fresh q) a) :=
      ⟨forceMate_not_dead ⟨103, bound1⟩, ⟨_, b, hb, rfl⟩, by omega, by omega⟩
    have rights1 := noRights_after_legal fresh.rights legal
    have rights2 := noRights_after_legal rights1 (show Legal _ _ from ⟨b, hb, rfl⟩)
    have suffix : FreshGame.Within σ 102
        (FreshGame.afterMove (FreshGame.afterMove (FreshGame.fresh q) a) b) := by
      apply seventh_king_weak_two_ply entered weakTurn band targetFar
        (centered_not_corner center apart) rights2
      · intro old member
        change old ∈ [play q a, q] at member
        rcases List.mem_cons.mp member with first | last
        · subst old; exact ⟨sk, ps, w, material, by have := center.2.1; omega⟩
        · have same : old = q := List.mem_singleton.mp last
          subst old; exact ⟨sk, ps, wk, h, by have := center.2.1; omega⟩
      · omega
      · change 2 ≤ 2; decide
      · exact FreshGame.two_ply_no_claim q a b
    exact Or.inr ⟨ongoing1, Or.inl ⟨nextTurn, _, ⟨ongoing1, b, hb, rfl⟩, suffix⟩⟩
  obtain ⟨r, legal⟩ := moves
  obtain ⟨s, actual, _⟩ := FreshGame.layer.reply_complete ongoing legal
  exact Or.inr ⟨ongoing, Or.inr ⟨turn, FreshGame.fresh_no_claim q, ⟨s, actual⟩, all⟩⟩

/-- The centered seventh-rank key square wins for every admitted defender
placement, either pawn colour and either turn, excluding rook pawns. -/
theorem fresh_centered_win {q : Position} {σ : Colour} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk)
    (center : CenteredSeventh σ sk ps) : FreshGame.ActualWin σ (FreshGame.fresh q) := by
  apply FreshGame.actual_win_of_rule
  rcases colour_cases σ q.turn with turn | turn
  · exact ⟨103, fresh_centered_strong h fresh turn center⟩
  · exact ⟨104, fresh_centered_weak h fresh turn center⟩

end EndgameChess.Rules.KPK
