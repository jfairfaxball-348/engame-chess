import EndgameChess.Rules.KPK.EntryPrefix

namespace EndgameChess.Rules.KPK
open EndgameChess.KK

private theorem fresh_entry_compose {q : Position} {σ : Colour} {m : Move} {n : Nat}
    (turn : q.turn = σ) (legal : isLegal q m = true)
    (boardBound : MateWithin σ n (play q m))
    (continuation : FreshGame.Within σ n (FreshGame.afterMove (FreshGame.fresh q) m)) :
    FreshGame.Within σ (n+1) (FreshGame.fresh q) := by
  have bound := choose_bound turn ⟨m, legal, rfl⟩ boardBound
  have count := FreshGame.occurrences_le_past (FreshGame.fresh q)
  have ongoing : FreshGame.Ongoing (FreshGame.fresh q) := by
    refine ⟨forceMate_not_dead ⟨n+1, bound⟩, ⟨_, m, legal, rfl⟩, ?_, ?_⟩
    · change 0 < 150; decide
    · change FreshGame.occurrences (FreshGame.fresh q) ≤ 0 + 1 at count; omega
  exact Or.inr ⟨ongoing, Or.inl ⟨turn, FreshGame.afterMove (FreshGame.fresh q) m,
    ⟨ongoing, m, legal, rfl⟩, continuation⟩⟩

/-- A legal king step into side-by-side seventh-rank support wins in 101 plies,
including the quiet entry and every weak reply before the promotion reset. -/
theorem fresh_supported_king_entry {q : Position} {σ : Colour} {sk ps wk t : Square}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk) (turn : q.turn = σ)
    (step : dInf sk t = 1) (notPawn : t ≠ ps) (apart : 2 ≤ dInf t wk)
    (support : SupportedSeventh σ t ps) : FreshGame.Within σ 101 (FreshGame.fresh q) := by
  obtain ⟨r, legal, material, nextTurn⟩ := king_move h turn step notPawn apart
  obtain ⟨m, hm, rfl⟩ := legal
  have boardBound := supported_weak_bound material nextTurn support apart
  have continuation : FreshGame.Within σ 100 (FreshGame.afterMove (FreshGame.fresh q) m) := by
    apply supported_weak_one_ply material nextTurn support apart
      (noRights_after_legal fresh.rights ⟨m, hm, rfl⟩)
    · intro r member
      change r ∈ [q] at member
      have same : r = q := List.mem_singleton.mp member
      subst r; exact ⟨sk, ps, wk, h⟩
    · have clock := FreshGame.afterMove_clock_le (FreshGame.fresh q) m
      exact clock
    · change 1 ≤ 1; decide
  exact fresh_entry_compose turn hm boardBound continuation

/-- A legal king step into the sixth-pawn band wins unless it stalemates
the defender immediately. The original fresh prefix is retained. -/
theorem fresh_seventh_king_entry {q : Position} {σ : Colour} {sk ps wk t : Square}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk) (turn : q.turn = σ)
    (step : dInf sk t = 1) (notPawn : t ≠ ps) (apart : 2 ≤ dInf t wk)
    (band : SeventhKing σ t ps) (notCorner : ¬ SixthCornerStalemate σ ps wk) :
    FreshGame.Within σ 103 (FreshGame.fresh q) := by
  obtain ⟨r, legal, material, nextTurn⟩ := king_move h turn step notPawn apart
  obtain ⟨m, hm, rfl⟩ := legal
  have boardBound := seventh_king_weak_board_bound material nextTurn band apart notCorner
  have continuation : FreshGame.Within σ 102 (FreshGame.afterMove (FreshGame.fresh q) m) := by
    apply seventh_king_weak_one_ply material nextTurn band apart notCorner
      (noRights_after_legal fresh.rights ⟨m, hm, rfl⟩)
    · intro r member
      change r ∈ [q] at member
      have same : r = q := List.mem_singleton.mp member
      subst r
      exact ⟨sk, ps, wk, h, by have := band.2.1; omega⟩
    · exact FreshGame.afterMove_clock_le (FreshGame.fresh q) m
    · change 1 ≤ 1; decide
  exact fresh_entry_compose turn hm boardBound continuation

/-- A finite geometric entry certificate; its absence is not a drawing criterion. -/
def KingEntry (σ : Colour) (sk ps wk : Square) : Prop :=
  ∃ t, dInf sk t = 1 ∧ t ≠ ps ∧ 2 ≤ dInf t wk ∧
    (SupportedSeventh σ t ps ∨ (SeventhKing σ t ps ∧ ¬ SixthCornerStalemate σ ps wk))

theorem fresh_king_entry_win {q : Position} {σ : Colour} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk) (turn : q.turn = σ)
    (entry : KingEntry σ sk ps wk) : FreshGame.ActualWin σ (FreshGame.fresh q) := by
  obtain ⟨t, step, notPawn, apart, support | ⟨band, notCorner⟩⟩ := entry
  · exact FreshGame.actual_win_of_rule ⟨101, fresh_supported_king_entry h fresh turn step notPawn apart support⟩
  · exact FreshGame.actual_win_of_rule ⟨103, fresh_seventh_king_entry h fresh turn step notPawn apart band notCorner⟩

/-- The vertical entry square for a sixth-rank king on an adjacent pawn file. -/
theorem sixth_rank_vertical_entry {σ : Colour} {sk ps wk : Square}
    (kingRank : height σ sk = 5) (pawnRank : height σ ps = 5 ∨ height σ ps = 6)
    (files : absDiff sk.1.val ps.1.val = 1)
    (apart : 2 ≤ dInf (atHeight σ sk.1 6) wk)
    (notCorner : height σ ps = 5 → ¬ SixthCornerStalemate σ ps wk) : KingEntry σ sk ps wk := by
  let t := atHeight σ sk.1 6
  have rank : height σ t = 6 := height_atHeight σ sk.1 6
  have step : dInf sk t = 1 := by
    rw [dInf_oriented σ, kingRank, rank]
    change max (absDiff sk.1.val sk.1.val) (absDiff 5 6) = 1
    simp [absDiff]
  have different : t ≠ ps := by
    intro same
    have fileSame : sk.1 = ps.1 := by simpa only [t, atHeight] using congrArg Prod.fst same
    simp [fileSame, absDiff] at files
  refine ⟨t, step, different, apart, ?_⟩
  rcases pawnRank with fifth | sixth
  · exact Or.inr ⟨⟨rank, fifth, files⟩, notCorner fifth⟩
  · exact Or.inl ⟨rank, sixth, files⟩

/-- Direct lower-rank coordination result, for either pawn colour. -/
theorem fresh_sixth_rank_entry_win {q : Position} {σ : Colour} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk) (turn : q.turn = σ)
    (kingRank : height σ sk = 5) (pawnRank : height σ ps = 5 ∨ height σ ps = 6)
    (files : absDiff sk.1.val ps.1.val = 1)
    (apart : 2 ≤ dInf (atHeight σ sk.1 6) wk)
    (notCorner : height σ ps = 5 → ¬ SixthCornerStalemate σ ps wk) :
    FreshGame.ActualWin σ (FreshGame.fresh q) :=
  fresh_king_entry_win h fresh turn (sixth_rank_vertical_entry kingRank pawnRank files apart notCorner)

end EndgameChess.Rules.KPK
