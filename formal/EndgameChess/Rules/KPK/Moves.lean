import EndgameChess.Rules.KPK.Material

namespace EndgameChess.Rules.KPK
open EndgameChess.KK

/-- Complete forward push geometry, including the initial double step. -/
def Push (q : Position) (σ : Colour) (ps t : Square) : Prop :=
  dx ps t = 0 ∧ q.board t = none ∧
    (dy ps t = forward σ ∨
      (dy ps t = 2 * forward σ ∧ ps.2.val = pawnRank σ ∧
        pathClear q.board ps t = true))

theorem pawn_pseudo_iff {q : Position} {σ : Colour} {sk ps wk : Square} {m : Move}
    (h : IsKPK q σ sk ps wk) (ht : q.turn = σ) (src : m.src = ps) :
    isPseudo q m = true ↔ Push q σ ps m.dst ∧ promoOK σ m = true := by
  have source : q.board m.src = some ⟨σ, .pawn⟩ := by
    rw [src, h.2.2.2]; exact LoneKing.board_xs h.1
  have noEP := no_enemy_pawn (s := (m.dst.1, m.src.2)) h
  rw [isPseudo, source]
  simp only [ht, beq_self_eq_true, Bool.true_and, Bool.and_eq_true]
  constructor
  · rintro ⟨target, move, promo⟩
    have empty := (strong_target_empty h ht).mp target
    have push := move
    simp only [pawnMoveOK, ht, src, empty, Option.isNone_none,
      Bool.and_true, Bool.and_false, Bool.or_false] at push
    have noEP' : (q.board (m.dst.1, ps.2) == some ⟨σ.opp, .pawn⟩) = false := by
      apply Bool.eq_false_iff.mpr
      intro yes
      exact noEP (by simpa only [src] using (beq_iff_eq.mp yes))
    simp only [noEP', Bool.and_false, Bool.or_false, Bool.or_eq_true,
      Bool.and_eq_true, beq_iff_eq] at push
    rcases push with ⟨file, rank⟩ | ⟨⟨⟨file, rank⟩, start⟩, clear⟩
    · exact ⟨⟨file, empty, Or.inl rank⟩, promo⟩
    · exact ⟨⟨file, empty, Or.inr ⟨rank, start, clear⟩⟩, promo⟩
  · rintro ⟨⟨file, empty, shape⟩, promo⟩
    refine ⟨(strong_target_empty h ht).mpr empty, ?_, promo⟩
    rcases shape with single | ⟨double, start, clear⟩
    · simp [pawnMoveOK, ht, src, file, empty, single]
    · simp [pawnMoveOK, ht, src, file, empty, double, start, clear]

theorem push_files {q : Position} {σ : Colour} {ps t : Square}
    (push : Push q σ ps t) : ps.1 = t.1 := by
  apply Fin.ext
  have zero := push.1
  simp only [dx] at zero
  omega

theorem push_ne {q : Position} {σ : Colour} {ps t : Square}
    (push : Push q σ ps t) : ps ≠ t := by
  intro e
  rcases push.2.2 with one | ⟨two, _, _⟩
  · cases σ <;> simp [e, dy, forward] at one
  · cases σ <;> simp [e, dy, forward] at two

/-- No EP deletion or rook motion occurs in a KPK pawn push, even with an EP marker. -/
theorem pawn_play_board {q : Position} {σ : Colour} {sk ps wk : Square} {m : Move}
    (h : IsKPK q σ sk ps wk) (ht : q.turn = σ) (src : m.src = ps)
    (push : Push q σ ps m.dst) :
    (play q m).board = fun s =>
      if s = m.dst then some ⟨σ, match m.promo with
        | none => .pawn | some k => k.toKind⟩
      else if s = ps then none else q.board s := by
  have source : q.board ps = some ⟨σ, .pawn⟩ := by
    rw [h.2.2.2]; exact LoneKing.board_xs h.1
  have files : ps.1 = m.dst.1 := push_files push
  funext s
  cases pro : m.promo <;> simp [play, source, files, pro, ht, src]

/-- Exact material after a push: either KPK or the selected promoted class. -/
theorem pawn_play_material {q : Position} {σ : Colour} {sk ps wk : Square} {m : Move}
    (h : IsKPK q σ sk ps wk) (ht : q.turn = σ) (src : m.src = ps)
    (push : Push q σ ps m.dst) :
    LoneKing.Material (match m.promo with | none => .pawn | some k => k.toKind)
      (play q m) σ sk m.dst wk := by
  have empty := push.2.1
  rw [h.2.2.2] at empty
  obtain ⟨nsk, nps, nwk⟩ := LoneKing.board_none.mp empty
  refine ⟨Ne.symm nsk, h.2.1, nwk, ?_⟩
  rw [pawn_play_board h ht src push]
  funext s
  rw [h.2.2.2]
  unfold LoneKing.board
  by_cases dst : s = m.dst
  · subst s; simp [nsk]
  · by_cases old : s = ps
    · subst s; simp [dst, Ne.symm h.1, h.2.2.1]
    · simp [dst, old]

/-- With separated kings, every pseudo-legal pawn push is legal. -/
theorem pawn_legal_iff {q : Position} {σ : Colour} {sk ps wk : Square} {m : Move}
    (h : IsKPK q σ sk ps wk) (ht : q.turn = σ) (src : m.src = ps)
    (far : 2 ≤ dInf sk wk) :
    isLegal q m = true ↔ Push q σ ps m.dst ∧ promoOK σ m = true := by
  constructor
  · intro legal
    have pseudo : isPseudo q m = true := by
      simp only [isLegal, Bool.and_eq_true] at legal
      exact legal.1
    exact (pawn_pseudo_iff h ht src).mp pseudo
  · intro shape
    have material := pawn_play_material h ht src shape.1
    have notKing : (match m.promo with | none => PieceType.pawn | some k => k.toKind) ≠ .king := by
      cases m.promo with
      | none => decide
      | some k => cases k <;> decide
    have safe : inCheck (play q m) σ = false := by
      cases he : inCheck (play q m) σ
      · rfl
      · have near := (LoneKing.strong_check notKing material).mp he
        rw [dInf_comm] at near
        omega
    simp [isLegal, (pawn_pseudo_iff h ht src).mpr shape, ht, safe]

/-- Complete strong move partition: ordinary king step or forward pawn push. -/
theorem strong_motion {q : Position} {σ : Colour} {sk ps wk : Square} {m : Move}
    (h : IsKPK q σ sk ps wk) (ht : q.turn = σ) (legal : isLegal q m = true) :
    (m.src = sk ∧ m.promo = none ∧ dInf sk m.dst = 1 ∧ q.board m.dst = none) ∨
    (m.src = ps ∧ Push q σ ps m.dst ∧ promoOK σ m = true) := by
  have pseudo : isPseudo q m = true := by
    simp only [isLegal, Bool.and_eq_true] at legal
    exact legal.1
  obtain ⟨pc, source, colour⟩ := own_of_isPseudo pseudo
  rw [h.2.2.2] at source
  rcases LoneKing.board_some source with ⟨src, rfl⟩ | ⟨src, rfl⟩ | ⟨_, rfl⟩
  · left
    have hs : q.board m.src = some ⟨q.turn, .king⟩ := by
      rw [ht, src, h.2.2.2]; exact LoneKing.board_sk
    have noCastle : canCastle q m = false := by
      apply canCastle_false_of_noRook
      intro s rook
      rw [h.2.2.2] at rook
      rcases LoneKing.board_some rook with ⟨_, e⟩ | ⟨_, e⟩ | ⟨_, e⟩ <;>
        have kind := congrArg Piece.kind e <;> cases kind
    rw [isPseudo_of_king hs, noCastle] at pseudo
    simp only [Bool.or_false, Bool.and_eq_true, Option.isNone_iff_eq_none] at pseudo
    exact ⟨src, pseudo.2.1, by simpa only [src] using kingGeom_iff.mp pseudo.2.2,
      (strong_target_empty h ht).mp pseudo.1⟩
  · exact Or.inr ⟨src, (pawn_pseudo_iff h ht src).mp pseudo⟩
  · exact False.elim (opp_ne σ (colour.trans ht).symm)

theorem king_play_material {q : Position} {σ : Colour} {sk ps wk : Square} {m : Move}
    (h : IsKPK q σ sk ps wk) (ht : q.turn = σ) (src : m.src = sk)
    (pro : m.promo = none) (step : dInf sk m.dst = 1) (empty : q.board m.dst = none) :
    IsKPK (play q m) σ m.dst ps wk := by
  have source : q.board m.src = some ⟨q.turn, .king⟩ := by
    rw [src, ht, h.2.2.2]; exact LoneKing.board_sk
  have none := empty
  rw [h.2.2.2] at none
  obtain ⟨nsk, nps, nwk⟩ := LoneKing.board_none.mp none
  refine ⟨nps, nwk, h.2.2.1, ?_⟩
  rw [play_board_simple source (by decide) pro (fun _ => by rw [src]; exact step)]
  funext s
  rw [src, ht, h.2.2.2]
  unfold LoneKing.board
  by_cases dst : s = m.dst
  · subst s; simp
  · by_cases old : s = sk
    · subst s; simp [dst, h.1, h.2.1]
    · simp [dst, old]

/-- Complete strong successor material, retaining every promotion alternative. -/
theorem strong_cases {q r : Position} {σ : Colour} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (ht : q.turn = σ) (legal : Legal q r) :
    (∃ t, IsKPK r σ t ps wk ∧ dInf sk t = 1 ∧ r.turn = σ.opp) ∨
    (∃ m, r = play q m ∧ m.src = ps ∧ Push q σ ps m.dst ∧
      promoOK σ m = true ∧
      LoneKing.Material (match m.promo with | none => .pawn | some k => k.toKind)
        r σ sk m.dst wk ∧ r.turn = σ.opp) := by
  obtain ⟨m, hm, rfl⟩ := legal
  rcases strong_motion h ht hm with ⟨src, pro, step, empty⟩ | ⟨src, push, promo⟩
  · exact Or.inl ⟨m.dst, king_play_material h ht src pro step empty, step,
      by rw [play_turn, ht]⟩
  · exact Or.inr ⟨m, rfl, src, push, promo, pawn_play_material h ht src push,
      by rw [play_turn, ht]⟩

/-- Constructive strong king step. Pawn attacks do not constrain its own king. -/
theorem king_move {q : Position} {σ : Colour} {sk ps wk t : Square}
    (h : IsKPK q σ sk ps wk) (ht : q.turn = σ)
    (step : dInf sk t = 1) (notPawn : t ≠ ps) (far : 2 ≤ dInf t wk) :
    ∃ r, Legal q r ∧ IsKPK r σ t ps wk ∧ r.turn = σ.opp := by
  let m : Move := ⟨sk, t, none⟩
  have nsk : t ≠ sk := Ne.symm (ne_of_dInf_pos (by omega))
  have nwk : t ≠ wk := ne_of_dInf_pos (by omega)
  have empty : q.board t = none := by
    rw [h.2.2.2]; exact LoneKing.board_none.mpr ⟨nsk, notPawn, nwk⟩
  have source : q.board m.src = some ⟨q.turn, .king⟩ := by
    rw [ht, h.2.2.2]; exact LoneKing.board_sk
  have pseudo : isPseudo q m = true := by
    rw [isPseudo_of_king source]
    simp [m, targetOK, empty, kingGeom_iff.mpr step]
  have material := king_play_material h ht (m := m) rfl rfl step empty
  have safe : inCheck (play q m) q.turn = false := by
    rw [ht]; exact strong_not_check material far
  exact ⟨play q m, legal_of_pseudo pseudo safe, material, by rw [play_turn, ht]⟩

/-- Constructive quiet weak king step, with the directional pawn attack excluded. -/
theorem weak_move {q : Position} {σ : Colour} {sk ps wk t : Square}
    (h : IsKPK q σ sk ps wk) (ht : q.turn = σ.opp)
    (step : dInf wk t = 1) (notPawn : t ≠ ps) (far : 2 ≤ dInf sk t)
    (notAttack : ¬ PawnSees σ ps t) :
    ∃ r, Legal q r ∧ IsKPK r σ sk ps t ∧ r.turn = σ := by
  let m : Move := ⟨wk, t, none⟩
  have nsk : t ≠ sk := Ne.symm (ne_of_dInf_pos (by omega))
  have nwk : t ≠ wk := Ne.symm (ne_of_dInf_pos (by omega))
  have empty : q.board t = none := by
    rw [h.2.2.2]; exact LoneKing.board_none.mpr ⟨nsk, notPawn, nwk⟩
  have source : q.board m.src = some ⟨q.turn, .king⟩ := by
    rw [ht, h.2.2.2]; exact LoneKing.board_wk h.2.1 h.2.2.1
  have pseudo : isPseudo q m = true := by
    rw [isPseudo_of_king source]
    simp [m, targetOK, empty, kingGeom_iff.mpr step]
  have material : IsKPK (play q m) σ sk ps t := by
    refine ⟨h.1, Ne.symm nsk, Ne.symm notPawn, ?_⟩
    rw [play_board_simple source (by decide) rfl (fun _ => step)]
    funext s
    rw [ht, h.2.2.2]
    unfold LoneKing.board
    by_cases dst : s = t
    · subst s; simp [m, nsk, notPawn]
    · by_cases old : s = wk
      · subst s; simp [m, dst, Ne.symm h.2.1, Ne.symm h.2.2.1]
      · simp [m, dst, old]
  have safe : inCheck (play q m) q.turn = false := by
    rw [ht]
    cases he : inCheck (play q m) σ.opp
    · rfl
    · rcases (weak_check material).mp he with adjacent | attack
      · omega
      · exact False.elim (notAttack attack)
  exact ⟨play q m, legal_of_pseudo pseudo safe, material,
    by rw [play_turn, ht, opp_opp]⟩

end EndgameChess.Rules.KPK
