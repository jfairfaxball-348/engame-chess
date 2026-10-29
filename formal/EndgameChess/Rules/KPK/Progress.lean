import EndgameChess.Rules.KPK.Geometry
import EndgameChess.Rules.FreshGame.Definitions

namespace EndgameChess.Rules.KPK
open EndgameChess.KK

/-- Distance advanced from the pawn owner's home rank (not optimal DTZ). -/
def height (σ : Colour) (ps : Square) : Nat :=
  match σ with | .white => ps.2.val | .black => 7 - ps.2.val

theorem height_le (σ : Colour) (ps : Square) : height σ ps ≤ 7 := by
  cases σ <;> simp only [height] <;> omega

/-- A push increases oriented rank by exactly one or two; no board enumeration. -/
theorem push_height {q : Position} {σ : Colour} {ps t : Square}
    (push : Push q σ ps t) :
    height σ t = height σ ps + 1 ∨
      (height σ t = height σ ps + 2 ∧ ps.2.val = pawnRank σ) := by
  rcases push.2.2 with single | ⟨double, start, _⟩
  · left; cases σ <;> simp only [height, dy, forward] at single ⊢ <;> omega
  · right; refine ⟨?_, start⟩
    cases σ <;> simp only [height, dy, forward] at double ⊢ <;> omega

theorem push_strict {q : Position} {σ : Colour} {ps t : Square}
    (push : Push q σ ps t) : height σ ps < height σ t := by
  rcases push_height push with one | ⟨two, _⟩ <;> omega

theorem promotion_rank (σ : Colour) (t : Square) :
    t.2.val = lastRank σ ↔ height σ t = 7 := by
  cases σ <;> simp only [lastRank, height] <;> omega

theorem promo_none_iff (σ : Colour) (ps t : Square) :
    promoOK σ ⟨ps, t, none⟩ = true ↔ height σ t ≠ 7 := by
  simp only [promoOK]
  split <;> simp_all [promotion_rank]

theorem promo_some_iff (σ : Colour) (ps t : Square) (k : PromoPiece) :
    promoOK σ ⟨ps, t, some k⟩ = true ↔ height σ t = 7 := by
  simp only [promoOK]
  split <;> simp_all [promotion_rank]

/-- A legal promotion push is always a single step from the penultimate rank. -/
theorem promotion_single {q : Position} {σ : Colour} {ps t : Square}
    (push : Push q σ ps t) (last : t.2.val = lastRank σ) :
    dy ps t = forward σ ∧ height σ ps = 6 := by
  rcases push.2.2 with one | ⟨two, start, _⟩
  · refine ⟨one, ?_⟩
    cases σ <;> simp only [lastRank, height, dy, forward] at last one ⊢ <;> omega
  · cases σ <;> simp only [lastRank, pawnRank, forward, dy] at last start two <;> omega

/-- Every pawn push is an actual zeroing move, including promotion. -/
theorem pawn_zeroing {q : Position} {σ : Colour} {sk ps wk : Square} {m : Move}
    (h : IsKPK q σ sk ps wk) (ht : q.turn = σ) (src : m.src = ps) :
    RawClock.zeroing q m = true := by
  have source : q.board ps = some ⟨σ, .pawn⟩ := by
    rw [h.2.2.2]; exact LoneKing.board_xs h.1
  simp [RawClock.zeroing, src, source, ht]

theorem pawn_resets_clock {s : FreshGame.State} {σ : Colour} {sk ps wk : Square} {m : Move}
    (h : IsKPK s.board σ sk ps wk) (ht : s.board.turn = σ) (src : m.src = ps) :
    (FreshGame.afterMove s m).clock = 0 := by
  simp [FreshGame.afterMove, pawn_zeroing h ht src]

/-- Promotion clears EP; a two-square marker can only arise on a double push. -/
theorem promotion_ep_none {q : Position} {σ : Colour} {sk ps wk : Square} {m : Move}
    (h : IsKPK q σ sk ps wk) (ht : q.turn = σ) (src : m.src = ps)
    (push : Push q σ ps m.dst) (last : m.dst.2.val = lastRank σ) :
    (play q m).ep = none := by
  have single := (promotion_single push last).1
  have abs : (dy m.src m.dst).natAbs = 1 := by
    rw [src, single]; cases σ <;> rfl
  simp [play, abs]

/-- Exact nonpromoting KPK material has a unique pawn square. -/
theorem pawn_square_unique {q : Position} {σ : Colour} {sk ps wk sk' ps' wk' : Square}
    (h : IsKPK q σ sk ps wk) (h' : IsKPK q σ sk' ps' wk') : ps = ps' := by
  have source : q.board ps' = some ⟨σ, .pawn⟩ := by
    rw [h'.2.2.2]; exact LoneKing.board_xs h'.1
  rw [h.2.2.2] at source
  rcases LoneKing.board_some source with ⟨_, e⟩ | ⟨e, _⟩ | ⟨_, e⟩
  · have kind := congrArg Piece.kind e; cases kind
  · exact e.symm
  · have kind := congrArg Piece.kind e; cases kind

/-- Every KPK-to-KPK legal step preserves the pawn or strictly advances it.
Promotion cannot masquerade as a KPK successor. -/
theorem kpk_step_progress {q r : Position} {σ : Colour} {sk ps wk a p b : Square}
    (h : IsKPK q σ sk ps wk) (next : IsKPK r σ a p b) (legal : Legal q r) :
    ps = p ∨ height σ ps < height σ p := by
  rcases colour_cases σ q.turn with turn | turn
  · rcases strong_cases h turn legal with ⟨t, hm, _⟩ |
        ⟨m, _, _, push, _, hm, _⟩
    · exact Or.inl (pawn_square_unique hm next)
    · cases pro : m.promo with
      | none =>
        simp only [pro] at hm
        have same := pawn_square_unique hm next
        exact Or.inr (by rw [← same]; exact push_strict push)
      | some k =>
        simp only [pro] at hm
        have impossible := pawn_material_kind hm next
        cases k <;> cases impossible
  · rcases LoneKing.weak_cases h turn legal with ⟨t, hm, _⟩ | ⟨w, b', kk⟩
    · exact Or.inl (pawn_square_unique hm next)
    · have source : r.board p = some ⟨σ, .pawn⟩ := by
        rw [next.2.2.2]; exact LoneKing.board_xs next.1
      exact False.elim ((nrp_kkBoard kk.2 p _ source).2 rfl)

theorem kpk_step_monotone {q r : Position} {σ : Colour} {sk ps wk a p b : Square}
    (h : IsKPK q σ sk ps wk) (next : IsKPK r σ a p b) (legal : Legal q r) :
    height σ ps ≤ height σ p := by
  rcases kpk_step_progress h next legal with same | strict
  · simp [same]
  · omega

/-- Exact KPK admits no en-passant capture, whatever raw marker is stored. -/
theorem no_legalEP {q : Position} {σ : Colour} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) : ¬ ∃ m, RawRepetition.LegalEP q m := by
  rintro ⟨m, event⟩
  have source := event.2.1
  change q.board m.src = some ⟨q.turn, .pawn⟩ at source
  have owner := (pawn_at h source).1
  have enemy := event.2.2.2.2.2
  rw [owner] at enemy
  exact no_enemy_pawn h enemy

theorem effectiveEP_none {q : Position} {σ : Colour} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) : RawRepetition.effectiveEP q = none := by
  classical
  simp [RawRepetition.effectiveEP, no_legalEP h]

/-- Equality of repetition keys forces equality of the pawn square. -/
theorem key_pawn_unique {q r : Position} {σ : Colour} {sk ps wk a p b : Square}
    (h : IsKPK q σ sk ps wk) (next : IsKPK r σ a p b)
    (same : RawRepetition.key q = RawRepetition.key r) : ps = p := by
  have boards : q.board = r.board := by
    simpa only [RawRepetition.key, RawRepetition.normalizeEP] using congrArg Position.board same
  apply pawn_square_unique h
  exact ⟨next.1, next.2.1, next.2.2.1, boards.trans next.2.2.2⟩

theorem different_height_different_key {q r : Position} {σ : Colour} {sk ps wk a p b : Square}
    (h : IsKPK q σ sk ps wk) (next : IsKPK r σ a p b)
    (different : height σ ps ≠ height σ p) : RawRepetition.key q ≠ RawRepetition.key r := by
  intro same
  exact different (congrArg (height σ) (key_pawn_unique h next same))

end EndgameChess.Rules.KPK
