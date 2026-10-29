import EndgameChess.Rules.KPK.Corner

namespace EndgameChess.Rules.KPK
open EndgameChess.KK

def promotionSquare (σ : Colour) (file : Fin 8) : Square :=
  (file, match σ with | .white => 7 | .black => 0)

/-- The corner and its two orthogonal neighbours form a rook-pawn holding region. -/
def RookFortress (σ : Colour) (ps wk : Square) : Prop :=
  (ps.1.val = 0 ∨ ps.1.val = 7) ∧ 1 ≤ height σ ps ∧ height σ ps ≤ 6 ∧
    ((height σ wk = 7 ∧ absDiff ps.1.val wk.1.val ≤ 1) ∨
      (height σ wk = 6 ∧ ps.1 = wk.1))

theorem promotion_square_height (σ : Colour) (file : Fin 8) :
    height σ (promotionSquare σ file) = 7 := by cases σ <;> rfl

/-- Away from the corner itself, retreating into the corner is safe from the strong king. -/
theorem fortress_return {σ : Colour} {sk ps wk : Square}
    (fort : RookFortress σ ps wk) (far : 2 ≤ dInf sk wk)
    (away : wk ≠ promotionSquare σ ps.1) :
    dInf wk (promotionSquare σ ps.1) = 1 ∧
      2 ≤ dInf sk (promotionSquare σ ps.1) := by
  obtain ⟨edge, _, _, area⟩ := fort
  have different : wk.1.val ≠ ps.1.val ∨ wk.2.val ≠ (promotionSquare σ ps.1).2.val := by
    by_cases file : wk.1.val = ps.1.val
    · right; intro rank; exact away (Prod.ext (Fin.ext file) (Fin.ext rank))
    · exact Or.inl file
  cases σ <;> rcases edge with edge | edge <;> rcases area with ⟨rank, files⟩ | ⟨rank, files⟩ <;>
    simp only [height, promotionSquare, dInf, absDiff] at far rank files different ⊢ <;> omega

/-- With the pawn below the seventh rank, an orthogonal corner escape remains in the fortress. -/
theorem fortress_escape {σ : Colour} {sk ps : Square}
    (edge : ps.1.val = 0 ∨ ps.1.val = 7) (low : height σ ps ≤ 5)
    (positive : 1 ≤ height σ ps) (far : 2 ≤ dInf sk (promotionSquare σ ps.1)) :
    ∃ t, dInf (promotionSquare σ ps.1) t = 1 ∧ 2 ≤ dInf sk t ∧
      t ≠ ps ∧ ¬ PawnSees σ ps t ∧ RookFortress σ ps t := by
  let h : Square := (if ps.1.val = 0 then 1 else 6, (promotionSquare σ ps.1).2)
  let v : Square := (ps.1, match σ with | .white => 6 | .black => 1)
  have hd : dInf (promotionSquare σ ps.1) h = 1 := by
    cases σ <;> rcases edge with edge | edge <;> simp [h, promotionSquare, dInf, absDiff, edge] <;> decide
  have vd : dInf (promotionSquare σ ps.1) v = 1 := by
    cases σ <;> simp [v, promotionSquare, dInf, absDiff] <;> decide
  have hf : RookFortress σ ps h := by
    refine ⟨edge, positive, by omega, Or.inl ⟨?_, ?_⟩⟩
    · cases σ <;> rfl
    · rcases edge with edge | edge <;> simp [h, absDiff, edge] <;> decide
  have vf : RookFortress σ ps v := by
    refine ⟨edge, positive, by omega, Or.inr ⟨?_, rfl⟩⟩
    cases σ <;> rfl
  have hn : h ≠ ps := by
    intro same
    have rank := congrArg (height σ) same
    have hh : height σ h = 7 := by cases σ <;> rfl
    omega
  have vn : v ≠ ps := by
    intro same
    have rank := congrArg (height σ) same
    have vv : height σ v = 6 := by cases σ <;> rfl
    omega
  have ha : ¬ PawnSees σ ps h := by
    cases σ <;> simp only [PawnSees, dy, forward, height, h, promotionSquare] at low ⊢ <;> omega
  have va : ¬ PawnSees σ ps v := by
    simp [PawnSees, dx, v]
  by_cases safe : 2 ≤ dInf sk h
  · exact ⟨h, hd, safe, hn, ha, hf⟩
  · refine ⟨v, vd, ?_, vn, va, vf⟩
    cases σ <;> rcases edge with edge | edge <;>
      simp [h, v, promotionSquare, dInf, absDiff, edge] at safe far ⊢ <;> omega

private def FortressRegion (σ : Colour) (q : Position) : Prop :=
  (∃ sk ps wk, IsKPK q σ sk ps wk ∧ 2 ≤ dInf sk wk ∧ RookFortress σ ps wk) ∨
    DeadK q ∨ (q.turn = σ.opp ∧ ∃ r, Legal q r ∧ DeadK r)

private theorem fortress_strong_step {q r : Position} {σ : Colour}
    (region : FortressRegion σ q) (turn : q.turn = σ) (legal : Legal q r) :
    FortressRegion σ r := by
  rcases region with ⟨sk, ps, wk, h, far, fort⟩ | dead | ⟨wrong, _⟩
  · rcases strong_cases h turn legal with ⟨t, hm, _⟩ |
        ⟨m, _, src, push, promo, hm, nextTurn⟩
    · exact Or.inl ⟨t, ps, wk, hm, LoneKing.kings_apart_after (by decide) hm legal, fort⟩
    · have files : m.dst.1 = ps.1 := (push_files push).symm
      cases pro : m.promo with
      | none =>
        simp only [pro] at hm
        have notLast : height σ m.dst ≠ 7 := by
          apply (promo_none_iff σ ps m.dst).mp
          simpa only [promoOK, pro] using promo
        have advance := push_strict push
        have ceiling := height_le σ m.dst
        have nextFort : RookFortress σ m.dst wk := by
          refine ⟨?_, by have := fort.2.1; omega, by omega, ?_⟩
          · simpa only [files] using fort.1
          · simpa only [files] using fort.2.2.2
        exact Or.inl ⟨sk, m.dst, wk, hm,
          LoneKing.kings_apart_after (by decide) hm legal, nextFort⟩
      | some k =>
        simp only [pro] at hm
        have lastHeight : height σ m.dst = 7 := by
          apply (promo_some_iff σ ps m.dst k).mp
          simpa only [promoOK, pro] using promo
        have same : m.dst = promotionSquare σ ps.1 := by
          apply Prod.ext
          · exact files
          · apply Fin.ext
            cases σ <;> simp only [height, promotionSquare] at lastHeight ⊢ <;> omega
        have away : wk ≠ promotionSquare σ ps.1 := by
          intro equal
          have occupied := hm.2.2.1
          exact occupied (same.trans equal.symm)
        obtain ⟨adjacent, unprotected⟩ := fortress_return fort far away
        have nk : k.toKind ≠ .king := by cases k <;> decide
        obtain ⟨u, capture, w, b, kk⟩ := LoneKing.unprotected_capture nk hm nextTurn
          (by rw [same]; exact adjacent) (by rw [same]; exact unprotected)
        exact Or.inr (Or.inr ⟨nextTurn, u, capture, dead_of_legal_into_KK capture kk⟩)
  · exact Or.inr (Or.inl (fun ⟨t, reach, mate⟩ => dead ⟨t, reachK_cons legal reach, mate⟩))
  · exact False.elim (opp_ne σ (turn.symm.trans wrong))

private theorem fortress_weak_choice {q : Position} {σ : Colour} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (turn : q.turn = σ.opp) (far : 2 ≤ dInf sk wk)
    (fort : RookFortress σ ps wk) (moves : ∃ r, Legal q r) :
    ∃ r, Legal q r ∧ FortressRegion σ r := by
  by_cases atCorner : wk = promotionSquare σ ps.1
  · by_cases seventh : height σ ps = 6
    · have corner : CornerBlocked σ ps wk := by
        refine ⟨?_, fort.1, seventh, ?_⟩
        · rw [atCorner]; rfl
        · rw [atCorner]; exact promotion_square_height σ ps.1
      by_cases protect : dInf sk ps = 1
      · exact False.elim (corner_protected_no_moves h turn far corner protect moves)
      · have zero : dInf sk ps ≠ 0 := fun e => h.1 (dInf_eq_zero_iff.mp e)
        obtain ⟨r, legal, w, b, kk⟩ := LoneKing.unprotected_capture
          (by decide : PieceType.pawn ≠ .king) h turn (corner_adjacent corner) (by omega)
        exact ⟨r, legal, Or.inr (Or.inl (dead_of_legal_into_KK legal kk))⟩
    · have low : height σ ps ≤ 5 := by have := fort.2.2.1; omega
      obtain ⟨t, step, safe, notPawn, notAttack, nextFort⟩ :=
        fortress_escape fort.1 low fort.2.1 (by rwa [← atCorner])
      obtain ⟨r, legal, hm, _⟩ := weak_move h turn
        (by rwa [← atCorner] at step) notPawn safe notAttack
      exact ⟨r, legal, Or.inl ⟨sk, ps, t, hm, safe, nextFort⟩⟩
  · obtain ⟨step, safe⟩ := fortress_return fort far atCorner
    have notPawn : promotionSquare σ ps.1 ≠ ps := by
      intro same
      have rank := congrArg (height σ) same
      have last := promotion_square_height σ ps.1
      have low := fort.2.2.1
      omega
    have notAttack : ¬ PawnSees σ ps (promotionSquare σ ps.1) := by
      simp [PawnSees, dx, promotionSquare]
    obtain ⟨r, legal, hm, _⟩ := weak_move h turn step notPawn safe notAttack
    have nextFort : RookFortress σ ps (promotionSquare σ ps.1) :=
      ⟨fort.1, fort.2.1, fort.2.2.1,
        Or.inl ⟨promotion_square_height σ ps.1, by simp [promotionSquare, absDiff]⟩⟩
    exact ⟨r, legal, Or.inl ⟨sk, ps, _, hm, safe, nextFort⟩⟩

/-- General rook-pawn fortress, for every pawn rank, both colours, both edge
files and either turn. Capturable promotions are retained as explicit exits. -/
theorem fresh_rook_fortress_draw {q : Position} {σ : Colour} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk)
    (fort : RookFortress σ ps wk) :
    FreshGame.Hold σ (FreshGame.fresh q) ∧ FreshGame.Hold σ.opp (FreshGame.fresh q) := by
  refine ⟨fresh_strong_hold h fresh, ?_⟩
  apply FreshGame.hold_of_invariant σ.opp (fun s => FortressRegion σ s.board)
  · intro s region goal
    rcases region with ⟨a, p, b, hm, far, _⟩ | dead | ⟨_, r, legal, _⟩
    · exact not_mated hm far goal.2
    · exact dead ⟨s.board, ReachK.refl _, goal.2⟩
    · exact goal.2.2 ⟨r, legal⟩
  · intro s t region notTurn actual
    have turn : s.board.turn = σ := by
      rcases colour_cases σ s.board.turn with strong | weak
      · exact strong
      · exact False.elim (notTurn weak)
    exact fortress_strong_step region turn (FreshGame.step_legal actual)
  · intro s region ongoing turn
    have choice : ∃ r, Legal s.board r ∧ FortressRegion σ r := by
      rcases region with ⟨a, p, b, hm, far, fortress⟩ | dead | ⟨_, r, legal, dead⟩
      · exact fortress_weak_choice hm turn far fortress ongoing.2.1
      · exact False.elim (ongoing.1 dead)
      · exact ⟨r, legal, Or.inr (Or.inl dead)⟩
    obtain ⟨r, legal, next⟩ := choice
    obtain ⟨t, actual, endpoint⟩ := FreshGame.layer.reply_complete ongoing legal
    refine ⟨t, actual, ?_⟩
    change t.board = r at endpoint
    rw [endpoint]; exact next
  · exact Or.inl ⟨sk, ps, wk, h, fresh.kings, fort⟩

/-- A defending king already on a rook pawn's promotion corner holds at every rank. -/
theorem fresh_rook_corner_draw {q : Position} {σ : Colour} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk)
    (edge : ps.1.val = 0 ∨ ps.1.val = 7) (corner : wk = promotionSquare σ ps.1) :
    FreshGame.Hold σ (FreshGame.fresh q) ∧ FreshGame.Hold σ.opp (FreshGame.fresh q) := by
  apply fresh_rook_fortress_draw h fresh
  have low := fresh.pawnLower
  have high := fresh.pawnUpper
  refine ⟨edge, ?_, ?_, Or.inl ⟨?_, ?_⟩⟩
  · cases σ <;> simp only [height] <;> omega
  · cases σ <;> simp only [height] <;> omega
  · rw [corner]; exact promotion_square_height σ ps.1
  · simp [corner, promotionSquare, absDiff]

end EndgameChess.Rules.KPK
