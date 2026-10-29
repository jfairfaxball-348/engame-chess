import EndgameChess.Rules.KPK.PromotionHistory
import EndgameChess.Rules.FreshGame.InvariantHolding

namespace EndgameChess.Rules.KPK
open EndgameChess.KK

/-- Rook pawn on its seventh rank, with the weak king on its promotion square. -/
def CornerBlocked (σ : Colour) (ps wk : Square) : Prop :=
  ps.1 = wk.1 ∧ (ps.1.val = 0 ∨ ps.1.val = 7) ∧ height σ ps = 6 ∧ height σ wk = 7

theorem corner_adjacent {σ : Colour} {ps wk : Square} (corner : CornerBlocked σ ps wk) :
    dInf wk ps = 1 := by
  obtain ⟨files, _, hp, hw⟩ := corner
  cases σ <;> simp only [height, dInf, absDiff, files] at hp hw ⊢ <;> omega

/-- A pawn cannot move through the king on its promotion square. -/
theorem corner_no_push {q : Position} {σ : Colour} {sk ps wk t : Square}
    (h : IsKPK q σ sk ps wk) (corner : CornerBlocked σ ps wk) : ¬ Push q σ ps t := by
  intro push
  have advance := push_strict push
  have ceiling := height_le σ t
  have files := push_files push
  have rank : t.2 = wk.2 := by
    apply Fin.ext
    have hp := corner.2.2.1
    have hw := corner.2.2.2
    cases σ <;> simp only [height] at advance ceiling hp hw <;> omega
  have same : t = wk := Prod.ext (files.symm.trans corner.1) rank
  have occupied : q.board wk = some ⟨σ.opp, .king⟩ := by
    rw [h.2.2.2]; exact LoneKing.board_wk h.2.1 h.2.2.1
  have empty := push.2.1
  rw [same, occupied] at empty
  cases empty

/-- Protecting this blocked pawn stalemates the corner king. -/
theorem corner_protected_no_moves {q : Position} {σ : Colour} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (ht : q.turn = σ.opp) (_far : 2 ≤ dInf sk wk)
    (corner : CornerBlocked σ ps wk) (protect : dInf sk ps = 1) : ¬ ∃ r, Legal q r := by
  rintro ⟨r, legal⟩
  obtain ⟨t, material, _, step⟩ := LoneKing.safe_reply h ht (Or.inr protect) legal
  have nextFar := LoneKing.kings_apart_after (by decide) material legal
  have noAttack : ¬ PawnSees σ ps t := by
    intro attack
    have check := (weak_check material).mpr (Or.inr attack)
    have safe := legal_mover_safe legal
    rw [ht, check] at safe
    cases safe
  have distinct := material.2.2.1
  obtain ⟨files, edge, hp, hw⟩ := corner
  have neCoords : ps.1.val ≠ t.1.val ∨ ps.2.val ≠ t.2.val := by
    by_cases x : ps.1.val = t.1.val
    · right; intro y; exact distinct (Prod.ext (Fin.ext x) (Fin.ext y))
    · exact Or.inl x
  cases σ <;> rcases edge with edge | edge <;>
    simp only [height, PawnSees, dy, dx, forward, dInf, absDiff] at _far protect nextFar step noAttack hp hw <;>
    omega

private def CornerRegion (σ : Colour) (q : Position) : Prop :=
  (∃ sk ps wk, IsKPK q σ sk ps wk ∧ 2 ≤ dInf sk wk ∧ CornerBlocked σ ps wk) ∨ DeadK q

private theorem corner_strong_step {σ : Colour} {q r : Position}
    (region : CornerRegion σ q) (turn : q.turn = σ) (legal : Legal q r) : CornerRegion σ r := by
  rcases region with ⟨sk, ps, wk, h, _, corner⟩ | dead
  · rcases strong_cases h turn legal with ⟨t, material, _⟩ | ⟨m, _, _, push, _⟩
    · exact Or.inl ⟨t, ps, wk, material,
        LoneKing.kings_apart_after (by decide) material legal, corner⟩
    · exact False.elim (corner_no_push h corner push)
  · exact Or.inr (fun ⟨t, reach, mate⟩ => dead ⟨t, reachK_cons legal reach, mate⟩)

/-- A blocked seventh-rank rook pawn is drawn for either turn and colour.
The defender captures an unprotected pawn; protection instead gives stalemate. -/
theorem fresh_corner_draw {q : Position} {σ : Colour} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk)
    (corner : CornerBlocked σ ps wk) :
    FreshGame.Hold σ (FreshGame.fresh q) ∧ FreshGame.Hold σ.opp (FreshGame.fresh q) := by
  refine ⟨fresh_strong_hold h fresh, ?_⟩
  apply FreshGame.hold_of_invariant σ.opp (fun s => CornerRegion σ s.board)
  · intro s region goal
    rcases region with ⟨a, p, b, hm, far, _⟩ | dead
    · exact not_mated hm far goal.2
    · exact dead ⟨s.board, ReachK.refl _, goal.2⟩
  · intro s t region notTurn actual
    have turn : s.board.turn = σ := by
      rcases colour_cases σ s.board.turn with strong | weak
      · exact strong
      · exact False.elim (notTurn weak)
    exact corner_strong_step region turn (FreshGame.step_legal actual)
  · intro s region ongoing turn
    rcases region with ⟨a, p, b, hm, far, corner⟩ | dead
    · by_cases protect : dInf a p = 1
      · exact False.elim (corner_protected_no_moves hm turn far corner protect ongoing.2.1)
      · have positive : dInf a p ≠ 0 := fun e => hm.1 (dInf_eq_zero_iff.mp e)
        have unprotected : 2 ≤ dInf a p := by omega
        obtain ⟨r, legal, w, b', kk⟩ := LoneKing.unprotected_capture
          (by decide : PieceType.pawn ≠ .king) hm turn (corner_adjacent corner) unprotected
        obtain ⟨t, actual, endpoint⟩ := FreshGame.layer.reply_complete ongoing legal
        refine ⟨t, actual, Or.inr ?_⟩
        change t.board = r at endpoint
        rw [endpoint]; exact dead_of_legal_into_KK legal kk
    · exact False.elim (ongoing.1 dead)
  · exact Or.inl ⟨sk, ps, wk, h, fresh.kings, corner⟩

end EndgameChess.Rules.KPK
