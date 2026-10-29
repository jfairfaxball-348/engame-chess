import EndgameChess.Rules.KPK.Progress
import EndgameChess.Rules.LoneKing.Closure
import EndgameChess.Rules.FreshGame.Winning

namespace EndgameChess.Rules.KPK
open EndgameChess.KK

/-- Closed material region for all descendants, including every promotion. -/
def MaterialRegion (σ : Colour) (q : Position) : Prop :=
  (∃ k sk xs wk, k ≠ .king ∧ LoneKing.Material k q σ sk xs wk ∧
    2 ≤ dInf sk wk ∧ q.castling = noRights) ∨ DeadK q

theorem material_region_step {σ : Colour} {q r : Position}
    (region : MaterialRegion σ q) (legal : Legal q r) : MaterialRegion σ r := by
  rcases region with ⟨k, sk, xs, wk, nk, h, _, rights⟩ | dead
  · have nextRights := noRights_after_legal rights legal
    have enter {k : PieceType} {sk xs wk : Square} (nk : k ≠ .king)
        (material : LoneKing.Material k r σ sk xs wk) : MaterialRegion σ r :=
      Or.inl ⟨k, sk, xs, wk, nk, material,
        LoneKing.kings_apart_after nk material legal, nextRights⟩
    rcases colour_cases σ q.turn with turn | turn
    · by_cases pawn : k = .pawn
      · subst k
        rcases strong_cases h turn legal with ⟨t, hm, _⟩ |
            ⟨m, _, _, _, _, hm, _⟩
        · exact enter (by decide) hm
        · have notKing : (match m.promo with | none => PieceType.pawn | some k => k.toKind) ≠ .king := by
            cases m.promo with
            | none => decide
            | some k => cases k <;> decide
          exact enter notKing hm
      · rcases LoneKing.strong_cases nk pawn h turn rights legal with ⟨t, hm⟩ | ⟨t, hm⟩
        · exact enter nk hm
        · exact enter nk hm
    · rcases LoneKing.weak_cases h turn legal with ⟨t, hm, _⟩ | ⟨w, b, kk⟩
      · exact enter nk hm
      · exact Or.inr (dead_of_legal_into_KK legal kk)
  · exact Or.inr (fun ⟨t, reach, mate⟩ => dead ⟨t, reachK_cons legal reach, mate⟩)

theorem material_region_no_weak_mate {σ : Colour} {q : Position}
    (region : MaterialRegion σ q) : ¬ MateGoal σ.opp q := by
  intro goal
  rcases region with ⟨k, sk, xs, wk, nk, h, far, _⟩ | dead
  · have turn : q.turn = σ := by simpa only [opp_opp] using goal.1
    have check : inCheck q σ = true := by simpa only [turn] using goal.2.1
    have near := (LoneKing.strong_check nk h).mp check
    rw [dInf_comm] at near
    omega
  · exact dead ⟨q, ReachK.refl _, goal.2⟩

/-- Even cooperative legal play, through promotion and capture, cannot mate the pawn side. -/
theorem no_weak_reachable_mate {q r : Position} {σ : Colour} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (far : 2 ≤ dInf sk wk)
    (rights : q.castling = noRights) (reach : ReachK q r) : ¬ MateGoal σ.opp r := by
  have region : MaterialRegion σ r := by
    induction reach with
    | refl => exact Or.inl ⟨.pawn, sk, ps, wk, by decide, h, far, rights⟩
    | tail _ legal ih => exact material_region_step ih legal
  exact material_region_no_weak_mate region

/-- Actual strong-side holding for every fresh legal KPK root. No winning criterion required. -/
theorem fresh_strong_hold {q : Position} {σ : Colour} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk) :
    FreshGame.Hold σ (FreshGame.fresh q) := by
  apply FreshGame.hold_of_safe_reach
  intro r reach
  exact no_weak_reachable_mate h fresh.kings fresh.rights reach

theorem fresh_no_weak_win {q : Position} {σ : Colour} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk) :
    ¬ FreshGame.Win σ.opp (FreshGame.fresh q) :=
  FreshGame.hold_not_win (fresh_strong_hold h fresh)

theorem fresh_no_weak_actual_win {q : Position} {σ : Colour} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk) :
    ¬ FreshGame.ActualWin σ.opp (FreshGame.fresh q) :=
  fun win => fresh_no_weak_win h fresh (FreshGame.actual_win_iff_rule.mp win)

/-- An exposed pawn is a genuine holding branch: the weak king captures into dead KK. -/
theorem fresh_unsafe_weak_hold {q : Position} {σ : Colour} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (ht : q.turn = σ.opp)
    (far : 2 ≤ dInf sk wk) (unsafePawn : ¬ LoneKing.Safe sk ps wk) :
    FreshGame.Hold σ.opp (FreshGame.fresh q) := by
  have h0 : dInf ps wk ≠ 0 := fun e => h.2.2.1 (dInf_eq_zero_iff.mp e)
  have h1 : dInf sk ps ≠ 0 := fun e => h.1 (dInf_eq_zero_iff.mp e)
  have near : dInf wk ps = 1 := by
    simp only [LoneKing.Safe, not_or] at unsafePawn
    rw [dInf_comm]; omega
  have unprotected : 2 ≤ dInf sk ps := by
    simp only [LoneKing.Safe, not_or] at unsafePawn; omega
  obtain ⟨r, legal, w, b, kk⟩ := LoneKing.unprotected_capture
    (by decide : PieceType.pawn ≠ .king) h ht near unprotected
  exact FreshGame.hold_via_dead_reply ht (fun goal => not_mated h far goal.2)
    ⟨r, legal, dead_of_legal_into_KK legal kk⟩

theorem fresh_unsafe_draw {q : Position} {σ : Colour} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk)
    (ht : q.turn = σ.opp) (unsafePawn : ¬ LoneKing.Safe sk ps wk) :
    FreshGame.Hold σ (FreshGame.fresh q) ∧ FreshGame.Hold σ.opp (FreshGame.fresh q) :=
  ⟨fresh_strong_hold h fresh, fresh_unsafe_weak_hold h ht fresh.kings unsafePawn⟩

end EndgameChess.Rules.KPK
