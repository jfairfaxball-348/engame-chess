import EndgameChess.Rules.KRKLive.Main

/-! EC-C010: a protected rook strictly above its king confines the lone king above
its rank through every kernel-legal reply. Includes completeness for all such replies.
Paper proof: proofs/EC-C010_KRK_CONFINEMENT.md. -/
namespace EndgameChess.Rules
open EndgameChess.KK

/-- A protected separating rank. This invariant does not assert a legal reply exists. -/
def ProtectedRank (sk rs wk : Square) : Prop :=
  dInf sk rs = 1 ∧ sk.2.val < rs.2.val ∧ rs.2.val < wk.2.val

/-- Completeness for all legal lone-king replies when the strong king protects the rook.
The cooperative model omits captures; protection is what justifies that omission here. -/
theorem krk_protected_reply {q r : Position} {σ : Colour} {sk rs wk : Square}
    (hk : IsKRK q σ sk rs wk) (ht : q.turn = σ.opp) (hp : dInf sk rs = 1)
    (hl : Legal q r) : ∃ t, Matches r σ ⟨sk, rs, t, true⟩ ∧
      StepM ⟨sk, rs, wk, false⟩ ⟨sk, rs, t, true⟩ := by
  obtain ⟨h12, h13, h23, hb⟩ := hk
  obtain ⟨m, hm, rfl⟩ := hl
  have hps : isPseudo q m = true := by
    unfold isLegal at hm; simp only [Bool.and_eq_true] at hm; exact hm.1
  have hchk := not_inCheck_after_legal hm
  obtain ⟨pc, hpc, hcol⟩ := own_of_isPseudo hps
  rw [hb] at hpc
  rcases krkBoard_some hpc with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨esrc, rfl⟩
  · rw [ht] at hcol; exact False.elim (opp_ne _ hcol)
  · rw [ht] at hcol; exact False.elim (opp_ne _ hcol)
  · have hsrc : q.board m.src = some ⟨q.turn, .king⟩ := by
      rw [hb, ht, esrc]; exact krkBoard_wk h13 h23
    have hnc : canCastle q m = false := by
      apply canCastle_false_of_noRook
      intro s hs
      rw [hb, ht] at hs
      rcases krkBoard_some hs with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩
      · simp at h
      · simp only [Piece.mk.injEq] at h; exact opp_ne _ h.1.symm
      · simp at h
    rw [isPseudo_of_king hsrc, hnc] at hps
    simp only [Bool.or_false, Bool.and_eq_true, Option.isNone_iff_eq_none] at hps
    obtain ⟨htg, hpro, hg⟩ := hps
    have hd : dInf m.src m.dst = 1 := kingGeom_iff.1 hg
    rw [esrc] at hd
    have hdk : m.dst ≠ sk := by
      intro e
      have := (targetOK_some htg (by rw [hb, e]; exact krkBoard_sk)).2
      exact this rfl
    have hbp := play_board_simple hsrc (by decide) hpro (fun _ => by rw [esrc]; exact hd)
    rw [ht] at hchk
    have hcap : m.dst ≠ rs := by
      intro e
      have hcheck : inCheck (play q m) σ.opp = true := by
        rw [inCheck_iff]
        refine ⟨m.dst, by rw [hbp, ht]; simp, ?_⟩
        rw [attacked_iff, opp_opp]
        refine ⟨sk, ⟨σ, .king⟩, ?_, rfl, ?_⟩
        · rw [hbp, hb, ht, esrc]
          simp [Ne.symm hdk, h13, krkBoard_sk]
        · simpa [attacksFrom, kingGeom_iff, e] using hp
      rw [hcheck] at hchk; cases hchk
    have hb' : (play q m).board = krkBoard σ sk rs m.dst := by
      rw [hbp]; funext x; rw [hb, ht, esrc]; unfold krkBoard
      by_cases e1 : x = m.dst
      · subst e1; simp [hdk, hcap]
      · by_cases e2 : x = wk
        · subst e2; simp [e1, Ne.symm h13, Ne.symm h23]
        · simp [e1, e2]
    have hn : ¬ (dInf sk m.dst = 1 ∨ RookSees rs m.dst sk m.dst) := by
      intro hc
      rw [(inCheck_weak_krk h12 (Ne.symm hdk) (Ne.symm hcap) hb').2 hc] at hchk
      cases hchk
    have hfar : 2 ≤ dInf sk m.dst := by
      have h0 : dInf sk m.dst ≠ 0 := fun h => hdk (dInf_eq_zero_iff.1 h).symm
      have h1 : dInf sk m.dst ≠ 1 := fun h => hn (Or.inl h)
      omega
    refine ⟨m.dst, ⟨⟨h12, Ne.symm hdk, Ne.symm hcap, hb'⟩, ?_⟩,
      StepM.lone hd hcap hfar (fun h => hn (Or.inr h))⟩
    simp only [ite_true]; rw [play_turn, ht, opp_opp]

/-- The rook's rank cannot be crossed by a one-square noncapturing safe reply when
its strong king lies strictly below the rook's rank. -/
theorem rook_rank_barrier {sk rs wk t : Square}
    (hs : sk.2.val < rs.2.val) (hw : rs.2.val < wk.2.val)
    (hd : dInf wk t = 1) (hne : t ≠ rs) (hn : ¬ RookSees rs t sk t) :
    rs.2.val < t.2.val := by
  by_cases h : rs.2.val < t.2.val
  · exact h
  have hy : t.2.val = rs.2.val := by
    simp only [dInf, absDiff] at hd
    omega
  apply False.elim
  apply hn
  refine ⟨⟨?_, Or.inr hy.symm⟩, ?_, not_onSeg_end _ _⟩
  · rw [← ne_iff_coords]
    exact Ne.symm hne
  · simp only [OnSeg]
    omega

/-- Every legal defender reply preserves the protected separating rank. No nonemptiness,
progress, mate bound or complete forcing strategy is asserted. -/
theorem krk_protected_rank_reply {q r : Position} {σ : Colour} {sk rs wk : Square}
    (hk : IsKRK q σ sk rs wk) (ht : q.turn = σ.opp)
    (hi : ProtectedRank sk rs wk) (hl : Legal q r) :
    ∃ t, Matches r σ ⟨sk, rs, t, true⟩ ∧
      StepM ⟨sk, rs, wk, false⟩ ⟨sk, rs, t, true⟩ ∧ ProtectedRank sk rs t := by
  obtain ⟨t, hm, hstep⟩ := krk_protected_reply hk ht hi.1 hl
  refine ⟨t, hm, hstep, hi.1, hi.2.1, ?_⟩
  cases hstep with
  | lone hd hne _ hn => exact rook_rank_barrier hi.2.1 hi.2.2 hd hne hn

/-- Raising the rook above its old rank while its king stays below loses protection.
Thus a forcing strategy needs a broader safety invariant than ProtectedRank alone. -/
theorem protected_rank_raise_unprotected {sk rs wk t : Square}
    (hi : ProtectedRank sk rs wk) (hr : rs.2.val < t.2.val) : 2 ≤ dInf sk t := by
  have hs := hi.2.1
  simp only [dInf, absDiff]
  omega

end EndgameChess.Rules
