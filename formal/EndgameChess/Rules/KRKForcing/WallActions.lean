import EndgameChess.Rules.KRKForcing.RankAdvanceRescue

/-! S029: explicit wall-preserving moves and coordinate orientation. -/
namespace EndgameChess.Rules
open EndgameChess.KK
set_option maxHeartbeats 2000000

def pursuitFile (d : Bool) (s : Square) : Nat := if d then s.1.val else 7 - s.1.val

def wallFarFile (x : Fin 8) : Fin 8 := if 4 ≤ x.val then 0 else 7

def wallWaitFile (r x : Fin 8) : Fin 8 :=
  if 4 ≤ x.val then (if r.val = 0 then 1 else 0)
  else (if r.val = 7 then 6 else 7)

theorem pursuitFile_bound (d : Bool) (s : Square) : pursuitFile d s ≤ 7 := by
  cases d <;> simp only [pursuitFile, Bool.false_eq_true, ↓reduceIte] <;> omega

theorem pursuit_absDiff (d : Bool) (s t : Square) :
    absDiff (pursuitFile d s) (pursuitFile d t) = absDiff s.1.val t.1.val := by
  cases d <;> simp only [pursuitFile, Bool.false_eq_true, ↓reduceIte, absDiff] <;> omega

theorem wall_far_margin (w : Fin 8) : 4 ≤ absDiff (wallFarFile w).val w.val := by
  unfold wallFarFile; split <;> simp only [absDiff] <;> omega

theorem wall_wait_choice (r w : Fin 8) :
    wallWaitFile r w ≠ r ∧ 3 ≤ absDiff (wallWaitFile r w).val w.val := by
  unfold wallWaitFile
  split <;> split <;> simp only [ne_eq, Fin.ext_iff, absDiff] <;> omega

/-- Actual distinct rook tempo: every reply is material preserving, above the
wall and still at least two files from the rook. -/
theorem krk_wall_rook_move {q : Position} {σ : Colour} {sk rs wk nr : Square}
    (hq : Matches q σ ⟨sk, rs, wk, true⟩)
    (hb : sk.2.val < rs.2.val) (hw : rs.2.val < wk.2.val)
    (hy : nr.2 = rs.2) (hne : nr ≠ rs) (hf : 3 ≤ absDiff nr.1.val wk.1.val) :
    ∃ c, Legal q c ∧ Matches c σ ⟨sk, nr, wk, false⟩ ∧ (∃ r, Legal c r) ∧
      ∀ r, Legal c r → ∃ t, Matches r σ ⟨sk, nr, t, true⟩ ∧
        rs.2.val < t.2.val ∧ 2 ≤ absDiff nr.1.val t.1.val ∧
        absDiff t.1.val wk.1.val ≤ 1 ∧
        (wk.2.val = rs.2.val + 1 → rs.2.val + 2 ≤ t.2.val ∨
          (t.2.val = rs.2.val + 1 ∧ absDiff t.1.val wk.1.val = 1)) := by
  have hstep : StepM ⟨sk, rs, wk, true⟩ ⟨sk, nr, wk, false⟩ := by
    refine StepM.rook ?_ ?_ ?_ ?_ ?_ ?_ <;>
      simp only [RookLine, OnSeg, ne_iff_coords, dInf, absDiff] at * <;> omega
  obtain ⟨c, hl, hm⟩ := step_sound hq hstep
  have hgap : sk.2.val + 2 ≤ wk.2.val := by omega
  have hwy : nr.2.val < wk.2.val := by omega
  obtain ⟨t, hs⟩ := barrier_horizontal_reply_exists (sk := sk) (rs := nr) (wk := wk) hgap hwy (by omega)
  obtain ⟨r, hr, _⟩ := step_sound hm hs
  refine ⟨c, hl, hm, ⟨r, hr⟩, fun r hr => ?_⟩
  have hsafe : SafeRook sk nr wk := Or.inl (by
    (try dsimp only at *); simp only [dInf, absDiff] at *; omega)
  obtain ⟨t, hmt, hs, htbar⟩ := krk_safe_rank_reply (sk := sk) (rs := nr) (wk := wk) hm.1 hm.2 hsafe
    (by change sk.2.val < nr.2.val; omega) hwy hr
  try dsimp only at htbar
  refine ⟨t, hmt, by omega, ?_, ?_, ?_⟩
  · cases hs with
    | lone hd _ _ _ => (try dsimp only at *); simp only [dInf, absDiff] at *; omega
  · cases hs with
    | lone hd _ _ _ => (try dsimp only at *); simp only [dInf, absDiff] at *; omega
  · intro hband
    cases hs with
    | lone hd _ _ _ => (try dsimp only at *); simp only [dInf, absDiff] at *; omega

/-- A same-rank legal reply in a lower band must step horizontally. -/
theorem lower_band_reply_shape {sk rs wk t : Square}
    (hb : sk.2.val + 1 = rs.2.val) (hw : wk.2.val = rs.2.val + 1)
    (hs : StepM ⟨sk, rs, wk, false⟩ ⟨sk, rs, t, true⟩) :
    rs.2.val + 2 ≤ t.2.val ∨
      (t.2.val = rs.2.val + 1 ∧ absDiff t.1.val wk.1.val = 1) := by
  cases hs with
  | lone hd hne _ hn =>
    have hbar := rook_rank_barrier (by omega : sk.2.val < rs.2.val)
      (by omega : rs.2.val < wk.2.val) hd hne hn
    (try dsimp only at *); simp only [dInf, absDiff] at *; omega

/-- Construct the physical left/right king step; no kernel symmetry assumed. -/
theorem pursuit_king_step (d : Bool) {sk rs wk : Square}
    (hb : sk.2.val + 1 = rs.2.val) (hw : wk.2.val = rs.2.val + 1)
    (hx : pursuitFile d sk + 2 ≤ pursuitFile d wk) :
    ∃ su, su.2 = sk.2 ∧ pursuitFile d su = pursuitFile d sk + 1 ∧
      StepM ⟨sk, rs, wk, true⟩ ⟨su, rs, wk, false⟩ := by
  cases d
  · let su : Square := (⟨sk.1.val - 1, by omega⟩, sk.2)
    refine ⟨su, rfl, ?_, StepM.king ?_ ?_ ?_⟩ <;>
      dsimp [su, pursuitFile] at * <;>
      (try simp only [dInf, absDiff, ne_iff_coords] at *) <;> omega
  · let su : Square := (⟨sk.1.val + 1, by
        simp only [pursuitFile, ↓reduceIte] at hx; omega⟩, sk.2)
    refine ⟨su, rfl, ?_, StepM.king ?_ ?_ ?_⟩ <;>
      dsimp [su, pursuitFile] at * <;>
      (try simp only [dInf, absDiff, ne_iff_coords] at *) <;> omega

/-- Chasing is used only at offset≥2 and margin≥3. Every non-exit reply
preserves the orientation and the next strong-turn two-file margin. -/
theorem krk_pursuit_king_move (d : Bool) {q : Position} {σ : Colour} {sk rs wk : Square}
    (hq : Matches q σ ⟨sk, rs, wk, true⟩)
    (hb : sk.2.val + 1 = rs.2.val) (hw : wk.2.val = rs.2.val + 1)
    (hx : pursuitFile d sk + 2 ≤ pursuitFile d wk)
    (hf : 3 ≤ absDiff rs.1.val wk.1.val) :
    ∃ su c, su.2 = sk.2 ∧ pursuitFile d su = pursuitFile d sk + 1 ∧ Legal q c ∧
      Matches c σ ⟨su, rs, wk, false⟩ ∧ (∃ r, Legal c r) ∧
      ∀ r, Legal c r → ∃ t, Matches r σ ⟨su, rs, t, true⟩ ∧
        2 ≤ absDiff rs.1.val t.1.val ∧ absDiff t.1.val wk.1.val ≤ 1 ∧
        (rs.2.val + 2 ≤ t.2.val ∨
          (t.2.val = rs.2.val + 1 ∧ absDiff t.1.val wk.1.val = 1)) := by
  obtain ⟨su, hsy, hsx, hs⟩ := pursuit_king_step d hb hw hx
  obtain ⟨c, hl, hm⟩ := step_sound hq hs
  have hgap : su.2.val + 2 ≤ wk.2.val := by omega
  obtain ⟨t, ht⟩ := barrier_horizontal_reply_exists (sk := su) (rs := rs) (wk := wk) hgap (by omega) (by omega : 2 ≤ absDiff rs.1.val wk.1.val)
  obtain ⟨r, hr, _⟩ := step_sound hm ht
  refine ⟨su, c, hsy, hsx, hl, hm, ⟨r, hr⟩, fun r hr => ?_⟩
  have hsafe : SafeRook su rs wk := Or.inl (by (try dsimp only at *); simp only [dInf, absDiff] at *; omega)
  obtain ⟨t, hmt, hstep⟩ := krk_safe_reply (sk := su) (rs := rs) (wk := wk) hm.1 hm.2 hsafe hr
  refine ⟨t, hmt, ?_, ?_, lower_band_reply_shape (sk := su) (rs := rs) (wk := wk) (by omega) hw hstep⟩
  all_goals cases hstep with
  | lone hd _ _ _ => (try dsimp only at *); simp only [dInf, absDiff] at *; omega

end EndgameChess.Rules
