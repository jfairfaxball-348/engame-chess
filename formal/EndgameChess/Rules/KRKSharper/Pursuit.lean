import EndgameChess.Rules.KRKForcing.PursuitGeometry
import EndgameChess.Rules.KRKSharper.Definitions

/-! EC-C043: quantitative lower-band pursuit, conditional only on its explicit exits. -/
namespace EndgameChess.Rules
open EndgameChess.KK
set_option maxHeartbeats 3000000

private theorem sharper_pursuit_file_eq (d : Bool) {s t : Square}
    (h : pursuitFile d s = pursuitFile d t) : s.1.val = t.1.val := by
  cases d <;> simp only [pursuitFile, Bool.false_eq_true, ↓reduceIte] at h <;> omega

private theorem sharper_pursuit_margin_step {a b c : Square} {k : Nat}
    (hf : k + 1 ≤ absDiff a.1.val b.1.val) (hd : absDiff c.1.val b.1.val ≤ 1) :
    k ≤ absDiff a.1.val c.1.val := by
  simp only [absDiff] at *; omega

/-- The only recursive call follows an actual king-file advance. Rook
normalization and the offset-one waiting case are bounded proof branches. -/
theorem krk_oriented_lower_bound_sharper (d : Bool) {σ : Colour} {y E : Nat}
    (hexit : LowerExitBound σ y E) {q : Position} {sk rs wk : Square}
    (hq : Matches q σ ⟨sk, rs, wk, true⟩)
    (hsy : sk.2.val + 1 = y) (hry : rs.2.val = y) (hwy : wk.2.val = y + 1)
    (hf : 2 ≤ absDiff rs.1.val wk.1.val) (hx : pursuitFile d sk < pursuitFile d wk) :
    MateWithin σ (8 * (7 - pursuitFile d sk) - 6 + E) q := by
  suffices h : ∀ n, ∀ {q : Position} {sk rs wk : Square},
      Matches q σ ⟨sk, rs, wk, true⟩ → sk.2.val + 1 = y → rs.2.val = y →
      wk.2.val = y + 1 → 2 ≤ absDiff rs.1.val wk.1.val →
      pursuitFile d sk < pursuitFile d wk → 7 - pursuitFile d sk = n → MateWithin σ (8 * n - 6 + E) q by
    exact h _ hq hsy hry hwy hf hx rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro q sk rs wk hq hsy hry hwy hf hx heq
    have good {p : Position} {r w : Square}
        (hp : Matches p σ ⟨sk, r, w, true⟩) (hry' : r.2.val = y)
        (hwy' : w.2.val = y + 1) (hg : 3 ≤ absDiff r.1.val w.1.val)
        (hxg : pursuitFile d sk + 2 ≤ pursuitFile d w) :
        MateWithin σ (8 * (n - 1) - 6 + E + 2) p := by
      obtain ⟨su, c, hsu, hxu, hl, hm, hne, hall⟩ :=
        krk_pursuit_king_move d hp (by omega) (by omega) hxg hg
      apply mateWithin_pair hp.2 hl hm.2 hne
      intro v hv
      obtain ⟨t, hmt, hft, hunit, hshape⟩ := hall v hv
      have hsyu : su.2.val + 1 = y := by omega
      rcases hshape with hup | ⟨hty, hdx⟩
      · exact mateWithin_mono (hexit hmt hsyu hry' hft (Or.inl (by omega))) (by omega)
      · have hdo : absDiff (pursuitFile d t) (pursuitFile d w) = 1 := by
          rw [pursuit_absDiff]; exact hdx
        have hrel : pursuitFile d su ≤ pursuitFile d t := by
          simp only [absDiff] at hdo; omega
        by_cases he : pursuitFile d su = pursuitFile d t
        · exact mateWithin_mono (hexit hmt hsyu hry' hft (Or.inr ⟨by omega, sharper_pursuit_file_eq d he⟩)) (by omega)
        · have hbound := pursuitFile_bound d sk
          have hboundSu := pursuitFile_bound d su
          have hm : 7 - pursuitFile d su < n := by omega
          exact mateWithin_mono (ih _ hm hmt hsyu hry' (by omega) hft (by omega) rfl) (by omega)
    have wide {p : Position} {r w : Square}
        (hp : Matches p σ ⟨sk, r, w, true⟩) (hry' : r.2.val = y)
        (hwy' : w.2.val = y + 1) (hg : 2 ≤ absDiff r.1.val w.1.val)
        (hxg : pursuitFile d sk + 2 ≤ pursuitFile d w) :
        MateWithin σ (8 * (n - 1) - 6 + E + 6) p := by
      by_cases hthree : 3 ≤ absDiff r.1.val w.1.val
      · exact mateWithin_mono (good hp hry' hwy' hthree hxg) (by omega)
      have htwo : absDiff r.1.val w.1.val = 2 := by omega
      let nr : Square := (wallFarFile w.1, r.2)
      have hfar : 4 ≤ absDiff nr.1.val w.1.val := wall_far_margin w.1
      have hnr : nr ≠ r := by
        intro e
        rw [e] at hfar
        omega
      obtain ⟨c, hl, hm, hne, hall⟩ := krk_wall_rook_move hp
        (by omega) (by omega) (nr := nr) rfl hnr (by omega)
      apply mateWithin_pair hp.2 hl hm.2 hne
      intro v hv
      obtain ⟨t, hmt, _, hft, hunit, hshape⟩ := hall v hv
      have hnry : nr.2.val = y := hry'
      have hthree : 3 ≤ absDiff nr.1.val t.1.val := sharper_pursuit_margin_step hfar hunit
      rcases hshape (by omega) with hup | ⟨hty, hdx⟩
      · exact mateWithin_mono (hexit hmt hsy hnry hft (Or.inl (by omega))) (by omega)
      · have hdo : absDiff (pursuitFile d t) (pursuitFile d w) = 1 := by
          rw [pursuit_absDiff]; exact hdx
        by_cases hx2 : pursuitFile d sk + 2 ≤ pursuitFile d t
        · exact mateWithin_mono (good hmt hnry (by omega) hthree hx2) (by omega)
        have htx : pursuitFile d t = pursuitFile d sk + 1 := by
          simp only [absDiff] at hdo; omega
        have hwx : pursuitFile d w = pursuitFile d sk + 2 := by
          simp only [absDiff] at hdo; omega
        let wr : Square := (wallWaitFile nr.1 t.1, nr.2)
        have hwchoice := wall_wait_choice nr.1 t.1
        have hwr : wr ≠ nr := by
          intro e
          exact hwchoice.1 (congrArg Prod.fst e)
        have hwrmargin : 3 ≤ absDiff wr.1.val w.1.val :=
          pursuit_tempo_return_margin d hwx htx rfl
        obtain ⟨c2, hl2, hm2, hne2, hall2⟩ := krk_wall_rook_move hmt
          (by change sk.2.val < nr.2.val; omega) (by omega)
          (nr := wr) rfl hwr hwchoice.2
        apply mateWithin_pair hmt.2 hl2 hm2.2 hne2
        intro v2 hv2
        obtain ⟨u, hmu, _, hfu, hunit2, hshape2⟩ := hall2 v2 hv2
        have hwry : wr.2.val = y := hnry
        rcases hshape2 (by omega) with hup2 | ⟨huy, hdx2⟩
        · exact mateWithin_mono (hexit hmu hsy hwry hfu (Or.inl (by omega))) (by omega)
        · have hdu : absDiff (pursuitFile d u) (pursuitFile d t) = 1 := by
            rw [pursuit_absDiff]; exact hdx2
          by_cases he : pursuitFile d sk = pursuitFile d u
          · exact mateWithin_mono (hexit hmu hsy hwry hfu (Or.inr ⟨by omega, sharper_pursuit_file_eq d he⟩)) (by omega)
          · have hue : pursuitFile d u = pursuitFile d w := by
              simp only [absDiff] at hdu; omega
            have hue' := sharper_pursuit_file_eq d hue
            have hm3 : 3 ≤ absDiff wr.1.val u.1.val := by rw [hue']; exact hwrmargin
            exact mateWithin_mono (good hmu hwry (by omega) hm3 (by omega)) (by omega)
    by_cases hx2 : pursuitFile d sk + 2 ≤ pursuitFile d wk
    · exact mateWithin_mono (wide hq hry hwy hf hx2) (by have := pursuitFile_bound d wk; omega)
    have hx1 : pursuitFile d wk = pursuitFile d sk + 1 := by omega
    let nr : Square := (wallWaitFile rs.1 wk.1, rs.2)
    have hchoice := wall_wait_choice rs.1 wk.1
    have hnr : nr ≠ rs := by
      intro e
      exact hchoice.1 (congrArg Prod.fst e)
    obtain ⟨c, hl, hm, hne, hall⟩ := krk_wall_rook_move hq
      (by omega) (by omega) (nr := nr) rfl hnr hchoice.2
    apply mateWithin_mono (n := (8 * n - 8 + E) + 2) ?_ (by have := pursuitFile_bound d wk; omega)
    apply mateWithin_pair hq.2 hl hm.2 hne
    intro v hv
    obtain ⟨t, hmt, _, hft, hunit, hshape⟩ := hall v hv
    have hnry : nr.2.val = y := hry
    rcases hshape (by omega) with hup | ⟨hty, hdx⟩
    · exact mateWithin_mono (hexit hmt hsy hnry hft (Or.inl (by omega))) (by omega)
    · have hdo : absDiff (pursuitFile d t) (pursuitFile d wk) = 1 := by
        rw [pursuit_absDiff]; exact hdx
      by_cases he : pursuitFile d sk = pursuitFile d t
      · exact mateWithin_mono (hexit hmt hsy hnry hft (Or.inr ⟨by omega, sharper_pursuit_file_eq d he⟩)) (by omega)
      · have hx2 : pursuitFile d sk + 2 ≤ pursuitFile d t := by
          simp only [absDiff] at hdo; omega
        exact mateWithin_mono (wide hmt hnry (by omega) hft hx2)
          (by have := pursuitFile_bound d t; omega)

end EndgameChess.Rules
