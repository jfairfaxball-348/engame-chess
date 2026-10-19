import EndgameChess.Rules.KRKForcing.LowerPursuit

/-! EC-C018: closed clock-free forcing from a strictly separating rank wall. -/
namespace EndgameChess.Rules
open EndgameChess.KK
set_option maxHeartbeats 3000000

/-- Strong turn, exact KRK and strict rank separation suffice. A threatened rook
is repaired on the strong turn, not left for an extra defending move. -/
theorem krk_rank_wall_force {q : Position} {σ : Colour} {sk rs wk : Square}
    (hq : Matches q σ ⟨sk, rs, wk, true⟩)
    (hb : sk.2.val < rs.2.val) (hw : rs.2.val < wk.2.val) : ForceMate σ q := by
  suffices outer : ∀ n, ∀ {q : Position} {sk rs wk : Square},
      Matches q σ ⟨sk, rs, wk, true⟩ → sk.2.val < rs.2.val → rs.2.val < wk.2.val →
      7 - rs.2.val = n → ForceMate σ q by
    exact outer _ hq hb hw rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n rankIH =>
    have inner : ∀ g, ∀ {q : Position} {sk rs wk : Square},
        Matches q σ ⟨sk, rs, wk, true⟩ → sk.2.val < rs.2.val → rs.2.val < wk.2.val →
        7 - rs.2.val = n → rs.2.val - sk.2.val = g → ForceMate σ q := by
      intro g
      induction g using Nat.strongRecOn with
      | ind g gapIH =>
        intro q sk rs wk hq hb hw hrank hgap
        have upper {p : Position} {s r w : Square}
            (hp : Matches p σ ⟨s, r, w, true⟩)
            (hsy : s.2.val = sk.2.val) (hry : r.2.val = rs.2.val)
            (hup : r.2.val + 2 ≤ w.2.val) (hf : 2 ≤ absDiff r.1.val w.1.val) :
            ForceMate σ p := by
          obtain ⟨nr, c, _, hny, hl, hm, hne, _, hall⟩ :=
            krk_rank_advance_rescue (sk := s) (rs := r) (wk := w) hp.1 hp.2 (by omega) hup hf
          apply forceMate_choose hp.2 hl
          apply forceMate_defend hm.2 hne
          intro v hv
          obtain ⟨t, hmt, hdone | ⟨sr, d, hsr, _, hld, hmd, hned, halld⟩⟩ := hall v hv
          · exact rankIH (7 - nr.2.val) (by omega) hmt hdone.1 hdone.2.1 rfl
          · apply forceMate_choose hmt.2 hld
            apply forceMate_defend hmd.2 hned
            intro z hz
            obtain ⟨u, hmu, hbar⟩ := halld z hz
            exact rankIH (7 - sr.2.val) (by omega) hmu hbar.1 hbar.2.1 rfl
        have ready {p : Position} {r w : Square}
            (hp : Matches p σ ⟨sk, r, w, true⟩) (hry : r.2.val = rs.2.val)
            (hwr : r.2.val < w.2.val) (hf : 2 ≤ absDiff r.1.val w.1.val) :
            ForceMate σ p := by
          by_cases hup : r.2.val + 2 ≤ w.2.val
          · exact upper hp rfl hry hup hf
          have hwlow : w.2.val = r.2.val + 1 := by omega
          by_cases hcatch : sk.2.val + 2 ≤ r.2.val
          · let su : Square := (sk.1, ⟨sk.2.val + 1, by omega⟩)
            have hsu : su.2.val = sk.2.val + 1 := rfl
            have hs : StepM ⟨sk, r, w, true⟩ ⟨su, r, w, false⟩ := by
              refine StepM.king ?_ ?_ ?_ <;> dsimp [su] <;>
                simp only [dInf, absDiff, ne_iff_coords] at * <;> omega
            obtain ⟨c, hl, hm⟩ := step_sound hp hs
            have hbelow : su.2.val < r.2.val := by omega
            have hgap2 : su.2.val + 2 ≤ w.2.val := by omega
            obtain ⟨t, ht⟩ := barrier_horizontal_reply_exists (sk := su) (rs := r) (wk := w)
              hgap2 hwr hf
            obtain ⟨v, hv, _⟩ := step_sound hm ht
            apply forceMate_choose hp.2 hl
            apply forceMate_defend hm.2 ⟨v, hv⟩
            intro z hz
            have hsafe : SafeRook su r w := Or.inl (by simp only [dInf, absDiff] at *; omega)
            obtain ⟨t, hmt, _, hbar⟩ := krk_safe_rank_reply (sk := su) (rs := r) (wk := w)
              hm.1 hm.2 hsafe hbelow hwr hz
            exact gapIH (r.2.val - su.2.val) (by omega) hmt hbelow hbar (by omega) rfl
          have hlow : sk.2.val + 1 = r.2.val := by omega
          have hexit : LowerExitWins σ r.2.val := by
            intro z s rr u hm hsY hrY hfile he
            rcases he with hup' | ⟨huY, hfileeq⟩
            · exact upper hm (by omega) (by omega) (by omega) hfile
            · have ho : Opposed s u := ⟨hfileeq, by omega⟩
              obtain ⟨c, hl, hmc, hmate | ⟨hne, hall⟩⟩ :=
                krk_opposition_check_two hm ho hfile (by omega)
              · exact forceMate_choose hm.2 hl (forceMate_of_goal hmate)
              · apply forceMate_choose hm.2 hl
                apply forceMate_defend hmc.2 hne
                intro v hv
                obtain ⟨t, hmt, hty, _⟩ := hall v hv
                have hnew : (checkRook rr u).2.val = rs.2.val + 1 := by
                  change u.2.val = rs.2.val + 1
                  omega
                apply rankIH (7 - (checkRook rr u).2.val) (by omega) hmt
                · change s.2.val < u.2.val
                  omega
                · change u.2.val < t.2.val
                  omega
                · rfl
          exact krk_lower_band_force_of_exits hexit hp hlow rfl hwlow hf
        by_cases hf : 2 ≤ absDiff rs.1.val wk.1.val
        · exact ready hq rfl hw hf
        let nr : Square := (wallFarFile wk.1, rs.2)
        have hfar : 4 ≤ absDiff nr.1.val wk.1.val := wall_far_margin wk.1
        have hnr : nr ≠ rs := by
          intro he
          rw [he] at hfar
          omega
        obtain ⟨c, hl, hm, hne, hall⟩ := krk_wall_rook_move hq hb hw
          (nr := nr) rfl hnr (by omega)
        apply forceMate_choose hq.2 hl
        apply forceMate_defend hm.2 hne
        intro v hv
        obtain ⟨t, hmt, hbar, hfile, _, _⟩ := hall v hv
        exact ready hmt rfl hbar hfile
    intro q sk rs wk hq hb hw hn
    exact inner _ hq hb hw hn rfl

/-- The proved image family is now included in an actual forced-mate family. -/
theorem krk_phase_image_force {q : Position} {σ : Colour} {sk rs wk : Square}
    (hq : Matches q σ ⟨sk, rs, wk, true⟩) (hi : PhaseImage sk rs wk) :
    ForceMate σ q := by
  obtain ⟨hy, hwy, _, _, _⟩ := hi
  apply krk_rank_wall_force hq <;> omega

end EndgameChess.Rules
