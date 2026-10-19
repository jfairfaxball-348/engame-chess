import EndgameChess.Rules.KRKForcing.Safety
import EndgameChess.Rules.ForceMate

/-! S030 / EC-C019: an unprotected adjacent rook is legally capturable. -/
namespace EndgameChess.Rules
open EndgameChess.KK

theorem krk_unprotected_capture {q : Position} {σ : Colour} {sk rs wk : Square}
    (hk : IsKRK q σ sk rs wk) (ht : q.turn = σ.opp)
    (ha : dInf wk rs = 1) (hf : 2 ≤ dInf sk rs) :
    ∃ r, Legal q r ∧ ∃ w b, IsKK r w b := by
  obtain ⟨h12, h13, h23, hb⟩ := hk
  let m : Move := ⟨wk, rs, none⟩
  have hsrc : q.board m.src = some ⟨q.turn, .king⟩ := by
    rw [hb, ht]; exact krkBoard_wk h13 h23
  have hp : isPseudo q m = true := by
    rw [isPseudo_of_king hsrc]
    have hd : q.board m.dst = some ⟨σ, .rook⟩ := by rw [hb]; exact krkBoard_rs h12
    simp [targetOK, hd, ht, m, kingGeom_iff, ha]
    exact fun h => opp_ne σ h
  have hbp := play_board_simple hsrc (by decide) rfl (fun _ => ha)
  have hkk : ∃ w b, IsKK (play q m) w b ∧ 2 ≤ dInf w b := by
    cases σ with
    | white =>
      refine ⟨sk, rs, ⟨h12, ?_⟩, hf⟩
      rw [hbp]; funext x; rw [hb, ht]; unfold krkBoard kkBoard
      by_cases e1 : x = rs
      · subst e1; simp [m, Ne.symm h12, Colour.opp]
      · by_cases e2 : x = wk
        · subst e2; simp [m, e1, Ne.symm h13]
        · simp [m, e1, e2]
    | black =>
      refine ⟨rs, sk, ⟨Ne.symm h12, ?_⟩, by rwa [dInf_comm]⟩
      rw [hbp]; funext x; rw [hb, ht]; unfold krkBoard kkBoard
      by_cases e1 : x = rs
      · subst e1; simp [m, Colour.opp]
      · by_cases e2 : x = wk
        · subst e2; simp [m, e1, Ne.symm h13]
        · by_cases e3 : x = sk <;> simp [m, e1, e2, e3, h12, h13]
  obtain ⟨w, b, hkk, hdist⟩ := hkk
  have hc : inCheck (play q m) q.turn = false := by
    cases he : inCheck (play q m) q.turn
    · rfl
    · have hh : inCheck (ofKK ⟨w, b, (play q m).turn⟩) q.turn = true := by
        rw [inCheck_of_board (p := ofKK ⟨w, b, (play q m).turn⟩) (q := play q m)
          (by exact hkk.2.symm)]
        exact he
      have := (inCheck_ofKK (a := ⟨w, b, (play q m).turn⟩) hkk.1 q.turn).1 hh
      dsimp only at this
      omega
  exact ⟨play q m, legal_of_pseudo hp hc, w, b, hkk⟩

theorem krk_force_weak_safe {q : Position} {σ : Colour} {sk rs wk : Square}
    (hk : IsKRK q σ sk rs wk) (ht : q.turn = σ.opp)
    (hw : ForceMate σ q) : SafeRook sk rs wk := by
  classical
  by_cases hn : SafeRook sk rs wk
  · exact hn
  apply False.elim
  have hd0 : dInf rs wk ≠ 0 := fun h => hk.2.2.1 (dInf_eq_zero_iff.1 h)
  have hs0 : dInf sk rs ≠ 0 := fun h => hk.1 (dInf_eq_zero_iff.1 h)
  have ha : dInf wk rs = 1 := by
    simp only [SafeRook, not_or] at hn
    rw [dInf_comm]; omega
  have hf : 2 ≤ dInf sk rs := by
    simp only [SafeRook, not_or] at hn; omega
  obtain ⟨r, hl, w, b, hkk⟩ := krk_unprotected_capture hk ht ha hf
  exact dead_reply_not_forceMate ht hl (dead_of_legal_into_KK hl hkk) hw

end EndgameChess.Rules
