import EndgameChess.Rules.KPK.Coord.SixWin

/-! Every sixth-rank win outside the key squares falls in one of the strategy's classes. -/
namespace EndgameChess.Rules.KPK.Coord

set_option maxHeartbeats 4000000 in
/-- The lone king next to the pawn's file: the king steps beside the pawn. -/
theorem cover_t {a b c e f t o u : Nat} (D : DomS a b c 5 e f) (hc : 2 ≤ c) (sd : Sd c t o u)
    (he : e = t) (hf : f = 5 ∨ f = 7) (a1 : ¬ Arr 1 a b c) (k : ¬ Key5 a b c) (bs : ¬ Beside a b c)
    (u7 : ¬ ((a = c + 2 ∨ a + 2 = c) ∧ b = 7)) (top : f = 5 → ¬ (a = u ∧ b = 7)) :
    SN a b c e f t ∨ SN a b c e f o := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7'⟩ := D.bounds
  have k1 : Apart a b e f := D.1.k1
  have a1' : Ch a b (c + 1) 5 1 ∨ Ch a b (c + 1) 6 1 ∨ Ch a b (c - 1) 5 1 ∨ Ch a b (c - 1) 6 1 := by
    apply Classical.byContradiction
    intro q
    exact a1 ⟨fun g => q (Or.inl g), fun g => q (Or.inr (Or.inl g)), fun g => q (Or.inr (Or.inr (Or.inl g))),
      fun g => q (Or.inr (Or.inr (Or.inr g)))⟩
  clear a1
  unfold Ch at a1'
  unfold Key5 at k
  unfold Beside at bs
  unfold Apart at k1
  have ky : b ≤ 5 ∨ ¬ (a ≤ c + 1 ∧ c ≤ a + 1) := by omega
  have by' : b = 4 ∨ b = 5 ∨ b = 6 ∨ b = 7 := by omega
  clear k
  have sd' := sd
  unfold Sd at sd'
  by_cases g : f = 7 ∧ Near a b t 5
  · exact Or.inl ⟨g.2, by unfold Apart; omega, Or.inl ⟨he, g.1⟩, by omega⟩
  refine Or.inr ⟨?_, by unfold Apart; omega, Or.inr (by unfold Near; omega), by omega⟩
  unfold Near at g ⊢
  rcases sd' with s1 | s1 <;> rcases hf with rfl | rfl <;>
    rcases a1' with h | h | h | h <;> omega

/-- Every position outside the guard, the key squares, the squares beside the pawn and the
far last-rank squares, with the lone king in the pawn's square, is in a strategy class. -/
theorem step5_cover {a b c e f : Nat} (D : DomS a b c 5 e f) (hc : 2 ≤ c) (n : ¬ S5 a b c e f)
    (sq : ¬ Outside 2 c e f) (k : ¬ Key5 a b c) (bs : ¬ Beside a b c)
    (u7 : ¬ ((a = c + 2 ∨ a + 2 = c) ∧ b = 7)) : Step5 a b c e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7'⟩ := D.bounds
  have k3 := D.1.k3
  have k4 := D.k4
  unfold Outside at sq
  have h1 : e ≤ c + 2 := by omega
  have h2 : c ≤ e + 2 := by omega
  have h3 : 5 ≤ f := by omega
  have bk0 : Bl 0 c e f → ¬ Arr 0 a b c := fun b r => n (s5_bl0 b r k bs h1 h2 h3)
  have bk1 : Bl 1 c e f → ¬ Arr 1 a b c := fun b r => n (s5_bl1 b r k bs h1 h2 h3)
  by_cases two : e = c + 2 ∨ e + 2 = c
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨two, fun r => n ?_⟩))))
    exact ⟨k, h1, h2, h3, Or.inr ⟨bs, Or.inr (Or.inr (Or.inr (Or.inl ⟨by unfold Bl Ch; omega, r⟩)))⟩⟩
  by_cases mid : e = c
  · exfalso
    apply bk0 (by unfold Bl Ch; omega)
    unfold Key5 at k
    unfold Beside at bs
    unfold Arr Ch
    omega
  have sdr : Sd c (c + 1) (c - 1) (c + 2) := Or.inl ⟨rfl, by omega, rfl⟩
  have sdl : Sd c (c - 1) (c + 1) (c - 2) := Or.inr ⟨by omega, rfl, by omega⟩
  have a1 : ¬ Arr 1 a b c := bk1 (by unfold Bl Ch; omega)
  have row : f = 5 ∨ f = 7 := by omega
  by_cases right : e = c + 1
  · rcases cover_t D hc sdr right row a1 k bs u7 (fun _ q => u7 ⟨Or.inl q.1, q.2⟩) with q | q
    · exact Or.inl q
    · exact Or.inr (Or.inl q)
  · rcases cover_t D hc sdl (by omega) row a1 k bs u7 (fun _ q => u7 ⟨Or.inr (by omega), q.2⟩) with q | q
    · exact Or.inr (Or.inl q)
    · exact Or.inl q

end EndgameChess.Rules.KPK.Coord
