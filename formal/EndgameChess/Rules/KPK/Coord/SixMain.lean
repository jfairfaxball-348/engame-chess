import EndgameChess.Rules.KPK.Coord.SixMove

/-! The planned move of every sixth-rank position outside the guard. -/
namespace EndgameChess.Rules.KPK.Coord

set_option maxHeartbeats 4000000 in
/-- A far king heads diagonally for the square behind the pawn. -/
theorem mv_step {j a b c e f : Nat} (D : DomS a b c 5 e f) (hc : 2 ≤ c) (ph : Ch a b c 4 (j - 3))
    (hj : 3 ≤ j) (far : ¬ Ch a b c 4 1) (hu : e = c + 2 ∨ e + 2 = c) (hf : 5 ≤ f) (a2 : ¬ Arr 2 a b c)
    (n1 : ¬ SN a b c e f (c + 1)) (n2 : ¬ SN a b c e f (c - 1))
    (nk : ¬ Key5 a b c) (nb : ¬ Beside a b c) (nu : ¬ ((a = c + 2 ∨ a + 2 = c) ∧ b = 7))
    (hs : Arr 1 a b c → ¬ (f = 5 ∧ ((e = c + 2 ∧ c + 2 ≤ a) ∨ (e + 2 = c ∧ a + 2 ≤ c)) ∧ (b = 3 ∨ b = 7))) :
    Mv j a b c e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  have k1 := D.1.k1
  have k3 := D.1.k3
  have k4 := D.k4
  have a2' : Ch a b (c + 1) 5 2 ∨ Ch a b (c + 1) 6 2 ∨ Ch a b (c - 1) 5 2 ∨ Ch a b (c - 1) 6 2 := by
    apply Classical.byContradiction
    intro q
    exact a2 ⟨fun g => q (Or.inl g), fun g => q (Or.inr (Or.inl g)), fun g => q (Or.inr (Or.inr (Or.inl g))),
      fun g => q (Or.inr (Or.inr (Or.inr g)))⟩
  have same : ¬ (f = 5 ∧ ((e = c + 2 ∧ c + 2 ≤ a) ∨ (e + 2 = c ∧ a + 2 ≤ c)) ∧ (b = 3 ∨ b = 7)) := by
    intro q
    apply hs _ q
    unfold Arr Ch
    omega
  have r6 : ¬ (a = c + 2 ∧ b = 6 ∧ e + 2 = c) := by
    rintro ⟨h1, h2, h3⟩
    exact n1 ⟨by unfold Near; omega, by unfold Apart; omega, Or.inr (by unfold Near; omega), by omega⟩
  have l6 : ¬ (a + 2 = c ∧ b = 6 ∧ e = c + 2) := by
    rintro ⟨h1, h2, h3⟩
    exact n2 ⟨by unfold Near; omega, by unfold Apart; omega, Or.inr (by unfold Near; omega), by omega⟩
  clear hs n1 n2 a2
  obtain ⟨x, hx⟩ : ∃ x, (c + 2 ≤ a ∧ x + 1 = a) ∨ (a + 2 ≤ c ∧ x = a + 1) ∨ (a ≤ c + 1 ∧ c ≤ a + 1 ∧ x = a) := by
    by_cases g : c + 2 ≤ a
    · exact ⟨a - 1, Or.inl ⟨g, by omega⟩⟩
    · by_cases g2 : a + 2 ≤ c
      · exact ⟨a + 1, Or.inr (Or.inl ⟨g2, rfl⟩)⟩
      · exact ⟨a, Or.inr (Or.inr ⟨by omega, by omega, rfl⟩)⟩
  obtain ⟨y, hy⟩ : ∃ y, (b ≤ 3 ∧ y = b + 1) ∨ (5 ≤ b ∧ y + 1 = b) ∨ (b = 4 ∧ y = 4) := by
    by_cases g : b ≤ 3
    · exact ⟨b + 1, Or.inl ⟨g, rfl⟩⟩
    · by_cases g2 : 5 ≤ b
      · exact ⟨b - 1, Or.inr (Or.inl ⟨g2, by omega⟩)⟩
      · exact ⟨4, Or.inr (Or.inr ⟨by omega, rfl⟩)⟩
  unfold Ch at ph far a2'
  unfold Key5 at nk
  unfold Beside at nb
  have ax : a ≤ x + 1 ∧ x ≤ a + 1 := by
    clear same r6 l6 nk nb nu ph far a2' k1 k3 k4 hy
    omega
  have ay : b ≤ y + 1 ∧ y ≤ b + 1 := by
    clear same r6 l6 nk nb nu ph far a2' k1 k3 k4 hx
    omega
  have ne : ¬ (a = x ∧ b = y) := by
    clear same r6 l6 nk nb nu ph a2' k1 k3 k4
    omega
  have ap : Apart x y e f := by
    clear r6 l6 ph k3 k4
    unfold Apart
    rcases hu with g | g <;> rcases a2' with q | q | q | q <;> omega
  have np : ¬ (x = c ∧ y = 5) := by
    clear same r6 l6 nb nu ph far a2' k1 k3 k4 ap
    omega
  have st : KingStep a b c 5 e f x y :=
    ⟨⟨ax.1, ax.2, ay.1, ay.2, ne⟩, by clear same r6 l6 nk nb nu ph far a2' k1 k3 k4; omega,
      by clear same r6 l6 nk nb nu ph far a2' k1 k3 k4; omega, np, ap⟩
  have mp : Ch x y c 4 (j - 4) := by
    clear same r6 l6 nk nb nu a2' k1 k3 k4 ap st np
    unfold Ch; omega
  have a1 : ¬ Arr 1 x y c := by
    clear same r6 l6 nk nb nu ph far k1 k3 k4 ap st np mp
    intro r
    obtain ⟨r1, r2, r3, r4⟩ := r
    unfold Ch at r1 r2 r3 r4
    rcases a2' with q | q | q | q <;> omega
  have p2 : Ch x y c 5 2 := by
    clear same r6 l6 nk nb nu ph far k1 k3 k4 ap st np mp a1
    unfold Ch; rcases a2' with q | q | q | q <;> omega
  have bx : ¬ Beside x y c := by
    clear same nu ph far k3 k4 ap st np mp a1 p2 a2' nb ax ay ne
    unfold Beside
    rintro ⟨g1, g2⟩
    have b6 : b = 6 := by
      clear r6 l6 nk k1 g2 hx hu
      omega
    subst b6
    have side : c + 2 ≤ a ∨ a + 2 ≤ c := by omega
    rcases hu with g | g <;> rcases side with g3 | g3 <;> rcases g2 with g4 | g4 <;> omega
  have y7 : y ≠ 7 := by
    clear same r6 l6 nk nb nu ph far a2' k1 k3 k4 ap st np mp a1 p2 bx
    omega
  have j5 : 5 ≤ j := by
    clear same r6 l6 nk nb nu a2' k1 k3 k4 ap st np mp a1 p2 bx hx hy
    unfold Ch at *
    omega
  refine mv_far D hc mp j5 st hu a1 p2 bx y7 ?_
  rintro ⟨g1, g2, g3, g4, g5⟩
  exact bx ⟨g5, Or.inr (by omega)⟩

set_option maxHeartbeats 4000000 in
/-- Every sixth-rank position outside the guard has its planned move. -/
theorem six_move {j a b c e f : Nat} (D : DomS a b c 5 e f) (hc : 2 ≤ c) (n : ¬ S5 a b c e f)
    (ph : Phi j a b c) (cover : ¬ Outside 2 c e f → ¬ Key5 a b c → ¬ Beside a b c →
      ¬ ((a = c + 2 ∨ a + 2 = c) ∧ b = 7) → Step5 a b c e f) : Mv j a b c e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  by_cases key : (a = c + 1 ∨ a + 1 = c ∨ a = c) ∧ 6 ≤ b
  · exact mv_ahead D hc ph key.1 key.2
  have nk : ¬ Key5 a b c := by unfold Key5; omega
  by_cases sq : Outside 2 c e f
  · have s' := sq
    unfold Outside at s'
    have fr : Free a b e f c 6 := by unfold Free; omega
    exact Or.inl ⟨fr, w6_run (dom_push D fr) hc sq⟩
  have s' := sq
  unfold Outside at s'
  by_cases bs : Beside a b c
  · refine mv_beside D hc ph bs ?_
    rintro ⟨h1, h2⟩
    exact n ⟨nk, by omega, by omega, by omega, Or.inl ⟨bs, h1, h2⟩⟩
  by_cases top : (a = c + 2 ∨ a + 2 = c) ∧ b = 7
  · have r0 : Arr 0 a b c := by unfold Arr Ch; omega
    have hj : 1 ≤ j := by
      unfold Phi Ch at ph
      rcases ph with q | q | q | q | q <;> omega
    have nF : ¬ (e = c ∧ f = 6) := by
      rintro ⟨rfl, rfl⟩
      exact n (s5_bl0 (Or.inl (by unfold Ch; omega)) r0 nk bs (by omega) (by omega) (by omega))
    have nB : ¬ (e = c ∧ f = 7) := by
      rintro ⟨rfl, rfl⟩
      exact n (s5_bl0 (Or.inr (by unfold Ch; omega)) r0 nk bs (by omega) (by omega) (by omega))
    have nA : (a = c + 2 → ¬ (e = c + 1 ∧ f = 5)) ∧ (a + 2 = c → ¬ (e + 1 = c ∧ f = 5)) := by
      constructor
      · rintro h ⟨h1, h2⟩
        exact n ⟨nk, by omega, by omega, by omega, Or.inr ⟨bs, Or.inl ⟨h2, Or.inl ⟨h1, h⟩, top.2⟩⟩⟩
      · rintro h ⟨h1, h2⟩
        exact n ⟨nk, by omega, by omega, by omega, Or.inr ⟨bs, Or.inl ⟨h2, Or.inr ⟨h1, h⟩, top.2⟩⟩⟩
    rcases top with ⟨h | h, hb⟩
    · exact mv_u7 D hc hj (t := c + 1) (o := c - 1) (u := c + 2) (Or.inl ⟨rfl, by omega, rfl⟩) h hb (nA.1 h) nF nB
    · exact mv_u7 D hc hj (t := c - 1) (o := c + 1) (u := c - 2) (Or.inr ⟨by omega, rfl, by omega⟩) (by omega) hb
        (fun q => nA.2 h ⟨by omega, q.2⟩) nF nB
  have rest : 3 ≤ j ∧ Ch a b c 4 (j - 3) := by
    unfold Phi at ph
    rcases ph with q | q | q | q | q
    · omega
    · omega
    · exact absurd q.2 bs
    · refine ⟨q.1, ?_⟩
      unfold Ch; omega
    · exact q
  obtain ⟨hj3, ph3⟩ := rest
  have sdr : Sd c (c + 1) (c - 1) (c + 2) := Or.inl ⟨rfl, by omega, rfl⟩
  have sdl : Sd c (c - 1) (c + 1) (c - 2) := Or.inr ⟨by omega, rfl, by omega⟩
  by_cases n1 : SN a b c e f (c + 1)
  · exact mv_sn D hc hj3 sdr n1
  by_cases n2 : SN a b c e f (c - 1)
  · exact mv_sn D hc hj3 sdl n2
  by_cases p1 : SP a b c e f (c + 1) (c - 1) (c - 2)
  · exact mv_sp D hc sdr (Or.inr ⟨by omega, by omega⟩) p1 nk bs (fun q => top ⟨Or.inl q.1, q.2⟩) n1
  by_cases p2 : SP a b c e f (c - 1) (c + 1) (c + 2)
  · exact mv_sp D hc sdl (Or.inl ⟨rfl, rfl⟩) p2 nk bs (fun q => top ⟨Or.inr (by omega), q.2⟩) n2
  rcases cover sq nk bs top with h | h | h | h | ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
  · exact absurd h n1
  · exact absurd h n2
  · exact absurd h p1
  · exact absurd h p2
  · exact mv_behind D hc (by unfold Ch at ph3 h1; omega) h1 h2 h3 sq
  · by_cases near : Ch a b c 4 1
    · by_cases behind : a = c ∧ b = 4
      · exfalso
        obtain ⟨rfl, rfl⟩ := behind
        rcases h1 with h1 | h1
        · apply n2
          refine ⟨by unfold Near; omega, by unfold Apart; omega, Or.inr (by unfold Near; omega), by omega⟩
        · apply n1
          refine ⟨by unfold Near; omega, by unfold Apart; omega, Or.inr (by unfold Near; omega), by omega⟩
      · exact mv_behind D hc (by unfold Ch at ph3 near; omega) near behind (by unfold Bl Ch; omega) sq
    · refine mv_step D hc ph3 hj3 near h1 (by omega) h2 n1 n2 nk bs top ?_
      rintro r ⟨q1, q2, q3⟩
      exact n ⟨nk, by omega, by omega, by omega, Or.inr ⟨bs, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨q1, q2, q3, r⟩))))⟩⟩

end EndgameChess.Rules.KPK.Coord
