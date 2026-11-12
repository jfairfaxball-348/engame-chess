import EndgameChess.Rules.KPK.Coord.FiveRace

/-! Fifth-rank wins: the race when the lone king can touch the pawn next move. Outside the
guard the king is then close enough to protect the pawn after its step, and the race is
always to the far side. -/
namespace EndgameChess.Rules.KPK.Coord

set_option maxHeartbeats 4000000 in
/-- The squares from which the lone king threatens the pawn, inside the pawn's square. -/
theorem thr_cases {a b c e f : Nat} (D : DomS a b c 4 e f) (hc : 2 ≤ c) (sq : Sq4 c e f)
    (thr : Thr c e f) :
    (e = c ∧ (f = 5 ∨ f = 6)) ∨ ∃ t o u, Sd c t o u ∧
      ((e = t ∧ (f = 4 ∨ f = 6)) ∨ (e = u ∧ (f = 4 ∨ f = 5))) := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  have k3 := D.1.k3
  have k4 := D.k4
  unfold Sq4 at sq
  unfold Thr Ch at thr
  by_cases mid : e = c
  · exact Or.inl ⟨mid, by omega⟩
  right
  by_cases g : c < e
  · exact ⟨c + 1, c - 1, c + 2, Or.inl ⟨rfl, by omega, rfl⟩, by omega⟩
  · exact ⟨c - 1, c + 1, c - 2, Or.inr ⟨by omega, rfl, by omega⟩, by omega⟩

set_option maxHeartbeats 4000000 in
/-- A lone king in front of the pawn loses no race of two or more moves. -/
theorem no_race_front {a b c e f p q m : Nat} (hc : 2 ≤ c) (kt : KeyT c p q) (he : e = c)
    (hf : f = 5 ∨ f = 6) (hm : 1 ≤ m) (won : Won a b c e f p q (m + 1)) : False := by
  obtain ⟨hp, hq⟩ := kt
  apply won.2
  rcases hp with rfl | hp <;> rcases hq with rfl | rfl <;>
    (unfold WR Cross Hit Ch; omega)

set_option maxHeartbeats 4000000 in
/-- Nor does one beside the pawn's file on the seventh rank. -/
theorem no_race_t6 {a b c e t o u p q m : Nat} (hc : 2 ≤ c) (sd : Sd c t o u)
    (kt : KeyT c p q) (he : e = t) (hm : 1 ≤ m) (won : Won a b c e 6 p q (m + 1)) : False := by
  obtain ⟨hp, hq⟩ := kt
  unfold Sd at sd
  apply won.2
  rcases hp with rfl | hp <;> rcases hq with rfl | rfl <;>
    (unfold WR Cross Hit Ch; omega)

set_option maxHeartbeats 4000000 in
/-- A lone king on the pawn's rank or two files out on the sixth loses races only to the
far side, and only short ones. -/
theorem race_far_side {a b c e f t o u p q m : Nat} (hc : 2 ≤ c) (sd : Sd c t o u)
    (kt : KeyT c p q) (hl : (e = t ∧ f = 4) ∨ (e = u ∧ (f = 4 ∨ f = 5))) (hm : 1 ≤ m)
    (won : Won a b c e f p q (m + 1)) : p = o ∧ m ≤ 2 ∧ (e = t → m = 1) ∧ (f = 5 → m = 1) := by
  obtain ⟨hp, hq⟩ := kt
  unfold Sd at sd
  apply Classical.byContradiction
  intro bad
  apply won.2
  rcases hp with rfl | hp <;> rcases hq with rfl | rfl <;>
    (unfold WR Cross Hit Ch; omega)

set_option maxHeartbeats 4000000 in
/-- A king within one of the three squares beside the pawn on the far side protects it. -/
theorem box_not_pr {x y c t o u : Nat} (hc : 2 ≤ c) (sd : Sd c t o u) (h1 : x ≤ o + 1)
    (h2 : o ≤ x + 1) (h3 : 2 ≤ y) (h4 : y ≤ 6) (np : ¬ (x = c ∧ y = 4)) : ¬ Pr4 x y c t 4 := by
  rintro ⟨-, nn, all⟩
  unfold Sd at sd
  unfold Near at nn
  obtain ⟨y', hy⟩ : ∃ y', (y' = 3 ∨ y' = 4 ∨ y' = 5) ∧ y ≤ y' + 1 ∧ y' ≤ y + 1 := by
    by_cases g1 : y ≤ 3
    · exact ⟨3, by omega⟩
    by_cases g2 : 5 ≤ y
    · exact ⟨5, by omega⟩
    · exact ⟨4, by omega⟩
  exact all o y' (by unfold Near; omega) (by unfold Near; omega) (by unfold Apart; omega)

set_option maxHeartbeats 4000000 in
/-- A king on the lone king's file that wins a three-move race to the far side stands on
the last rank. -/
theorem close_u_file {a b c f t o u q m : Nat} (hc : 2 ≤ c) (sd : Sd c t o u)
    (hf : f = 4 ∨ f = 5) (hq : q = 5 ∨ q = 6) (b7 : b ≤ 7) (cx : Ch a b o q (m + 1))
    (thru : ¬ Thru a b c o q ∨ Ch a b o q m) (m2 : m ≤ 2) (m5 : f = 5 → m = 1)
    (nadj : f = 4 → ¬ Ch a b t 6 1) (k1 : Apart a b u f) (g : a = u) : b = 7 ∧ f = 4 := by
  unfold Sd at sd
  unfold Apart at k1
  subst g
  rcases hq with rfl | rfl <;> rcases hf with rfl | rfl <;>
    (unfold Thru at thru; unfold Ch at cx nadj thru; omega)

set_option maxHeartbeats 4000000 in
/-- The step towards the far side is not next to the lone king. -/
theorem close_u_apart {a b c f t o u q m x y : Nat} (hc : 2 ≤ c) (sd : Sd c t o u)
    (hf : f = 4 ∨ f = 5) (hq : q = 5 ∨ q = 6) (b7 : b ≤ 7) (cx : Ch a b o q (m + 1))
    (thru : ¬ Thru a b c o q ∨ Ch a b o q m) (m2 : m ≤ 2) (m5 : f = 5 → m = 1)
    (nadj : f = 4 → ¬ Ch a b t 6 1) (k1 : Apart a b u f) (tw : Toward a b o q x y) : Apart x y u f := by
  obtain ⟨tx, ty⟩ := tw
  by_cases g : a = u
  · obtain ⟨rfl, rfl⟩ := close_u_file hc sd hf hq b7 cx thru m2 m5 nadj k1 g
    unfold Apart
    omega
  · unfold Sd at sd
    unfold Ch at cx
    clear thru nadj k1 ty
    unfold Apart
    omega

set_option maxHeartbeats 4000000 in
/-- After the step the king is within one of the squares protecting the pawn. -/
theorem close_u_box {a b c f t o u q m x y : Nat} (hc : 2 ≤ c) (h3 : c ≤ 3) (sd : Sd c t o u)
    (hf : f = 4 ∨ f = 5) (hq : q = 5 ∨ q = 6) (b7 : b ≤ 7) (cx : Ch a b o q (m + 1))
    (thru : ¬ Thru a b c o q ∨ Ch a b o q m) (m2 : m ≤ 2) (m5 : f = 5 → m = 1)
    (nadj : f = 4 → ¬ Ch a b t 6 1) (k1 : Apart a b u f) (nrr : ¬ Rr4 a c u f) (kx : ¬ K4 x y c)
    (tw : Toward a b o q x y) : x ≤ o + 1 ∧ o ≤ x + 1 ∧ 2 ≤ y ∧ y ≤ 6 := by
  obtain ⟨tx, ty⟩ := tw
  have hy : 2 ≤ y ∧ y ≤ 6 := by
    unfold Ch at cx
    clear thru nadj k1 nrr kx tx
    omega
  by_cases g : a = u
  · obtain ⟨rfl, rfl⟩ := close_u_file hc sd hf hq b7 cx thru m2 m5 nadj k1 g
    exfalso
    apply kx
    unfold Sd at sd
    unfold K4
    omega
  · unfold Sd at sd
    unfold Ch at cx
    unfold Rr4 at nrr
    clear thru nadj k1 ty kx
    omega
set_option maxHeartbeats 4000000 in
/-- Lone king two files out, on the pawn's rank or the sixth: the walk to the far side. -/
theorem mv_close_u {j a b c f t o u q m : Nat} (D : DomS a b c 4 u f) (hc : 2 ≤ c)
    (sd : Sd c t o u) (hf : f = 4 ∨ f = 5) (hq : q = 5 ∨ q = 6) (hm : 1 ≤ m) (hj : m + 5 ≤ j)
    (won : Won a b c u f o q (m + 1)) (nk : ¬ K4 a b c) (nb : ¬ B4 a b c)
    (nbh : ¬ (b = 3 ∧ (a = c + 1 ∨ a + 1 = c))) (nrr : ¬ Rr4 a c u f)
    (no6 : ¬ Won a b c u f t 6 1) : Mv4 j a b c u f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  have k1 := D.1.k1
  have k2 := D.1.k2
  have k4 := D.k4
  have sd' := sd
  unfold Sd at sd'
  have kt : KeyT c o q := ⟨by omega, hq⟩
  obtain ⟨kr, nwr⟩ := won
  obtain ⟨-, m2, -, m5⟩ := race_far_side hc sd kt (Or.inr ⟨rfl, hf⟩) hm ⟨kr, nwr⟩
  have nadj : f = 4 → ¬ Ch a b t 6 1 := by
    intro f4 g
    apply no6
    refine ⟨⟨g, Or.inl (by unfold Thru; omega)⟩, ?_⟩
    unfold WR Ch
    omega
  have thru : ¬ Thru a b c o q ∨ Ch a b o q m := by
    rcases kr.2 with h | h
    · exact Or.inl h
    · exact Or.inr h.1
  refine mv_walk D hc kt hj kr nk nb nbh ?_ ?_ ?_
  · intro x y tw
    exact close_u_apart hc sd hf hq u2 kr.1 thru m2 m5 nadj k1 tw
  · intro x y _ cap
    have t' := cap.1
    unfold Near at t'
    omega
  · intro x y X Y tw ws sqx kx
    obtain ⟨⟨n1, n2, n3, n4⟩, n5, n6⟩ := WeakStep.bounds ws
    have k5 := ws.k5
    have k6 := ws.k6
    have k8 := ws.k8
    obtain ⟨kr2, near, hx, hy, npawn, xlt⟩ := kr_fwd hc u3 u1 u2 kt nk nb nbh k2 kr tw
    have sqx' := sqx
    unfold Sq4 at sqx'
    have box : x ≤ o + 1 ∧ o ≤ x + 1 ∧ 2 ≤ y ∧ y ≤ 6 :=
      close_u_box hc u3 sd hf hq u2 kr.1 thru m2 m5 nadj k1 nrr kx tw
    refine ⟨fun pr => ?_, fun rr => ?_, fun w => nwr (wr_back hc kt ws.1 (by omega) sqx'.2.2
      (by omega) k8 k6 (by omega) w)⟩
    · have tch := pr.1
      have e1 : X = t ∧ Y = 4 := by
        unfold Near at tch
        omega
      obtain ⟨rfl, rfl⟩ := e1
      exact box_not_pr hc sd box.1 box.2.1 box.2.2.1 box.2.2.2 npawn pr
    · unfold Rr4 at rr
      omega

set_option maxHeartbeats 4000000 in
/-- Lone king beside the pawn: outside the guard the king stands one step from protecting
the pawn on the far side, and does so. -/
theorem mv_close_t {j a b c t o u q : Nat} (D : DomS a b c 4 t 4) (hc : 2 ≤ c)
    (sd : Sd c t o u) (hq : q = 5 ∨ q = 6) (hj : 4 ≤ j) (won : Won a b c t 4 o q 2)
    (nk : ¬ K4 a b c) (nb : ¬ B4 a b c) (nbh : ¬ (b = 3 ∧ (a = c + 1 ∨ a + 1 = c)))
    (no5 : ¬ Won a b c t 4 o 5 1) (out : ¬ S4 a b c t 4) : Mv4 j a b c t 4 := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  have k1 := D.1.k1
  have k2 := D.1.k2
  have sd' := sd
  unfold Sd at sd'
  obtain ⟨kr, -⟩ := won
  have nadj : ¬ Ch a b o 5 1 := by
    intro g
    apply no5
    refine ⟨⟨g, Or.inl (by unfold Thru; unfold Ch at g; omega)⟩, ?_⟩
    unfold WR Ch
    omega
  have pos : b = 3 ∧ (a + 1 = o ∨ a = o + 1) := by
    apply Classical.byContradiction
    intro hne
    apply out
    refine ⟨nk, by unfold Sq4; omega, Or.inr ⟨nb, Or.inr (Or.inr (Or.inl
      ⟨by unfold Near; omega, ?_, ?_⟩))⟩⟩
    · unfold K4 at nk
      unfold B4 at nb
      unfold Apart at k1
      unfold Near
      omega
    · intro x' y' m1 m2
      have cx := kr.1
      unfold Ch at cx nadj
      unfold Near at m1 m2
      unfold K4 at nk
      unfold Apart at k1
      unfold Apart
      omega
  have st : KingStep a b c 4 t 4 o 4 := by
    unfold KingStep Near Apart
    omega
  have D' := dom_step4 D st
  have keep : ¬ Capture o 4 c 4 t 4 := by
    unfold Capture Near
    omega
  have bx : B4 o 4 c := by unfold B4; omega
  refine Or.inr ⟨j - 1, by omega, o, 4, st, keep,
    weak_reply D' (Or.inr (Or.inl (Nat.le_refl 4))) keep, fun X Y ws => ?_⟩
  obtain ⟨⟨n1, n2, n3, n4⟩, n5, n6⟩ := WeakStep.bounds ws
  refine ⟨?_, Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, bx⟩)))⟩
  rintro ⟨-, -, ⟨-, hY, -⟩ | ⟨nbx, -⟩⟩
  · omega
  · exact nbx bx

/-- A won race outside the guard: the king has a move that keeps the win. -/
theorem mv_race {j a b c e f p q n : Nat} (D : DomS a b c 4 e f) (hc : 2 ≤ c)
    (kt : KeyT c p q) (hn : 1 ≤ n) (hj : n + 4 ≤ j) (won : Won a b c e f p q n)
    (nk : ¬ K4 a b c) (nb : ¬ B4 a b c) (sq : Sq4 c e f) (out : ¬ S4 a b c e f) :
    Mv4 j a b c e f := by
  by_cases bh : b = 3 ∧ (a = c + 1 ∨ a + 1 = c)
  · exact mv_behind4 D hc (by omega) bh.2 bh.1 kt sq won
  by_cases r1 : Won a b c e f (c + 1) 5 1
  · exact mv_arrive5 D hc (Or.inl rfl) (by omega) r1 nk
  by_cases r2 : Won a b c e f (c - 1) 5 1
  · exact mv_arrive5 D hc (Or.inr (by omega)) (by omega) r2 nk
  by_cases r3 : Won a b c e f (c + 1) 6 1
  · exact mv_arrive6 D hc (Or.inl rfl) (by omega) r3 r1 nk nb sq out
  by_cases r4 : Won a b c e f (c - 1) 6 1
  · exact mv_arrive6 D hc (Or.inr (by omega)) (by omega) r4 r2 nk nb sq out
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : 1 ≤ m := by
    apply Classical.byContradiction
    intro z
    have m0 : m = 0 := by omega
    subst m0
    obtain ⟨hp, hq⟩ := kt
    rcases hp with rfl | hp
    · rcases hq with rfl | rfl
      · exact r1 won
      · exact r3 won
    · have e1 : p = c - 1 := by omega
      subst e1
      rcases hq with rfl | rfl
      · exact r2 won
      · exact r4 won
  by_cases thr : Thr c e f
  · rcases thr_cases D hc sq thr with ⟨he, hf⟩ | ⟨t, o, u, sd, hl⟩
    · exact (no_race_front hc kt he hf hm won).elim
    · have sd' := sd
      unfold Sd at sd'
      have side (r : Nat) (hr : r = 5 ∨ r = 6) : (¬ Won a b c e f t r 1) ∧ (¬ Won a b c e f o r 1) := by
        rcases sd' with ⟨h1, h2, -⟩ | ⟨h1, h2, -⟩
        · have e2 : o = c - 1 := by omega
          subst h1 e2
          rcases hr with rfl | rfl
          · exact ⟨r1, r2⟩
          · exact ⟨r3, r4⟩
        · have e2 : t = c - 1 := by omega
          subst h2 e2
          rcases hr with rfl | rfl
          · exact ⟨r2, r1⟩
          · exact ⟨r4, r3⟩
      rcases hl with ⟨rfl, rfl | rfl⟩ | ⟨rfl, hf⟩
      · obtain ⟨rfl, -, m1, -⟩ := race_far_side hc sd kt (Or.inl ⟨rfl, rfl⟩) hm won
        have e1 : m = 1 := m1 rfl
        subst e1
        exact mv_close_t D hc sd kt.2 (by omega) won nk nb bh (side 5 (Or.inl rfl)).2 out
      · exact (no_race_t6 hc sd kt rfl hm won).elim
      · obtain ⟨rfl, -, -, -⟩ := race_far_side hc sd kt (Or.inr ⟨rfl, hf⟩) hm won
        refine mv_close_u D hc sd hf kt.2 hm (by omega) won nk nb bh ?_ (side 6 (Or.inr rfl)).1
        intro rr
        exact out ⟨nk, sq, Or.inr ⟨nb, Or.inr (Or.inr (Or.inr rr))⟩⟩
  · exact mv_far4 D hc kt (by omega) won nk nb bh sq thr

end EndgameChess.Rules.KPK.Coord
