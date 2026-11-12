import EndgameChess.Rules.KPK.Coord.FiveWin

/-! Fifth-rank wins: the king walks to a key square it reaches first. A lone-king step
gains at most one in the race, so the race stays won, and a won race excludes every
clause of the guard except the two in which the pawn falls. -/
namespace EndgameChess.Rules.KPK.Coord

/-- The lone king can touch the pawn on its next move, or does already. -/
def Thr (c e f : Nat) : Prop := Ch e f (c + 1) 4 1 ∨ Ch e f (c - 1) 4 1 ∨ Ch e f c 5 1

theorem toward_ex (e f g h : Nat) : ∃ u v, Toward e f g h u v := by
  have hx : ∃ u, (e < g ∧ u = e + 1) ∨ (g < e ∧ u + 1 = e) ∨ (e = g ∧ u = e) := by
    rcases Nat.lt_trichotomy e g with k | k | k
    · exact ⟨e + 1, Or.inl ⟨k, rfl⟩⟩
    · exact ⟨e, Or.inr (Or.inr ⟨k, rfl⟩)⟩
    · exact ⟨e - 1, Or.inr (Or.inl ⟨k, by omega⟩)⟩
  have hy : ∃ v, (f < h ∧ v = f + 1) ∨ (h < f ∧ v + 1 = f) ∨ (f = h ∧ v = f) := by
    rcases Nat.lt_trichotomy f h with k | k | k
    · exact ⟨f + 1, Or.inl ⟨k, rfl⟩⟩
    · exact ⟨f, Or.inr (Or.inr ⟨k, rfl⟩)⟩
    · exact ⟨f - 1, Or.inr (Or.inl ⟨k, by omega⟩)⟩
  obtain ⟨u, hu⟩ := hx
  obtain ⟨v, hv⟩ := hy
  exact ⟨u, v, hu, hv⟩

set_option maxHeartbeats 4000000 in
/-- A lone-king step inside the pawn's square gains at most one in a race. The one
exception is the step from beside the pawn to the square in front of it. -/
theorem wr_back {e f c p q X Y n : Nat} (hc : 2 ≤ c) (kt : KeyT c p q) (st : Near e f X Y)
    (f4 : 4 ≤ f) (y4 : 4 ≤ Y) (na : ¬ (f = 5 ∧ (e = c + 1 ∨ e + 1 = c)))
    (nb : ¬ (Y = 5 ∧ (X = c + 1 ∨ X + 1 = c))) (np : ¬ (X = c ∧ Y = 4))
    (ex : ¬ (f = 4 ∧ (e = c + 1 ∨ e + 1 = c) ∧ X = c ∧ Y = 5)) (h : WR X Y c p q n) :
    WR e f c p q (n + 1) := by
  obtain ⟨hp, hq⟩ := kt
  unfold Near at st
  rcases hp with rfl | hp <;> rcases hq with rfl | rfl <;>
    (unfold WR Cross Hit Ch at *; omega)

set_option maxHeartbeats 4000000 in
/-- A king beside the pawn wins no race against a lone king two ranks ahead of it. -/
theorem won_not_bes {x y c X Y p q m : Nat} (hc : 2 ≤ c) (kt : KeyT c p q) (bes : B4 x y c)
    (hY : Y = 6) (hX : X = x ∨ X = c) (won : Won x y c X Y p q m) : False := by
  obtain ⟨hp, hq⟩ := kt
  obtain ⟨kr, nw⟩ := won
  unfold B4 at bes
  apply nw
  unfold KR Thru Ch at kr
  rcases hp with rfl | hp <;> rcases hq with rfl | rfl <;>
    (unfold WR Cross Hit Ch; omega)

set_option maxHeartbeats 4000000 in
/-- Opposed kings on an outer file: no race is won. -/
theorem won_not_op {x y c X Y p q m : Nat} (hc : 2 ≤ c) (h3 : c ≤ 3) (kt : KeyT c p q)
    (op : Op4 x y c X Y) (sq : Sq4 c X Y) (won : Won x y c X Y p q m) : False := by
  obtain ⟨hp, hq⟩ := kt
  obtain ⟨kr, nw⟩ := won
  unfold Op4 at op
  unfold Sq4 at sq
  apply nw
  unfold KR Thru Ch at kr
  rcases hp with rfl | hp <;> rcases hq with rfl | rfl <;>
    (unfold WR Cross Hit Ch; omega)

/-- A won race leaves only the two clauses of the guard in which the pawn falls. -/
theorem won_out {x y c X Y p q m : Nat} (hc : 2 ≤ c) (h3 : c ≤ 3) (kt : KeyT c p q)
    (won : Won x y c X Y p q m) (npr : ¬ Pr4 x y c X Y) (nrr : ¬ Rr4 x c X Y) :
    ¬ S4 x y c X Y := by
  rintro ⟨-, sq, ⟨bes, hY, hX⟩ | ⟨-, op | m4 | pr | rr⟩⟩
  · exact won_not_bes hc kt bes hY hX won
  · exact won_not_op hc h3 kt op sq won
  · obtain ⟨⟨r1, r2, r3, r4⟩, -, -⟩ := m4
    obtain ⟨hp, hq⟩ := kt
    rcases hp with rfl | hp
    · rcases hq with rfl | rfl
      · exact won.2 (r1 m won.1)
      · exact won.2 (r2 m won.1)
    · have e1 : p = c - 1 := by omega
      subst e1
      rcases hq with rfl | rfl
      · exact won.2 (r3 m won.1)
      · exact won.2 (r4 m won.1)
  · exact npr pr
  · exact nrr rr

set_option maxHeartbeats 4000000 in
/-- The step towards the target is a king step that stays on a shortest way round the pawn. -/
theorem kr_fwd {a b c p q m x y : Nat} (hc : 2 ≤ c) (h3 : c ≤ 3) (ha : a ≤ 7) (hb : b ≤ 7)
    (kt : KeyT c p q) (nk : ¬ K4 a b c) (nb : ¬ B4 a b c)
    (nbh : ¬ (b = 3 ∧ (a = c + 1 ∨ a + 1 = c))) (k2 : ¬ (a = c ∧ b = 4))
    (kr : KR a b c p q (m + 1)) (tw : Toward a b p q x y) :
    KR x y c p q m ∧ Near a b x y ∧ x ≤ 7 ∧ y ≤ 7 ∧ ¬ (x = c ∧ y = 4) ∧ x ≤ 6 := by
  obtain ⟨hp, hq⟩ := kt
  unfold K4 at nk
  unfold B4 at nb
  unfold Toward at tw
  unfold KR Thru Ch at kr
  rcases hp with rfl | hp <;> rcases hq with rfl | rfl <;>
    (unfold KR Thru Ch Near; omega)

/-- The king walks towards a key square it reaches first. The three safety conditions
are that the step is not next to the lone king, that the pawn is not then taken, and
that after a reply inside the square the pawn does not fall and the race is still won. -/
theorem mv_walk {j a b c e f p q m : Nat} (D : DomS a b c 4 e f) (hc : 2 ≤ c)
    (kt : KeyT c p q) (hj : m + 5 ≤ j) (kr : KR a b c p q (m + 1)) (nk : ¬ K4 a b c)
    (nb : ¬ B4 a b c) (nbh : ¬ (b = 3 ∧ (a = c + 1 ∨ a + 1 = c)))
    (hS : ∀ x y, Toward a b p q x y → Apart x y e f)
    (hC : ∀ x y, Toward a b p q x y → ¬ Capture x y c 4 e f)
    (hR : ∀ x y X Y, Toward a b p q x y → WeakStep x y c 4 e f X Y → Sq4 c X Y → ¬ K4 x y c →
      ¬ Pr4 x y c X Y ∧ ¬ Rr4 x c X Y ∧ ¬ WR X Y c p q m) : Mv4 j a b c e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  obtain ⟨x, y, tw⟩ := toward_ex a b p q
  obtain ⟨kr2, near, hx, hy, npawn, xlt⟩ := kr_fwd hc u3 u1 u2 kt nk nb nbh D.1.k2 kr tw
  have st : KingStep a b c 4 e f x y := ⟨near, hx, hy, npawn, hS x y tw⟩
  have D' := dom_step4 D st
  have keep := hC x y tw
  refine Or.inr ⟨j - 1, by omega, x, y, st, w4win_mono (i := m + 4) (by omega) ⟨keep,
    weak_reply D' (Or.inr (Or.inl (Nat.le_refl 4))) keep, fun X Y ws => ?_⟩⟩
  by_cases kx : K4 x y c
  · exact ⟨fun h => h.1 kx, Or.inr (Or.inr (Or.inl ⟨by omega, kx⟩))⟩
  by_cases sqx : Sq4 c X Y
  · obtain ⟨npr, nrr, nwr⟩ := hR x y X Y tw ws sqx kx
    have won' : Won x y c X Y p q m := ⟨kr2, nwr⟩
    have m1 : 1 ≤ m := by
      apply Classical.byContradiction
      intro z
      have m0 : m = 0 := by omega
      subst m0
      apply kx
      have k := kr2.1
      obtain ⟨hp, hq⟩ := kt
      unfold Ch at k
      unfold K4
      omega
    exact ⟨won_out hc u3 kt won' npr nrr,
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, q, m, kt, m1, by omega, won'⟩))))⟩
  · refine ⟨fun h => sqx h.2.1, Or.inl (push_out (domS_reply D' ws) hc ?_ sqx)⟩
    unfold K4 at kx
    omega

set_option maxHeartbeats 4000000 in
/-- Against a lone king that cannot touch the pawn next move the walk is safe. -/
theorem mv_far4 {j a b c e f p q m : Nat} (D : DomS a b c 4 e f) (hc : 2 ≤ c)
    (kt : KeyT c p q) (hj : m + 5 ≤ j) (won : Won a b c e f p q (m + 1)) (nk : ¬ K4 a b c)
    (nb : ¬ B4 a b c) (nbh : ¬ (b = 3 ∧ (a = c + 1 ∨ a + 1 = c))) (sq : Sq4 c e f)
    (far : ¬ Thr c e f) : Mv4 j a b c e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  have k2 := D.1.k2
  have k3 := D.1.k3
  have k4 := D.k4
  obtain ⟨kr, nwr⟩ := won
  have sq' := sq
  unfold Sq4 at sq'
  have far' := far
  unfold Thr Ch at far'
  refine mv_walk D hc kt hj kr nk nb nbh ?_ ?_ ?_
  · intro x y tw
    obtain ⟨kr2, near, hx, hy, npawn, xlt⟩ := kr_fwd hc u3 u1 u2 kt nk nb nbh k2 kr tw
    have cx := kr2.1
    apply Classical.byContradiction
    intro nap
    apply nwr
    obtain ⟨hp, hq⟩ := kt
    clear kr kr2 near tw nk nb nbh far sq
    unfold Ch at cx
    unfold Apart at nap
    rcases hp with rfl | hp <;> rcases hq with rfl | rfl <;>
      (unfold WR Cross Hit Ch; omega)
  · intro x y _ cap
    have t := cap.1
    unfold Near at t
    omega
  · intro x y X Y tw ws sqx kx
    obtain ⟨kr2, near, hx, hy, npawn, xlt⟩ := kr_fwd hc u3 u1 u2 kt nk nb nbh k2 kr tw
    obtain ⟨⟨n1, n2, n3, n4⟩, n5, n6⟩ := WeakStep.bounds ws
    have k8 := ws.k8
    have k6 := ws.k6
    unfold Sq4 at sqx
    refine ⟨fun pr => ?_, fun rr => ?_, fun w => nwr (wr_back hc kt ws.1 sq'.2.2 sqx.2.2 k4 k8 k6 ?_ w)⟩
    · have t := pr.1
      unfold Near at t
      omega
    · unfold Rr4 at rr
      omega
    · omega

set_option maxHeartbeats 4000000 in
/-- One step from a sixth-rank key square that the lone king does not cover. -/
theorem mv_arrive5 {j a b c e f p : Nat} (D : DomS a b c 4 e f) (hc : 2 ≤ c)
    (hp : p = c + 1 ∨ p + 1 = c) (hj : 3 ≤ j) (won : Won a b c e f p 5 1) (nk : ¬ K4 a b c) :
    Mv4 j a b c e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  have k2 := D.1.k2
  obtain ⟨kr, nwr⟩ := won
  have st : KingStep a b c 4 e f p 5 := by
    unfold K4 at nk
    unfold KR Thru Ch at kr
    unfold WR Cross Hit Ch at nwr
    unfold KingStep Near Apart
    omega
  have D' := dom_step4 D st
  have keep : ¬ Capture p 5 c 4 e f := by
    unfold Capture Near
    omega
  exact Or.inr ⟨j - 1, by omega, p, 5, st, w4win_key D' (by unfold K4; omega) (by omega) keep⟩

set_option maxHeartbeats 4000000 in
/-- One step from a seventh-rank key square, and from no free sixth-rank one: outside the
guard the lone king is not touching the pawn, so the king goes there. -/
theorem mv_arrive6 {j a b c e f p : Nat} (D : DomS a b c 4 e f) (hc : 2 ≤ c)
    (hp : p = c + 1 ∨ p + 1 = c) (hj : 3 ≤ j) (won : Won a b c e f p 6 1)
    (no5 : ¬ Won a b c e f p 5 1) (nk : ¬ K4 a b c) (nb : ¬ B4 a b c) (sq : Sq4 c e f)
    (out : ¬ S4 a b c e f) : Mv4 j a b c e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  have k1 := D.1.k1
  have k2 := D.1.k2
  have k4 := D.k4
  obtain ⟨kr, nwr⟩ := won
  have kr' := kr.1
  unfold Ch at kr'
  have nk' := nk
  unfold K4 at nk'
  have nb' := nb
  unfold B4 at nb'
  have sq' := sq
  unfold Sq4 at sq'
  have st : KingStep a b c 4 e f p 6 := by
    unfold WR Cross Hit Ch at nwr
    unfold KingStep Near Apart
    omega
  have D' := dom_step4 D st
  have keep : ¬ Capture p 6 c 4 e f := by
    intro cap
    have touch := cap.1
    apply out
    refine ⟨nk, sq, Or.inr ⟨nb, Or.inr (Or.inr (Or.inl ⟨touch, ?_, ?_⟩))⟩⟩
    · unfold Near
      omega
    · intro x' y' m1 m2 ap
      apply no5
      unfold Near at m1 m2 touch
      unfold Apart at ap k1
      refine ⟨⟨by unfold Ch; omega, Or.inl (by unfold Thru; omega)⟩, ?_⟩
      unfold WR Ch
      omega
  exact Or.inr ⟨j - 1, by omega, p, 6, st, w4win_key D' (by unfold K4; omega) (by omega) keep⟩

set_option maxHeartbeats 4000000 in
/-- A king diagonally behind the pawn that wins a race: the lone king is not near the two
squares that would stop a king beside the pawn. -/
theorem behind_far {a b c e f p q n : Nat} (D : DomS a b c 4 e f) (hc : 2 ≤ c)
    (side : a = c + 1 ∨ a + 1 = c) (hb : b = 3) (kt : KeyT c p q) (sq : Sq4 c e f)
    (won : Won a b c e f p q n) :
    Apart a 4 e f ∧ ¬ Ch e f c 6 1 ∧ ¬ Ch e f a 6 1 := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  have k1 := D.1.k1
  have k3 := D.1.k3
  have k4 := D.k4
  obtain ⟨kr, nwr⟩ := won
  obtain ⟨hp, hq⟩ := kt
  unfold Sq4 at sq
  unfold KR Thru Ch at kr
  apply Classical.byContradiction
  intro bad
  apply nwr
  unfold Apart Ch at bad
  rcases hp with rfl | hp <;> rcases hq with rfl | rfl <;>
    (unfold WR Cross Hit Ch; omega)

set_option maxHeartbeats 4000000 in
/-- From diagonally behind the pawn the king steps beside it. -/
theorem mv_behind4 {j a b c e f p q n : Nat} (D : DomS a b c 4 e f) (hc : 2 ≤ c) (hj : 4 ≤ j)
    (side : a = c + 1 ∨ a + 1 = c) (hb : b = 3) (kt : KeyT c p q) (sq : Sq4 c e f)
    (won : Won a b c e f p q n) : Mv4 j a b c e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  obtain ⟨ap, f1, f2⟩ := behind_far D hc side hb kt sq won
  have st : KingStep a b c 4 e f a 4 := by
    refine ⟨?_, u1, by omega, by omega, ap⟩
    unfold Near
    omega
  have D' := dom_step4 D st
  have keep : ¬ Capture a 4 c 4 e f := by
    unfold Capture Near
    omega
  have bx : B4 a 4 c := by unfold B4; omega
  refine Or.inr ⟨j - 1, by omega, a, 4, st, keep,
    weak_reply D' (Or.inr (Or.inl (Nat.le_refl 4))) keep, fun X Y ws => ?_⟩
  obtain ⟨⟨n1, n2, n3, n4⟩, n5, n6⟩ := WeakStep.bounds ws
  refine ⟨?_, Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, bx⟩)))⟩
  rintro ⟨-, -, ⟨-, hY, hX⟩ | ⟨nbx, -⟩⟩
  · unfold Ch at f1 f2
    omega
  · exact nbx bx

end EndgameChess.Rules.KPK.Coord
