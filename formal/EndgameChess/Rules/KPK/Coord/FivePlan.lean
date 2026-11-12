import EndgameChess.Rules.KPK.Coord.FiveRest

/-! The fifth rank of a bishop or centre pawn is classified: outside the guard the pawn
owner wins. Every position outside the guard has a phase, and each phase has its move. -/
namespace EndgameChess.Rules.KPK.Coord
open EndgameChess.KK

set_option maxHeartbeats 4000000 in
/-- No race won, lone king two files out. -/
theorem rest_u {a b c f t o u n : Nat} (D : DomS a b c 4 u f) (hc : 2 ≤ c) (sd : Sd c t o u)
    (sq : Sq4 c u f) (nk : ¬ K4 a b c) (nb : ¬ B4 a b c) (rt5 : Rc a b c u f t 5)
    (rt6 : Rc a b c u f t 6) (ro5 : Rc a b c u f o 5) (ro6 : Rc a b c u f o 6)
    (nb1 : t = c + 1 → ¬ (c < u ∧ u < a ∧ (f ≤ 6 ∨ b ≤ 3)))
    (nb2 : t + 1 = c → ¬ (u < c ∧ a < u ∧ (f ≤ 6 ∨ b ≤ 3)))
    (kw : Ch a b u 5 n ∨ Ch a b u 6 n) (lw : ¬ Ch u f c 5 n ∧ ¬ Ch u f c 6 n)
    (nop : ¬ Op4 a b c u f) : PushOK a b c u f ∨ RestM 7 a b c u f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  have k1 := D.1.k1
  have sd' := sd
  unfold Sd at sd'
  unfold Sq4 at sq
  have n1 : n ≤ 1 := by
    unfold Ch at lw
    omega
  have ha : a = t ∨ a = u ∨ Sw c u a := by
    unfold Ch at kw
    unfold Sw
    omega
  have hb : b = 4 ∨ b = 5 ∨ b = 6 ∨ b = 7 := by
    unfold Ch at kw
    omega
  have z5 : ¬ KR a b c o 5 2 := nokr ro5 (by unfold WR Cross Hit Ch; omega)
  have z6 : ¬ KR a b c o 6 2 := nokr ro6 (by unfold WR Cross Hit Ch; omega)
  have y5 : f = 7 → ¬ KR a b c t 5 1 :=
    fun h => nokr rt5 (by subst h; unfold WR Cross Hit Ch; omega)
  have y6 : f = 4 → ¬ KR a b c t 6 1 :=
    fun h => nokr rt6 (by subst h; unfold WR Cross Hit Ch; omega)
  have x5 : f = 4 → ¬ KR a b c o 5 3 :=
    fun h => nokr ro5 (by subst h; unfold WR Cross Hit Ch; omega)
  have x6 : f = 4 → ¬ KR a b c o 6 3 :=
    fun h => nokr ro6 (by subst h; unfold WR Cross Hit Ch; omega)
  unfold K4 at nk
  unfold B4 at nb
  unfold Apart at k1
  unfold Op4 at nop
  unfold KR Thru Ch at z5 z6 y5 y6 x5 x6
  clear lw rt5 rt6 ro5 ro6 kw
  have row : f = 4 ∨ f = 5 ∨ f = 6 ∨ f = 7 := by omega
  rcases ha with rfl | rfl | sw
  · exfalso
    rcases sd' with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> subst h3 <;>
    rcases row with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;> omega
  · rcases sd' with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> subst h3 <;>
    rcases row with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
      first
      | (exfalso; omega)
      | (left; exact push_ku D hc sd rfl (by omega) (by omega))
  · have sw' := sw
    unfold Sw at sw'
    rcases sd' with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;> subst h3 <;>
    rcases row with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
      first
      | (exfalso; omega)
      | (right; exact ⟨_, a, sw, Or.inr (Or.inr (Or.inl ⟨by omega, rfl, by omega, rfl, rfl⟩))⟩)

set_option maxHeartbeats 4000000 in
/-- No race won, lone king three files out. -/
theorem rest_w {a b c f t o u w n : Nat} (D : DomS a b c 4 w f) (hc : 2 ≤ c) (sd : Sd c t o u)
    (sw : Sw c u w) (sq : Sq4 c w f) (ro6 : Rc a b c w f o 6)
    (nb1 : t = c + 1 → ¬ (c < w ∧ w < a ∧ (f ≤ 6 ∨ b ≤ 3)))
    (nb2 : t + 1 = c → ¬ (w < c ∧ a < w ∧ (f ≤ 6 ∨ b ≤ 3)))
    (kw : Ch a b u 5 n ∨ Ch a b u 6 n) (lw : ¬ Ch w f c 5 n ∧ ¬ Ch w f c 6 n)
    (nop : ¬ Op4 a b c w f) : PushOK a b c w f ∨ RestM 7 a b c w f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  have k1 := D.1.k1
  have sd' := sd
  unfold Sd at sd'
  have sw' := sw
  unfold Sw at sw'
  unfold Sq4 at sq
  have n2 : n ≤ 2 := by
    unfold Ch at lw
    omega
  have z6 : ¬ KR a b c o 6 3 := nokr ro6 (by unfold WR Cross Hit Ch; omega)
  have aw : (a = w ∨ (u = c + 2 ∧ a = w + 1)) ∧ 3 ≤ b := by
    unfold KR Thru Ch at z6
    unfold Ch at kw
    omega
  clear z6 ro6 lw
  unfold Apart at k1
  unfold Op4 at nop
  unfold Ch at kw
  have row : f = 4 ∨ f = 5 ∨ f = 6 ∨ f = 7 := by omega
  have hb : b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6 ∨ b = 7 := by omega
  obtain ⟨aw, -⟩ := aw
  rcases aw with rfl | ⟨hu, rfl⟩
  · rcases row with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl | rfl <;>
      first
      | (exfalso; omega)
      | (left; exact push_kw D hc sw (by omega) (by omega) (by intro h; unfold Ch; omega))
      | (right; exact ⟨u, _, sw, Or.inl ⟨by omega, rfl, rfl, rfl, rfl⟩⟩)
      | (right; exact ⟨u, _, sw, Or.inr (Or.inl ⟨by omega, rfl, rfl, rfl, rfl⟩)⟩)
  · rcases row with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl | rfl <;>
      first
      | (exfalso; omega)
      | (right; exact ⟨u, w, sw, Or.inr (Or.inr (Or.inr
          ⟨by omega, hu, rfl, by omega, rfl, rfl⟩))⟩)

/-- Inside the square with no race won: the pawn advances, or the position is one of the
few that need a king step first. -/
theorem rest_ph {a b c e f : Nat} (D : DomS a b c 4 e f) (hc : 2 ≤ c) (nk : ¬ K4 a b c)
    (nb : ¬ B4 a b c) (sq : Sq4 c e f) (out : ¬ S4 a b c e f)
    (nr : ∀ p q n, KeyT c p q → 1 ≤ n → ¬ Won a b c e f p q n) :
    PushOK a b c e f ∨ RestM 7 a b c e f := by
  have rc (p q : Nat) (kt : KeyT c p q) : Rc a b c e f p q := rc_of_none nk kt nr
  have r4 : Rc4 a b c e f :=
    ⟨rc _ _ ⟨Or.inl rfl, Or.inl rfl⟩, rc _ _ ⟨Or.inl rfl, Or.inr rfl⟩,
      rc _ _ ⟨Or.inr (by omega), Or.inl rfl⟩, rc _ _ ⟨Or.inr (by omega), Or.inr rfl⟩⟩
  have nm : ¬ M4 a b c e f := fun m => out ⟨nk, sq, Or.inr ⟨nb, Or.inr (Or.inl m)⟩⟩
  have nop : ¬ Op4 a b c e f := fun m => out ⟨nk, sq, Or.inr ⟨nb, Or.inl m⟩⟩
  obtain ⟨t, o, u, sd, rt5, rt6, ro5, ro6, nb1, nb2, n, kw, lw⟩ := rest_side hc r4 nm
  obtain ⟨hf, -⟩ := rest_file D hc sd sq rt5 rt6 kw lw
  rcases hf with rfl | sw
  · exact rest_u D hc sd sq nk nb rt5 rt6 ro5 ro6 nb1 nb2 kw lw nop
  · exact rest_w D hc sd sw sq ro6 nb1 nb2 kw lw nop

set_option maxHeartbeats 4000000 in
/-- Every position outside the guard has a phase. -/
theorem five_cover {a b c e f : Nat} (D : DomS a b c 4 e f) (hc : 2 ≤ c)
    (out : ¬ S4 a b c e f) : Ph4 12 a b c e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  by_cases k : K4 a b c
  · exact Or.inr (Or.inr (Or.inl ⟨by omega, k⟩))
  by_cases bes : B4 a b c
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, bes⟩)))
  by_cases sq : Sq4 c e f
  · by_cases hw : ∃ p q n, KeyT c p q ∧ 1 ≤ n ∧ Won a b c e f p q n
    · obtain ⟨p, q, n, kt, n1, won⟩ := hw
      refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨p, q, n, kt, n1, ?_, won⟩))))
      have nw := won.2
      obtain ⟨hp, hq⟩ := kt
      unfold Sq4 at sq
      apply Classical.byContradiction
      intro big
      apply nw
      rcases hp with rfl | hp <;> rcases hq with rfl | rfl <;>
        (unfold WR Cross Hit Ch; omega)
    · have nr : ∀ p q n, KeyT c p q → 1 ≤ n → ¬ Won a b c e f p q n :=
        fun p q n kt n1 won => hw ⟨p, q, n, kt, n1, won⟩
      rcases rest_ph D hc k bes sq out nr with h | h
      · exact Or.inl h
      · exact ph4_mono (i := 7) (by omega) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
  · refine Or.inl (push_out D hc ?_ sq)
    unfold K4 at k
    omega

/-- Every phase has its move. -/
theorem mv4 {j a b c e f : Nat} (D : DomS a b c 4 e f) (hc : 2 ≤ c) (out : ¬ S4 a b c e f)
    (ph : Ph4 j a b c e f) : Mv4 j a b c e f := by
  rcases ph with h | ⟨hj, ha, hb⟩ | ⟨hj, k⟩ | ⟨hj, bes⟩ | ⟨p, q, n, kt, n1, nj, won⟩ | rest
  · exact Or.inl h
  · exact mv_front D hc hj ha hb
  · exact mv_key D hc hj k
  · exact mv_beside4 D hc hj bes out
  · by_cases k : K4 a b c
    · exact mv_key D hc (by omega) k
    by_cases bes : B4 a b c
    · exact mv_beside4 D hc (by omega) bes out
    by_cases sq : Sq4 c e f
    · exact mv_race D hc kt n1 nj won k bes sq out
    · refine Or.inl (push_out D hc ?_ sq)
      unfold K4 at k
      omega
  · exact mv_rest D hc rest

theorem strongPush_mono {V V2 : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Prop}
    {a b c d e f : Nat} (sub : ∀ l a b c d e f, V l a b c d e f → V2 l a b c d e f)
    (h : StrongPush V a b c d e f) : StrongPush V2 a b c d e f := by
  rcases h with ⟨fr, le, l, hl, w⟩ | ⟨d1, fr, fr2, l, hl, w⟩ | h | h
  · exact Or.inl ⟨fr, le, l, hl, sub _ _ _ _ _ _ _ w⟩
  · exact Or.inr (Or.inl ⟨d1, fr, fr2, l, hl, sub _ _ _ _ _ _ _ w⟩)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

/-- The winning plan on the fifth, sixth and seventh ranks. -/
def fivePlan : Plan where
  S j a b c d e f := sixPlan.S j a b c d e f ∨
    (d = 4 ∧ 2 ≤ c ∧ j ≤ 12 ∧ ¬ S4 a b c e f ∧ Ph4 j a b c e f)
  W j a b c d e f := sixPlan.W j a b c d e f ∨ (d = 4 ∧ 2 ≤ c ∧ j ≤ 12 ∧ W4win j a b c e f)
  S_le := by
    intro j a b c d e f h
    rcases h with h | h
    · exact sixPlan.S_le h
    · have := h.2.2.1
      omega
  W_le := by
    intro j a b c d e f h
    rcases h with h | h
    · exact sixPlan.W_le h
    · have := h.2.2.1
      omega
  strong := by
    intro j a b c d e f D h
    rcases h with h | ⟨rfl, hc, hj, out, ph⟩
    · rcases sixPlan.strong D h with q | ⟨i, rfl, x, y, st, w⟩
      · exact Or.inl (strongPush_mono (fun _ _ _ _ _ _ _ w => Or.inl w) q)
      · exact Or.inr ⟨i, rfl, x, y, st, Or.inl w⟩
    · rcases mv4 D hc out ph with ⟨fr, w5⟩ | ⟨i, rfl, x, y, st, w⟩
      · exact Or.inl (Or.inl ⟨fr, by omega, 10, by omega,
          Or.inl ⟨hc, by omega, Or.inr (Or.inr ⟨rfl, w5⟩)⟩⟩)
      · exact Or.inr ⟨i, rfl, x, y, st, Or.inr ⟨rfl, hc, by omega, w⟩⟩
  weak := by
    intro j a b c d e f D h
    rcases h with h | ⟨rfl, hc, hj, keep, reply, all⟩
    · obtain ⟨q1, q2, q3⟩ := sixPlan.weak D h
      refine ⟨q1, q2, fun x y st => ?_⟩
      obtain ⟨i, le, s⟩ := q3 x y st
      exact ⟨i, le, Or.inl s⟩
    · exact ⟨keep, reply, fun x y st =>
        ⟨j, Nat.le_refl j, Or.inr ⟨rfl, hc, hj, (all x y st).1, (all x y st).2⟩⟩⟩

/-- A bishop or centre pawn on the fifth rank, pawn owner to move, outside the guard: an
actual win. With `fresh_five_hold` this classifies these roots. -/
theorem fresh_fifth_win {σ : Colour} {q : Position} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk) (turn : q.turn = σ)
    (safe : ¬ PawnSees σ ps wk) (file : 2 ≤ mx ps ps) (rank : height σ ps = 4)
    (out : ¬ S4 (mx ps sk) (height σ sk) (mx ps ps) (mx ps wk) (height σ wk)) :
    FreshGame.Within σ 604 (FreshGame.fresh q) := by
  have cfg := fresh_cfg h fresh
  have D : DomS (mx ps sk) (height σ sk) (mx ps ps) (height σ ps) (mx ps wk) (height σ wk) :=
    ⟨dom_of_cfg cfg, fun attack => safe ((att_iff σ ps wk).mpr attack)⟩
  rw [rank] at D
  exact fresh_plan_strong (P := fivePlan) (j := 12) h fresh turn safe
    (Or.inr ⟨rank, file, Nat.le_refl 12, out, five_cover D file out⟩)

/-- Fifth rank, lone king to move: if it cannot take the pawn and no move reaches the
guard, the pawn owner wins. -/
theorem fresh_fifth_weak_win {σ : Colour} {q : Position} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk) (turn : q.turn = σ.opp)
    (file : 2 ≤ mx ps ps) (rank : height σ ps = 4)
    (keep : ¬ Capture (mx ps sk) (height σ sk) (mx ps ps) 4 (mx ps wk) (height σ wk))
    (all : ∀ x y, WeakStep (mx ps sk) (height σ sk) (mx ps ps) 4 (mx ps wk) (height σ wk) x y →
      ¬ S4 (mx ps sk) (height σ sk) (mx ps ps) x y) :
    FreshGame.Within σ 604 (FreshGame.fresh q) := by
  have cfg := fresh_cfg h fresh
  have D : Dom (mx ps sk) (height σ sk) (mx ps ps) (height σ ps) (mx ps wk) (height σ wk) :=
    dom_of_cfg cfg
  rw [rank] at D
  exact fresh_plan_weak (P := fivePlan) (j := 12) h fresh turn
    (Or.inr ⟨rank, file, Nat.le_refl 12, keep,
      weak_reply D (Or.inr (Or.inl (Nat.le_refl 4))) keep,
      fun x y st => ⟨all x y st, five_cover (domS_reply D st) file (all x y st)⟩⟩)

/-- Fifth rank, lone king to move: it takes the pawn or steps into the guard, and holds. -/
theorem fresh_fifth_weak_hold {σ : Colour} {q : Position} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk) (turn : q.turn = σ.opp)
    (file : 2 ≤ mx ps ps) (rank : height σ ps = 4)
    (w : W4 (mx ps sk) (height σ sk) (mx ps ps) (mx ps wk) (height σ wk)) :
    FreshGame.Hold σ.opp (FreshGame.fresh q) ∧ ∀ n, ¬ MateWithin σ n q :=
  fresh_guard_weak (G := fiveGuard) h fresh turn (Or.inr ⟨rank, file, w⟩)

end EndgameChess.Rules.KPK.Coord
