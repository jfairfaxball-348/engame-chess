import EndgameChess.Rules.KPK.Coord.Four2

/-! Fourth rank: the push with the king on the sixth or seventh rank, and the guard. -/
namespace EndgameChess.Rules.KPK.Coord

set_option maxHeartbeats 4000000 in
/-- Beside the pawn with the king two files or more out on that side: the lone king takes
the pawn next. -/
theorem s4_beside_far {a b c u : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (hb : 5 ≤ b)
    (side : (u = c + 1 ∧ c + 2 ≤ a) ∨ (u + 1 = c ∧ a + 2 ≤ c)) : S4 a b c u 4 := by
  refine ⟨by unfold K4; omega, by unfold Sq4; omega, Or.inr ⟨by unfold B4; omega,
    Or.inr (Or.inr (Or.inl ⟨by unfold Near; omega, by unfold Near; omega, ?_⟩))⟩⟩
  intro x y n1 n2
  unfold Near at n1 n2
  unfold Apart
  omega

set_option maxHeartbeats 4000000 in
theorem m4_q5 {c : Nat} (hc : 1 ≤ c) : M4 (c + 4) 5 c (c + 2) 4 := by m4c

set_option maxHeartbeats 4000000 in
theorem m4_q6 {c : Nat} (hc : 1 ≤ c) : M4 (c + 4) 6 c (c + 2) 4 := by m4c

set_option maxHeartbeats 4000000 in
/-- The king two ranks above the lone king blocks its step up: the lone king steps one file
towards the pawn instead. -/
theorem push_blocked {a b c e f : Nat} (D : DomS a b c 3 e f) (hc : 1 ≤ c) (h : S3 a b c e f)
    (fr : Free a b e f c 4) (hb : b = f + 2) (b56 : b = 5 ∨ b = 6) (adj : a ≤ e + 1 ∧ e ≤ a + 1)
    (ncap : ¬ Capture a b c 4 e f) : W4 a b c e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  obtain ⟨hf, B, hl, ap, s⟩ := h
  have hB : B = b + 1 := by unfold Lift at hl; omega
  subst hB
  have D' := dom_lift D hl hf ap
  have k3 := D.1.k3
  have k4' := D'.k4
  obtain ⟨nk, sq, rest⟩ := s
  unfold Free at fr
  have cs : (e = c + 2 ∧ c + 2 ≤ a ∧ (b = 6 ∨ c + 3 ≤ a)) ∨
      (e + 2 = c ∧ a + 2 ≤ c ∧ (b = 6 ∨ a + 3 ≤ c)) ∨
      (e = c + 3 ∧ ((a = c + 3 ∧ b = 6) ∨ a = c + 4)) ∨ (e + 3 = c ∧ a + 3 = c ∧ b = 6) := by
    rcases rest with ⟨bes, -, -⟩ | ⟨-, op | m | pr | rr⟩
    · unfold B4 at bes; omega
    · unfold Op4 at op
      unfold Sq4 at sq
      omega
    · have f34 : (b = 5 ∧ f = 3) ∨ (b = 6 ∧ f = 4) := by omega
      have he : e + 3 = c ∨ e + 2 = c ∨ e + 1 = c ∨ e = c ∨ e = c + 1 ∨ e = c + 2 ∨
          e = c + 3 := by
        have := sq
        unfold Sq4 at this
        omega
      have ha' : a + 1 = e ∨ a = e ∨ a = e + 1 := by omega
      obtain ⟨z1, z2, z3, z4, z5, z6⟩ := near4_of hc m
      have o1 : (c < e ∧ e < a) ∨ ¬ (Ch a (b + 1) (c + 2) 5 1 ∨ Ch a (b + 1) (c + 2) 6 1) ∨
          (Ch e (f + 1) c 5 1 ∨ Ch e (f + 1) c 6 1) := by
        rcases m.2.1 with q | q
        · exact Or.inl ⟨q.1, q.2.1⟩
        · by_cases g : Ch a (b + 1) (c + 2) 5 1 ∨ Ch a (b + 1) (c + 2) 6 1
          · exact Or.inr (Or.inr (q 1 g))
          · exact Or.inr (Or.inl g)
      have o2 : (e < c ∧ a < e) ∨ ¬ (Ch a (b + 1) (c - 2) 5 1 ∨ Ch a (b + 1) (c - 2) 6 1) ∨
          (Ch e (f + 1) c 5 1 ∨ Ch e (f + 1) c 6 1) := by
        rcases m.2.2 with q | q
        · exact Or.inl ⟨q.1, q.2.1⟩
        · by_cases g : Ch a (b + 1) (c - 2) 5 1 ∨ Ch a (b + 1) (c - 2) 6 1
          · exact Or.inr (Or.inr (q 1 g))
          · exact Or.inr (Or.inl g)
      clear m b56 hb D D' hl ap
      unfold Ch at z1 z2 z3 z4 z5 z6 o1 o2
      unfold Capture Near at ncap
      unfold Sq4 at sq
      unfold Att at k4'
      unfold K4 at nk
      rcases f34 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases ha' with rfl | rfl | rfl <;>
        rcases he with h | h | h | h | h | h | h <;> omega
    · exfalso
      obtain ⟨n1, n2, n3⟩ := pr
      apply ncap
      refine ⟨by unfold Near at n1 ⊢; omega, fun near => ?_⟩
      have := n3 a b (by unfold Near; omega) (by unfold Near at near ⊢; omega)
      unfold Apart at this
      unfold Near at near n2
      unfold K4 at nk
      omega
    · unfold Rr4 at rr; omega
  rcases cs with ⟨he, ha, hb'⟩ | ⟨he, ha, hb'⟩ | ⟨he, ha⟩ | ⟨he, ha, hb6⟩
  · exact Or.inr ⟨c + 1, 4, by ws, s4_beside_far hc u3 (by omega) (Or.inl ⟨rfl, ha⟩)⟩
  · exact Or.inr ⟨c - 1, 4, by ws, s4_beside_far hc u3 (by omega) (Or.inr ⟨by omega, ha⟩)⟩
  · have m : M4 a b c (c + 2) 4 := by
      rcases ha with ⟨rfl, rfl⟩ | rfl
      · exact m4_w6 hc (Or.inl ⟨rfl, rfl⟩)
      · rcases b56 with rfl | rfl
        · exact m4_q5 hc
        · exact m4_q6 hc
    exact Or.inr ⟨c + 2, 4, by ws, by unfold K4; omega, by unfold Sq4; omega,
      Or.inr ⟨by unfold B4; omega, Or.inr (Or.inl m)⟩⟩
  · have m : M4 a b c (c - 2) 4 := by
      subst hb6
      exact m4_w6 hc (Or.inr ⟨by omega, ha⟩)
    exact Or.inr ⟨c - 2, 4, by ws, by unfold K4; omega, by unfold Sq4; omega,
      Or.inr ⟨by unfold B4; omega, Or.inr (Or.inl m)⟩⟩

set_option maxHeartbeats 4000000 in
/-- Lowering a king on the sixth or seventh rank keeps the main race. -/
theorem m4_lower {a b c e f : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (hb : b = 5 ∨ b = 6) (ha : a ≤ 7)
    (sq : Sq4 c e f) (hf : f ≤ 7) (h : M4 a (b + 1) c e f) (ap : Apart a b e f)
    (nk : ¬ K4 a b c) (nx : ¬ HiEx a b c e f) : M4 a b c e f := by
  have N := near4_of hc h
  obtain ⟨⟨r1, r2, r3, r4⟩, o1, o2⟩ := h
  refine ⟨⟨rc_lower hc h3 hb (Or.inl rfl) (Or.inl rfl) ha sq hf r1 N ap nk nx,
    rc_lower hc h3 hb (Or.inl rfl) (Or.inr rfl) ha sq hf r2 N ap nk nx,
    rc_lower hc h3 hb (Or.inr (by omega)) (Or.inl rfl) ha sq hf r3 N ap nk nx,
    rc_lower hc h3 hb (Or.inr (by omega)) (Or.inr rfl) ha sq hf r4 N ap nk nx⟩, ?_, ?_⟩
  · by_cases left : c < e ∧ e < a ∧ (f ≤ 6 ∨ b ≤ 3)
    · exact Or.inl left
    rcases o1 with q | q
    · exact absurd ⟨q.1, q.2.1, by omega⟩ left
    have q1 : ¬ (Ch a (b + 1) (c + 2) 5 1 ∨ Ch a (b + 1) (c + 2) 6 1) ∨
        (Ch e f c 5 1 ∨ Ch e f c 6 1) := by
      by_cases g : Ch a (b + 1) (c + 2) 5 1 ∨ Ch a (b + 1) (c + 2) 6 1
      · exact Or.inr (q 1 g)
      · exact Or.inl g
    refine Or.inr (oc_lower hb q (fun g => ?_))
    obtain ⟨z1, z2, z3, z4, z5, z6⟩ := N
    unfold Ch at z1 z2 z3 z4 z5 z6 q1 g ⊢
    unfold HiEx at nx
    unfold K4 at nk
    unfold Sq4 at sq
    unfold Apart at ap
    omega
  · by_cases left : e < c ∧ a < e ∧ (f ≤ 6 ∨ b ≤ 3)
    · exact Or.inl left
    rcases o2 with q | q
    · exact absurd ⟨q.1, q.2.1, by omega⟩ left
    have q1 : ¬ (Ch a (b + 1) (c - 2) 5 1 ∨ Ch a (b + 1) (c - 2) 6 1) ∨
        (Ch e f c 5 1 ∨ Ch e f c 6 1) := by
      by_cases g : Ch a (b + 1) (c - 2) 5 1 ∨ Ch a (b + 1) (c - 2) 6 1
      · exact Or.inr (q 1 g)
      · exact Or.inl g
    refine Or.inr (oc_lower hb q (fun g => ?_))
    obtain ⟨z1, z2, z3, z4, z5, z6⟩ := N
    unfold Ch at z1 z2 z3 z4 z5 z6 q1 g ⊢
    unfold HiEx at nx
    unfold K4 at nk
    unfold Sq4 at sq
    unfold Apart at ap
    omega

set_option maxHeartbeats 4000000 in
/-- The push answered with the king on the sixth or seventh rank. -/
theorem s3_push_high {a b c e f : Nat} (D : DomS a b c 3 e f) (hc : 1 ≤ c) (h : S3 a b c e f)
    (fr : Free a b e f c 4) (hb : b = 5 ∨ b = 6) : W4 a b c e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  by_cases cap : Capture a b c 4 e f
  · exact Or.inl cap
  by_cases blk : b = f + 2 ∧ a ≤ e + 1 ∧ e ≤ a + 1
  · exact push_blocked D hc h fr blk.1 hb blk.2 cap
  have hh := h
  obtain ⟨hf, B, hl, ap, s⟩ := hh
  have hB : B = b + 1 := by unfold Lift at hl; omega
  subst hB
  have D2 := dom_lift D hl hf ap
  have k1 : Apart a b e f := D.1.k1
  have k3 := D.1.k3
  have k4 := D2.k4
  have sqf : 4 ≤ f + 1 := s.2.1.2.2
  unfold Free at fr
  by_cases hx : HiEx a b c e (f + 1)
  · unfold HiEx at hx
    obtain ⟨rfl, rfl, f6, side⟩ := hx
    have f5 : f = 6 := by omega
    subst f5
    refine Or.inr ⟨e, 5, ?_, s4_center hc rfl (Or.inl rfl) (by unfold K4; omega)
      (by unfold B4; omega)⟩
    unfold WeakStep Near Apart Att
    unfold Apart at k1
    omega
  have apU : Apart a b e (f + 1) := by
    unfold Apart at k1 ⊢
    omega
  have step : WeakStep a b c 4 e f e (f + 1) := by
    unfold WeakStep Near Apart Att
    unfold Apart at apU
    unfold Att at k4
    omega
  obtain ⟨nk, sq, rest⟩ := s
  have nb : ¬ B4 a b c := by unfold B4; omega
  rcases rest with ⟨bes, -, -⟩ | ⟨-, op | m | pr | rr⟩
  · unfold B4 at bes; omega
  · unfold Op4 at op; omega
  · have nk2 : ¬ K4 a b c := by
      intro k
      apply cap
      obtain ⟨z1, z2, z3, z4, -, -⟩ := near4_of hc m
      unfold Ch at z1 z2 z3 z4
      unfold K4 at k nk
      unfold Capture Near
      unfold Apart at k1
      omega
    exact Or.inr ⟨e, f + 1, step, nk2, sq, Or.inr ⟨nb,
      Or.inr (Or.inl (m4_lower hc u3 hb u1 sq (by omega) m apU nk2 hx))⟩⟩
  · exfalso
    obtain ⟨n1, n2, n3⟩ := pr
    apply cap
    refine ⟨by unfold Near at n1 ⊢; omega, fun near => ?_⟩
    have := n3 a b (by unfold Near; omega) (by unfold Near at near ⊢; omega)
    unfold Apart at this
    unfold Near at near n2
    unfold K4 at nk
    omega
  · have nk2 : ¬ K4 a b c := by unfold Rr4 at rr; unfold K4; omega
    exact Or.inr ⟨e, f + 1, step, nk2, sq, Or.inr ⟨nb, Or.inr (Or.inr (Or.inr rr))⟩⟩

/-- After the push from the fourth rank the lone king has its answer in the fifth-rank
guard. -/
theorem s3_push {a b c e f : Nat} (D : DomS a b c 3 e f) (hc : 1 ≤ c) (h : S3 a b c e f)
    (fr : Free a b e f c 4) : W4 a b c e f := by
  have u2 := D.bounds.2.1
  by_cases hb : b = 5 ∨ b = 6
  · exact s3_push_high D hc h fr hb
  · exact s3_push_low D hc h fr (by omega)

/-- Pawn on the fourth to seventh rank, any non-rook file. -/
def fourGuard : Guard where
  S a b c d e f := fiveGuard.S a b c d e f ∨ knFiveGuard.S a b c d e f ∨
    (d = 3 ∧ 1 ≤ c ∧ S3 a b c e f)
  W a b c d e f := fiveGuard.W a b c d e f ∨ knFiveGuard.W a b c d e f ∨
    (d = 3 ∧ 1 ≤ c ∧ W3 a b c e f)
  strong := by
    intro a b c d e f D h
    rcases h with h | h | ⟨rfl, hc, h⟩
    · obtain ⟨q1, q2, q3, q4⟩ := fiveGuard.strong D h
      exact ⟨fun x y s => Or.inl (q1 x y s), fun p r => Or.inl (q2 p r),
        fun p r t => Or.inl (q3 p r t), q4⟩
    · obtain ⟨q1, q2, q3, q4⟩ := knFiveGuard.strong D h
      exact ⟨fun x y s => Or.inr (Or.inl (q1 x y s)), fun p r => Or.inr (Or.inl (q2 p r)),
        fun p r t => Or.inr (Or.inl (q3 p r t)), q4⟩
    · refine ⟨fun x y st => Or.inr (Or.inr ⟨rfl, hc, s3_king D hc h st⟩), fun fr _ => ?_,
        fun q => by omega, fun q => by omega⟩
      have w := s3_push D hc h fr
      by_cases c1 : c = 1
      · subst c1
        exact Or.inr (Or.inl (Or.inr ⟨rfl, rfl, w⟩))
      · exact Or.inl (Or.inr ⟨rfl, by omega, w⟩)
  weak := by
    intro a b c d e f D h
    rcases h with h | h | ⟨rfl, hc, h⟩
    · rcases fiveGuard.weak D h with q | q | ⟨x, y, st, q⟩
      · exact Or.inl q
      · exact Or.inr (Or.inl q)
      · exact Or.inr (Or.inr ⟨x, y, st, Or.inl q⟩)
    · rcases knFiveGuard.weak D h with q | q | ⟨x, y, st, q⟩
      · exact Or.inl q
      · exact Or.inr (Or.inl q)
      · exact Or.inr (Or.inr ⟨x, y, st, Or.inr (Or.inl q)⟩)
    · rcases h with q | ⟨x, y, st, q⟩
      · exact Or.inl q
      · exact Or.inr (Or.inr ⟨x, y, st, Or.inr (Or.inr ⟨rfl, hc, q⟩)⟩)

open EndgameChess.KK in
/-- Non-rook pawn on the fourth rank, a fresh root in the lifted fifth-rank region with the
pawn owner to move: the lone king holds, and no forced mate exists at any length. -/
theorem fresh_four_hold {σ : Colour} {q : Position} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk) (turn : q.turn = σ)
    (safe : ¬ PawnSees σ ps wk) (file : 1 ≤ mx ps ps) (rank : height σ ps = 3)
    (sat : S3 (mx ps sk) (height σ sk) (mx ps ps) (mx ps wk) (height σ wk)) :
    FreshGame.Hold σ.opp (FreshGame.fresh q) ∧ ∀ n, ¬ MateWithin σ n q :=
  fresh_guard_strong (G := fourGuard) h fresh turn safe (Or.inr (Or.inr ⟨rank, file, sat⟩))

open EndgameChess.KK in
/-- Non-rook pawn on the fourth rank, lone king to move: it holds if it takes the pawn or
steps into the region. -/
theorem fresh_four_weak_hold {σ : Colour} {q : Position} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk) (turn : q.turn = σ.opp)
    (file : 1 ≤ mx ps ps) (rank : height σ ps = 3)
    (w : W3 (mx ps sk) (height σ sk) (mx ps ps) (mx ps wk) (height σ wk)) :
    FreshGame.Hold σ.opp (FreshGame.fresh q) ∧ ∀ n, ¬ MateWithin σ n q :=
  fresh_guard_weak (G := fourGuard) h fresh turn (Or.inr (Or.inr ⟨rank, file, w⟩))

end EndgameChess.Rules.KPK.Coord
