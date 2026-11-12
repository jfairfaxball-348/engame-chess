import EndgameChess.Rules.KPK.Coord.FiveClose

/-! Fifth-rank wins: the positions inside the pawn's square where no race is won. The
king stands two or three files out next to the opposed-file squares; the pawn advances,
or one king step inwards comes first. -/
namespace EndgameChess.Rules.KPK.Coord

theorem nokr {a b c e f p q k : Nat} (h : Rc a b c e f p q) (far : ¬ WR e f c p q k) :
    ¬ KR a b c p q k := fun kr => far (h k kr)

/-- With no race won the lone king is at least as close to every key square. -/
theorem rc_of_none {a b c e f p q : Nat} (nk : ¬ K4 a b c) (kt : KeyT c p q)
    (nr : ∀ p q n, KeyT c p q → 1 ≤ n → ¬ Won a b c e f p q n) : Rc a b c e f p q := by
  intro n kr
  apply Classical.byContradiction
  intro nw
  by_cases n0 : n = 0
  · subst n0
    apply nk
    have k := kr.1
    obtain ⟨hp, hq⟩ := kt
    unfold Ch at k
    unfold K4
    omega
  · exact nr p q n kt (by omega) ⟨kr, nw⟩

/-- If every race is level but the main race clause fails, the king is nearer to an outer
file than the lone king is to the pawn's file. -/
theorem rest_side {a b c e f : Nat} (hc : 2 ≤ c) (r : Rc4 a b c e f) (nm : ¬ M4 a b c e f) :
    ∃ t o u, Sd c t o u ∧ Rc a b c e f t 5 ∧ Rc a b c e f t 6 ∧ Rc a b c e f o 5 ∧
      Rc a b c e f o 6 ∧
      (t = c + 1 → ¬ (c < e ∧ e < a ∧ (f ≤ 6 ∨ b ≤ 3))) ∧
      (t + 1 = c → ¬ (e < c ∧ a < e ∧ (f ≤ 6 ∨ b ≤ 3))) ∧
      ∃ n, (Ch a b u 5 n ∨ Ch a b u 6 n) ∧ ¬ Ch e f c 5 n ∧ ¬ Ch e f c 6 n := by
  have wit (u : Nat) (h : ¬ Oc a b c e f u) :
      ∃ n, (Ch a b u 5 n ∨ Ch a b u 6 n) ∧ ¬ Ch e f c 5 n ∧ ¬ Ch e f c 6 n := by
    apply Classical.byContradiction
    intro no
    apply h
    intro n kr
    apply Classical.byContradiction
    intro nw
    exact no ⟨n, kr, fun x => nw (Or.inl x), fun x => nw (Or.inr x)⟩
  obtain ⟨r1, r2, r3, r4⟩ := r
  by_cases hr : Ocr a b c e f
  · by_cases hl : Ocl a b c e f
    · exact (nm ⟨⟨r1, r2, r3, r4⟩, hr, hl⟩).elim
    · refine ⟨c - 1, c + 1, c - 2, Or.inr ⟨by omega, rfl, by omega⟩, r3, r4, r1, r2,
        fun h => by omega, fun _ g => hl (Or.inl g), wit _ (fun g => hl (Or.inr g))⟩
  · exact ⟨c + 1, c - 1, c + 2, Or.inl ⟨rfl, by omega, rfl⟩, r1, r2, r3, r4,
      fun _ g => hr (Or.inl g), fun h => by omega, wit _ (fun g => hr (Or.inr g))⟩

set_option maxHeartbeats 4000000 in
/-- The lone king then stands two or three files out on that side. -/
theorem rest_file {a b c e f t o u n : Nat} (D : DomS a b c 4 e f) (hc : 2 ≤ c)
    (sd : Sd c t o u) (sq : Sq4 c e f) (rt5 : Rc a b c e f t 5) (rt6 : Rc a b c e f t 6)
    (kw : Ch a b u 5 n ∨ Ch a b u 6 n) (lw : ¬ Ch e f c 5 n ∧ ¬ Ch e f c 6 n) :
    (e = u ∨ Sw c u e) ∧ n ≤ 2 := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  have k1 := D.1.k1
  have k3 := D.1.k3
  have k4 := D.k4
  unfold Sd at sd
  unfold Sq4 at sq
  have n2 : n ≤ 2 := by
    unfold Ch at lw
    omega
  have nt : ¬ Thru a b c t 5 := by
    unfold Ch at kw
    unfold Thru
    omega
  have f5 : Ch a b t 5 (n + 1) → Ch e f t 5 (n + 1) := fun g => (rt5 (n + 1) ⟨g, Or.inl nt⟩).1
  have f6 : Ch a b t 6 (n + 1) → Ch e f t 6 (n + 1) :=
    fun g => (rt6 (n + 1) ⟨g, Or.inl (by unfold Thru; omega)⟩).1
  refine ⟨?_, n2⟩
  unfold Apart at k1
  have ncases : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases ncases with rfl | rfl | rfl <;> rcases kw with kw | kw <;>
    (unfold Ch at f5 f6 kw lw; unfold Sw; omega)

set_option maxHeartbeats 4000000 in
/-- A king two files out on the fourth to sixth rank, lone king no nearer the pawn's
file: the position is outside the guard. -/
theorem out_ku {a b c e f t o u : Nat} (hc : 2 ≤ c) (sd : Sd c t o u) (ha : a = u)
    (hb : 4 ≤ b ∧ b ≤ 6) (he : (u = c + 2 ∧ u ≤ e) ∨ (u + 2 = c ∧ e ≤ u)) : ¬ S4 a b c e f := by
  unfold Sd at sd
  rintro ⟨-, sq, ⟨bes, -, -⟩ | ⟨-, op | m4 | pr | rr⟩⟩
  · unfold B4 at bes
    omega
  · unfold Op4 at op
    omega
  · obtain ⟨-, o1, o2⟩ := m4
    have key (g : Oc a b c e f u) : False := by
      have h := g 1 (Or.inl (by unfold Ch; omega))
      unfold Ch at h
      omega
    rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rcases o1 with q | q
      · omega
      · have e1 : u = c + 2 := h1
        subst e1
        exact key q
    · rcases o2 with q | q
      · omega
      · have e1 : u = c - 2 := by omega
        subst e1
        exact key q
  · have tch := pr.1
    unfold Near at tch
    omega
  · unfold Rr4 at rr
    omega

set_option maxHeartbeats 4000000 in
/-- The same king: the pawn advances. -/
theorem push_ku {a b c e f t o u : Nat} (D : DomS a b c 4 e f) (hc : 2 ≤ c) (sd : Sd c t o u)
    (ha : a = u) (hb : 4 ≤ b ∧ b ≤ 6) (he : c + 2 ≤ e ∨ e + 2 ≤ c) : PushOK a b c e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  unfold Sd at sd
  refine pushOK_of D hc ⟨by omega, by omega⟩ (by unfold Capture Near; omega) (by omega) ?_
  intro x y st
  obtain ⟨⟨n1, n2, n3, n4⟩, n5, n6⟩ := WeakStep.bounds st
  exact nd_close hc (by unfold Arr Ch; omega) (by unfold Ch; omega) (by unfold Beside; omega)
    (by omega) (by unfold Bl Ch; omega)

set_option maxHeartbeats 4000000 in
/-- A king three files out, lone king no nearer the pawn's file: the pawn advances. -/
theorem push_kw {a b c e f u : Nat} (D : DomS a b c 4 e f) (hc : 2 ≤ c) (sw : Sw c u a)
    (hb : 3 ≤ b) (he : c + 3 ≤ e ∨ e + 3 ≤ c)
    (h37 : (b = 3 ∨ b = 7) → ¬ Ch e f u 5 1) : PushOK a b c e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  unfold Sw at sw
  refine pushOK_of D hc ⟨by omega, by omega⟩ (by unfold Capture Near; omega) (by omega) ?_
  intro x y st h
  obtain ⟨⟨n1, n2, n3, n4⟩, n5, n6⟩ := WeakStep.bounds st
  obtain ⟨-, b1, b2, b3, ⟨bs, -, -⟩ | ⟨-, h⟩⟩ := h
  · unfold Beside at bs
    omega
  rcases h with A | ⟨B, R⟩ | ⟨B, R⟩ | ⟨B, R⟩ | S | ⟨T, F⟩ | ⟨T, F⟩ | ⟨T, F⟩
  · omega
  · unfold Bl Ch at B
    omega
  · unfold Bl Ch at B
    omega
  · unfold Arr Ch at R
    omega
  · have g := h37 (by omega)
    unfold Ch at g
    omega
  · unfold Tc Ch at T
    omega
  · unfold Ch at F
    omega
  · unfold Ch at F
    omega

set_option maxHeartbeats 4000000 in
/-- King three files out below the pawn's rank, lone king on its file on the seventh: the
king steps inwards beside the pawn's rank. -/
theorem mv_r1 {j a b c e f u w : Nat} (D : DomS a b c 4 e f) (hc : 2 ≤ c) (sw : Sw c u w)
    (hj : 1 ≤ j) (ha : a = w) (hb : b = 3) (he : e = w) (hf : f = 6) : Mv4 j a b c e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  have sw' := sw
  unfold Sw at sw'
  obtain ⟨t, o, sd⟩ : ∃ t o, Sd c t o u := by
    rcases sw' with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact ⟨c + 1, c - 1, Or.inl ⟨rfl, by omega, h1⟩⟩
    · exact ⟨c - 1, c + 1, Or.inr ⟨by omega, rfl, h1⟩⟩
  have st : KingStep a b c 4 e f u 4 := by
    unfold KingStep Near Apart
    omega
  have D' := dom_step4 D st
  have keep : ¬ Capture u 4 c 4 e f := by
    unfold Capture Near
    omega
  refine Or.inr ⟨j - 1, by omega, u, 4, st, w4win_mono (Nat.zero_le _) ⟨keep,
    weak_reply D' (Or.inr (Or.inl (Nat.le_refl 4))) keep, fun X Y ws => ?_⟩⟩
  obtain ⟨⟨n1, n2, n3, n4⟩, n5, n6⟩ := WeakStep.bounds ws
  exact ⟨out_ku hc sd rfl (by omega) (by omega),
    Or.inl (push_ku (domS_reply D' ws) hc sd rfl (by omega) (by omega))⟩

set_option maxHeartbeats 4000000 in
/-- King three files out on the last rank, lone king on its file on the pawn's rank. -/
theorem mv_r2 {j a b c e f u w : Nat} (D : DomS a b c 4 e f) (hc : 2 ≤ c) (sw : Sw c u w)
    (hj : 1 ≤ j) (ha : a = w) (hb : b = 7) (he : e = w) (hf : f = 4) : Mv4 j a b c e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  have sw' := sw
  unfold Sw at sw'
  obtain ⟨t, o, sd⟩ : ∃ t o, Sd c t o u := by
    rcases sw' with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact ⟨c + 1, c - 1, Or.inl ⟨rfl, by omega, h1⟩⟩
    · exact ⟨c - 1, c + 1, Or.inr ⟨by omega, rfl, h1⟩⟩
  have st : KingStep a b c 4 e f u 6 := by
    unfold KingStep Near Apart
    omega
  have D' := dom_step4 D st
  have keep : ¬ Capture u 6 c 4 e f := by
    unfold Capture Near
    omega
  refine Or.inr ⟨j - 1, by omega, u, 6, st, w4win_mono (Nat.zero_le _) ⟨keep,
    weak_reply D' (Or.inr (Or.inl (Nat.le_refl 4))) keep, fun X Y ws => ?_⟩⟩
  obtain ⟨⟨n1, n2, n3, n4⟩, n5, n6⟩ := WeakStep.bounds ws
  exact ⟨out_ku hc sd rfl (by omega) (by omega),
    Or.inl (push_ku (domS_reply D' ws) hc sd rfl (by omega) (by omega))⟩

set_option maxHeartbeats 4000000 in
/-- King three files out beside the pawn's rank, lone king two files out on the last
rank: the king steps inwards to the sixth rank. -/
theorem mv_r3 {j a b c e f u w : Nat} (D : DomS a b c 4 e f) (hc : 2 ≤ c) (sw : Sw c u w)
    (hj : 6 ≤ j) (ha : a = w) (hb : b = 4 ∨ b = 5) (he : e = u) (hf : f = 7) :
    Mv4 j a b c e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  have sw' := sw
  unfold Sw at sw'
  obtain ⟨t, o, sd⟩ : ∃ t o, Sd c t o u := by
    rcases sw' with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact ⟨c + 1, c - 1, Or.inl ⟨rfl, by omega, h1⟩⟩
    · exact ⟨c - 1, c + 1, Or.inr ⟨by omega, rfl, h1⟩⟩
  have sd' := sd
  unfold Sd at sd'
  have st : KingStep a b c 4 e f u 5 := by
    unfold KingStep Near Apart
    omega
  have D' := dom_step4 D st
  have keep : ¬ Capture u 5 c 4 e f := by
    unfold Capture Near
    omega
  refine Or.inr ⟨j - 1, by omega, u, 5, st, w4win_mono (i := 5) (by omega) ⟨keep,
    weak_reply D' (Or.inr (Or.inl (Nat.le_refl 4))) keep, fun X Y ws => ?_⟩⟩
  obtain ⟨⟨n1, n2, n3, n4⟩, n5, n6⟩ := WeakStep.bounds ws
  have k7 := ws.k7
  have k5 := ws.k5
  by_cases g : X = t
  · have hY : Y = 7 := by omega
    subst g hY
    have kt : KeyT c X 5 := ⟨by omega, Or.inl rfl⟩
    have won : Won u 5 c X 7 X 5 1 := by
      refine ⟨⟨by unfold Ch; omega, Or.inl (by unfold Thru; omega)⟩, ?_⟩
      unfold WR Ch
      omega
    refine ⟨won_out hc u3 kt won ?_ ?_,
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨X, 5, 1, kt, Nat.le_refl 1, by omega, won⟩))))⟩
    · intro pr
      have tch := pr.1
      unfold Near at tch
      omega
    · intro rr
      unfold Rr4 at rr
      omega
  · exact ⟨out_ku hc sd rfl (by omega) (by omega),
      Or.inl (push_ku (domS_reply D' ws) hc sd rfl (by omega) (by omega))⟩

set_option maxHeartbeats 4000000 in
/-- King three files out on the sixth rank, lone king two files out on the last rank:
outside the guard. -/
theorem out_w5_u7 {c : Nat} (hc : 2 ≤ c) : ¬ S4 (c + 3) 5 c (c + 2) 7 := by
  rintro ⟨-, -, ⟨bes, -, -⟩ | ⟨-, op | m4 | pr | rr⟩⟩
  · unfold B4 at bes
    omega
  · unfold Op4 at op
    omega
  · rcases m4.2.1 with q | q
    · omega
    · have h := q 1 (Or.inl (by unfold Ch; omega))
      unfold Ch at h
      omega
  · have tch := pr.1
    unfold Near at tch
    omega
  · unfold Rr4 at rr
    omega

set_option maxHeartbeats 4000000 in
/-- King four files out beside the pawn's rank, lone king three files out on the last
rank: the king steps inwards to the sixth rank. -/
theorem mv_r4 {j a b c e f : Nat} (D : DomS a b c 4 e f) (hc : 2 ≤ c) (hj : 7 ≤ j)
    (ha : a = c + 4) (hb : b = 4 ∨ b = 5) (he : e = c + 3) (hf : f = 7) : Mv4 j a b c e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  have sw : Sw c (c + 2) (c + 3) := Or.inl ⟨rfl, rfl⟩
  have st : KingStep a b c 4 e f (c + 3) 5 := by
    unfold KingStep Near Apart
    omega
  have D' := dom_step4 D st
  have keep : ¬ Capture (c + 3) 5 c 4 e f := by
    unfold Capture Near
    omega
  refine Or.inr ⟨j - 1, by omega, c + 3, 5, st, w4win_mono (i := 6) (by omega) ⟨keep,
    weak_reply D' (Or.inr (Or.inl (Nat.le_refl 4))) keep, fun X Y ws => ?_⟩⟩
  obtain ⟨⟨n1, n2, n3, n4⟩, n5, n6⟩ := WeakStep.bounds ws
  have k7 := ws.k7
  have k5 := ws.k5
  by_cases g : X = c + 2
  · have hY : Y = 7 := by omega
    subst g hY
    exact ⟨out_w5_u7 hc, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨c + 2, c + 3, sw, Or.inr (Or.inr (Or.inl ⟨by omega, rfl, Or.inr rfl, rfl, rfl⟩))⟩))))⟩
  · have sqx : ¬ Sq4 c X Y := by
      unfold Sq4
      omega
    exact ⟨fun h => sqx h.2.1, Or.inl (push_out (domS_reply D' ws) hc (by omega) sqx)⟩

/-- The king steps of the positions with no race won. -/
theorem mv_rest {j a b c e f : Nat} (D : DomS a b c 4 e f) (hc : 2 ≤ c)
    (h : RestM j a b c e f) : Mv4 j a b c e f := by
  obtain ⟨u, w, sw, h⟩ := h
  rcases h with ⟨hj, ha, hb, he, hf⟩ | ⟨hj, ha, hb, he, hf⟩ | ⟨hj, ha, hb, he, hf⟩ |
    ⟨hj, hu, ha, hb, he, hf⟩
  · exact mv_r1 D hc sw hj ha hb he hf
  · exact mv_r2 D hc sw hj ha hb he hf
  · exact mv_r3 D hc sw hj ha hb he hf
  · unfold Sw at sw
    exact mv_r4 D hc hj (by omega) hb (by omega) hf

end EndgameChess.Rules.KPK.Coord
