import EndgameChess.Rules.KPK.Coord.Forced

/-! Holding from any hand-written `Guard` on the coordinate game: the lone king answers
every strong move inside the region, capturing the pawn or being stalemated at its
exits. This gives an actual hold, and excludes forced mate with no move limit. -/
namespace EndgameChess.Rules.KPK.Coord
open EndgameChess.KK

/-- A drawing strategy: each strong move leads to a position the lone king answers. A
promotion inside the region can always be captured at once. -/
structure Guard where
  S : Nat → Nat → Nat → Nat → Nat → Nat → Prop
  W : Nat → Nat → Nat → Nat → Nat → Nat → Prop
  strong : ∀ {a b c d e f}, DomS a b c d e f → S a b c d e f →
    (∀ x y, KingStep a b c d e f x y → W x y c d e f) ∧
    (Free a b e f c (d + 1) → d + 1 ≤ 6 → W a b c (d + 1) e f) ∧
    (d = 1 → Free a b e f c (d + 1) → Free a b e f c 3 → W a b c 3 e f) ∧
    (d = 6 → Free a b e f c 7 → Near e f c 7 ∧ ¬ Near a b c 7)
  weak : ∀ {a b c d e f}, Dom a b c d e f → W a b c d e f →
    Capture a b c d e f ∨ (∀ x y, ¬ WeakStep a b c d e f x y) ∨
      ∃ x y, WeakStep a b c d e f x y ∧ S a b c d x y

variable (G : Guard)

abbrev SD (σ : Colour) (sk ps wk : Square) : Prop :=
  G.S (mx ps sk) (height σ sk) (mx ps ps) (height σ ps) (mx ps wk) (height σ wk)

abbrev WD (σ : Colour) (sk ps wk : Square) : Prop :=
  G.W (mx ps sk) (height σ sk) (mx ps ps) (height σ ps) (mx ps wk) (height σ wk)

/-- Exact KPK board in the guarded region. -/
def DrawBoard (σ : Colour) (q : Position) : Prop :=
  ∃ sk ps wk, Cfg q σ sk ps wk ∧
    ((q.turn = σ ∧ ¬ PawnSees σ ps wk ∧ SD G σ sk ps wk) ∨ (q.turn = σ.opp ∧ WD G σ sk ps wk))

/-- The guarded region, its dead exits, and pending captures into a dead board. -/
def DrawRegion (σ : Colour) (q : Position) : Prop :=
  DrawBoard G σ q ∨ DeadK q ∨ (q.turn = σ.opp ∧ ∃ r, Legal q r ∧ DeadK r)

variable {G}

theorem push_coords {P : Nat → Nat → Nat → Nat → Nat → Nat → Prop} {σ : Colour}
    {sk ps wk t : Square} {y : Nat} (file : t.1 = ps.1) (rank : height σ t = y)
    (h : P (mx ps sk) (height σ sk) (mx ps ps) y (mx ps wk) (height σ wk)) :
    P (mx t sk) (height σ sk) (mx t t) (height σ t) (mx t wk) (height σ wk) := by
  have e (z : Square) : mx t z = mx ps z := mx_congr file z
  have self : mx ps t = mx ps ps := by simp only [mx, file]
  simp only [e, self, rank]
  exact h

theorem free_of_board {σ : Colour} {sk ps wk t : Square} (file : t.1 = ps.1) (nsk : sk ≠ t)
    (nwk : t ≠ wk) :
    Free (mx ps sk) (height σ sk) (mx ps wk) (height σ wk) (mx ps ps) (height σ t) := by
  have self : mx ps t = mx ps ps := by simp only [mx, file]
  refine ⟨fun same => nsk ?_, fun same => nwk ?_⟩
  · exact (square_eq_coords (σ := σ) (ps := ps)).mpr ⟨by rw [self]; exact same.1, same.2⟩
  · exact ((square_eq_coords (σ := σ) (ps := ps)).mpr ⟨by rw [self]; exact same.1, same.2⟩).symm

/-- A double step has a clear intermediate square. -/
theorem double_mid_free {q : Position} {σ : Colour} {sk ps wk t : Square}
    (h : IsKPK q σ sk ps wk) (file : t.1 = ps.1) (two : height σ t = height σ ps + 2)
    (clear : pathClear q.board ps t = true) :
    Free (mx ps sk) (height σ sk) (mx ps wk) (height σ wk) (mx ps ps) (height σ ps + 1) := by
  have mid : ∀ v : Square, mx ps v = mx ps ps → height σ v = height σ ps + 1 → q.board v = none := by
    intro v mv hv
    apply pathClear_iff.mp clear
    have vf : v.1.val = ps.1.val := by simp only [mx] at mv; split at mv <;> omega
    have tf : t.1.val = ps.1.val := congrArg Fin.val file
    have v2 := v.2.isLt
    have p2 := ps.2.isLt
    have t2 := t.2.isLt
    have line : RookLine ps t := by
      refine ⟨?_, Or.inl tf.symm⟩
      cases σ <;> simp only [height] at two <;> omega
    apply (isBetween_iff_onSeg line).mpr
    refine Or.inl ⟨tf.symm, vf, ?_⟩
    cases σ <;> simp only [height] at two hv <;> omega
  refine ⟨fun same => ?_, fun same => ?_⟩
  · have e := mid sk same.1 same.2
    rw [h.2.2.2] at e
    exact (LoneKing.board_none.mp e).1 rfl
  · have e := mid wk same.1 same.2
    rw [h.2.2.2] at e
    exact (LoneKing.board_none.mp e).2.2 rfl

theorem strong_draw_step {q r : Position} {σ : Colour} (region : DrawRegion G σ q)
    (turn : q.turn = σ) (legal : Legal q r) : DrawRegion G σ r := by
  rcases region with ⟨sk, ps, wk, cfg, ⟨_, safe, sat⟩ | ⟨wrong, _⟩⟩ | dead | ⟨wrong, _⟩
  rotate_left
  · exact False.elim (opp_ne σ (turn.symm.trans wrong))
  · exact Or.inr (Or.inl (fun ⟨t, reach, mate⟩ => dead ⟨t, reachK_cons legal reach, mate⟩))
  · exact False.elim (opp_ne σ (turn.symm.trans wrong))
  have Dm : DomS (mx ps sk) (height σ sk) (mx ps ps) (height σ ps) (mx ps wk) (height σ wk) :=
    ⟨dom_of_cfg cfg, fun attack => safe ((att_iff σ ps wk).mpr attack)⟩
  obtain ⟨kingAll, single, double, promotion⟩ := G.strong Dm sat
  have hm := cfg.material
  have low := cfg.low
  have high := cfg.high
  rcases strong_cases hm turn legal with ⟨t, material, step, nextTurn⟩ |
      ⟨m, rfl, src, push, promo, material, nextTurn⟩
  · have far := LoneKing.kings_apart_after (by decide) material legal
    have st : KingStep (mx ps sk) (height σ sk) (mx ps ps) (height σ ps) (mx ps wk) (height σ wk)
        (mx ps t) (height σ t) :=
      ⟨(near_iff σ ps sk t).mp step, mx_le _ _, height_le _ _,
        fun same => material.1 ((square_eq_coords (σ := σ) (ps := ps)).mpr same),
        (apart_iff σ ps t wk).mp far⟩
    exact Or.inl ⟨t, ps, wk, ⟨material, far, low, high, noRights_after_legal cfg.rights legal⟩,
      Or.inr ⟨nextTurn, kingAll _ _ st⟩⟩
  · have file : m.dst.1 = ps.1 := (push_files push).symm
    cases pro : m.promo with
    | none =>
      simp only [pro] at material
      have notLast : height σ m.dst ≠ 7 := by
        apply (promo_none_iff σ ps m.dst).mp
        simpa only [promoOK, pro] using promo
      have top := height_le σ m.dst
      have far := LoneKing.kings_apart_after (by decide) material legal
      have free := free_of_board (σ := σ) file material.1 material.2.2.1
      rcases push_height push with one | ⟨two, start⟩
      · have fr : Free (mx ps sk) (height σ sk) (mx ps wk) (height σ wk) (mx ps ps)
            (height σ ps + 1) := by rw [← one]; exact free
        have next := single fr (by omega)
        exact Or.inl ⟨sk, m.dst, wk, ⟨material, far, by omega, by omega,
          noRights_after_legal cfg.rights legal⟩, Or.inr ⟨nextTurn, push_coords file one next⟩⟩
      · have dOne : height σ ps = 1 := by
          cases σ <;> simp only [pawnRank, height] at start ⊢ <;> omega
        have clear : pathClear q.board ps m.dst = true := by
          rcases push.2.2 with onestep | ⟨_, _, clear⟩
          · have := push_height push
            cases σ <;> simp only [height, dy, forward] at onestep two <;> omega
          · exact clear
        have fr1 := double_mid_free hm file two clear
        have d3 : height σ m.dst = 3 := by omega
        have fr2 : Free (mx ps sk) (height σ sk) (mx ps wk) (height σ wk) (mx ps ps) 3 := by
          rw [← d3]; exact free
        have next := double dOne fr1 fr2
        exact Or.inl ⟨sk, m.dst, wk, ⟨material, far, by omega, by omega,
          noRights_after_legal cfg.rights legal⟩, Or.inr ⟨nextTurn, push_coords file d3 next⟩⟩
    | some k =>
      simp only [pro] at material
      have last : height σ m.dst = 7 := by
        apply (promo_some_iff σ ps m.dst k).mp
        simpa only [promoOK, pro] using promo
      have dSix : height σ ps = 6 := by
        rcases push_height push with one | ⟨two, start⟩
        · omega
        · cases σ <;> simp only [pawnRank, height] at start two last <;> omega
      have free := free_of_board (σ := σ) file material.1 material.2.2.1
      rw [last] at free
      obtain ⟨near1, near2⟩ := promotion dSix free
      have self : mx ps m.dst = mx ps ps := by simp only [mx, file]
      have adjacent : dInf wk m.dst = 1 := by
        apply (near_iff σ ps wk m.dst).mpr
        rw [self, last]; exact near1
      have apart : 2 ≤ dInf sk m.dst := by
        have zero : dInf sk m.dst ≠ 0 := fun e => material.1 (dInf_eq_zero_iff.mp e)
        have one : dInf sk m.dst ≠ 1 := by
          intro e
          apply near2
          have := (near_iff σ ps sk m.dst).mp e
          rwa [self, last] at this
        omega
      have nk : k.toKind ≠ .king := by cases k <;> decide
      obtain ⟨u, capture, w, b, kk⟩ := LoneKing.unprotected_capture nk material nextTurn adjacent apart
      exact Or.inr (Or.inr ⟨nextTurn, u, capture, dead_of_legal_into_KK capture kk⟩)

theorem weak_draw_choice {q : Position} {σ : Colour} (region : DrawRegion G σ q)
    (turn : q.turn = σ.opp) (moves : ∃ r, Legal q r) : ∃ r, Legal q r ∧ DrawRegion G σ r := by
  rcases region with ⟨sk, ps, wk, cfg, ⟨wrong, _⟩ | ⟨_, sat⟩⟩ | dead | ⟨_, r, legal, dead⟩
  · exact False.elim (opp_ne σ (wrong.symm.trans turn))
  · have capture_exit : Capture (mx ps sk) (height σ sk) (mx ps ps) (height σ ps) (mx ps wk) (height σ wk) →
        ∃ r, Legal q r ∧ DrawRegion G σ r := by
      rintro ⟨near1, near2⟩
      have adjacent : dInf wk ps = 1 := (near_iff σ ps wk ps).mpr near1
      have apart : 2 ≤ dInf sk ps := by
        have zero : dInf sk ps ≠ 0 := fun e => cfg.material.1 (dInf_eq_zero_iff.mp e)
        have one : dInf sk ps ≠ 1 := fun e => near2 ((near_iff σ ps sk ps).mp e)
        omega
      obtain ⟨r, legal, w, b, kk⟩ := LoneKing.unprotected_capture (by decide : PieceType.pawn ≠ .king)
        cfg.material turn adjacent apart
      exact ⟨r, legal, Or.inr (Or.inl (dead_of_legal_into_KK legal kk))⟩
    rcases G.weak (dom_of_cfg cfg) sat with capture | noStep | ⟨x, y, step, next⟩
    · exact capture_exit capture
    · by_cases cap : Capture (mx ps sk) (height σ sk) (mx ps ps) (height σ ps) (mx ps wk) (height σ wk)
      · exact capture_exit cap
      · obtain ⟨r, legal⟩ := moves
        obtain ⟨t, material, _, dist⟩ := LoneKing.safe_reply cfg.material turn
          (safe_of_no_capture cap cfg.material.2.2.1) legal
        exact False.elim (noStep _ _ (weak_step_of_legal cfg turn legal material dist))
    · obtain ⟨r, t, legal, material, nextTurn, rfl, rfl, _⟩ := legal_of_weak_step cfg turn step
      refine ⟨r, legal, Or.inl ⟨sk, ps, t, weak_cfg cfg legal material, Or.inl ⟨nextTurn, ?_, next⟩⟩⟩
      exact fun sees => step.2.2.2.2.2 ((att_iff σ ps t).mp sees)
  · obtain ⟨r, legal⟩ := moves
    exact ⟨r, legal, Or.inr (Or.inl (fun ⟨t, reach, mate⟩ => dead ⟨t, reachK_cons legal reach, mate⟩))⟩
  · exact ⟨r, legal, Or.inr (Or.inl dead)⟩

theorem region_no_goal {q : Position} {σ : Colour} (region : DrawRegion G σ q) : ¬ MateGoal σ q := by
  intro goal
  rcases region with ⟨sk, ps, wk, cfg, _⟩ | dead | ⟨_, r, legal, _⟩
  · exact not_mated cfg.material cfg.far goal.2
  · exact dead ⟨q, ReachK.refl _, goal.2⟩
  · exact goal.2.2 ⟨r, legal⟩

/-- The lone king holds the closed draw region under the actual game semantics. -/
theorem draw_hold {q : Position} {σ : Colour} (region : DrawRegion G σ q) :
    FreshGame.Hold σ.opp (FreshGame.fresh q) := by
  apply FreshGame.hold_of_invariant σ.opp (fun s => DrawRegion G σ s.board)
  · intro s r goal
    rw [opp_opp] at goal
    exact region_no_goal r goal
  · intro s t r notTurn actual
    have turn : s.board.turn = σ := by
      rcases colour_cases σ s.board.turn with strong | weak
      · exact strong
      · exact False.elim (notTurn weak)
    exact strong_draw_step r turn (FreshGame.step_legal actual)
  · intro s r ongoing turn
    obtain ⟨u, legal, next⟩ := weak_draw_choice r turn ongoing.2.1
    obtain ⟨t, actual, endpoint⟩ := FreshGame.layer.reply_complete ongoing legal
    refine ⟨t, actual, ?_⟩
    change t.board = u at endpoint
    rw [endpoint]; exact next
  · exact region

/-- The closed draw region excludes forced mate even with no move limit. -/
theorem draw_no_force {σ : Colour} (n : Nat) : ∀ {q : Position}, DrawRegion G σ q → ¬ MateWithin σ n q := by
  induction n with
  | zero => exact fun region goal => region_no_goal region goal
  | succ n ih =>
    intro q region win
    rcases win with goal | ⟨_, ⟨turn, r, legal, next⟩ | ⟨turn, moves, all⟩⟩
    · exact region_no_goal region goal
    · exact ih (strong_draw_step region turn legal) next
    · obtain ⟨r, legal, nextRegion⟩ := weak_draw_choice region turn moves
      exact ih nextRegion (all r legal)

/-- A fresh root inside a guard, pawn owner to move: an actual hold for the lone king,
and no forced mate at any length. -/
theorem fresh_guard_strong {σ : Colour} {q : Position} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk) (turn : q.turn = σ)
    (safe : ¬ PawnSees σ ps wk) (sat : SD G σ sk ps wk) :
    FreshGame.Hold σ.opp (FreshGame.fresh q) ∧ ∀ n, ¬ MateWithin σ n q := by
  have region : DrawRegion G σ q :=
    Or.inl ⟨sk, ps, wk, fresh_cfg h fresh, Or.inl ⟨turn, safe, sat⟩⟩
  exact ⟨draw_hold region, fun n => draw_no_force n region⟩

/-- A fresh root inside a guard, lone king to move. -/
theorem fresh_guard_weak {σ : Colour} {q : Position} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk) (turn : q.turn = σ.opp)
    (sat : WD G σ sk ps wk) :
    FreshGame.Hold σ.opp (FreshGame.fresh q) ∧ ∀ n, ¬ MateWithin σ n q := by
  have region : DrawRegion G σ q :=
    Or.inl ⟨sk, ps, wk, fresh_cfg h fresh, Or.inr ⟨turn, sat⟩⟩
  exact ⟨draw_hold region, fun n => draw_no_force n region⟩

end EndgameChess.Rules.KPK.Coord
