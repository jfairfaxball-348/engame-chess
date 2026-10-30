import EndgameChess.Rules.KPK.Coord.Promo

/-! Forced wins from any hand-written strategy `Plan` on the coordinate game: a
pawn-height/phase rank decreases on every ply, each pawn move resets the clock,
and repetition is excluded because equal keys have equal ranks. -/
namespace EndgameChess.Rules.KPK.Coord
open EndgameChess.KK

/-- A push that keeps a winning plan going, or a promotion that wins. -/
def StrongPush (W : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Prop) (a b c d e f : Nat) : Prop :=
  (Free a b e f c (d + 1) ∧ d + 1 ≤ 6 ∧ ∃ l, l ≤ 40 ∧ W l a b c (d + 1) e f) ∨
  (d = 1 ∧ Free a b e f c (d + 1) ∧ Free a b e f c 3 ∧ ∃ l, l ≤ 40 ∧ W l a b c 3 e f) ∨
  (d = 6 ∧ Free a b e f c 7 ∧ QueenGood a b c e f) ∨
  (d = 6 ∧ Free a b e f c 7 ∧ RookGood a b c e f)

/-- A strategy: a phase `j ≤ 40` for each coordinate position in its region. With the
strong side to move the phase is spent on a king step or ended by a pawn move; a weak
reply never raises it, cannot capture the pawn and exists. -/
structure Plan where
  S : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Prop
  W : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Prop
  S_le : ∀ {j a b c d e f}, S j a b c d e f → j ≤ 40
  W_le : ∀ {j a b c d e f}, W j a b c d e f → j ≤ 40
  strong : ∀ {j a b c d e f}, DomS a b c d e f → S j a b c d e f →
    StrongPush W a b c d e f ∨
      ∃ i, j = i + 1 ∧ ∃ x y, KingStep a b c d e f x y ∧ W i x y c d e f
  weak : ∀ {j a b c d e f}, Dom a b c d e f → W j a b c d e f →
    ¬ Capture a b c d e f ∧ (∃ x y, WeakStep a b c d e f x y) ∧
      ∀ x y, WeakStep a b c d e f x y → ∃ i, i ≤ j ∧ S i a b c d x y

abbrev SAt (P : Plan) (j : Nat) (σ : Colour) (sk ps wk : Square) : Prop :=
  P.S j (mx ps sk) (height σ sk) (mx ps ps) (height σ ps) (mx ps wk) (height σ wk)

abbrev WAt (P : Plan) (j : Nat) (σ : Colour) (sk ps wk : Square) : Prop :=
  P.W j (mx ps sk) (height σ sk) (mx ps ps) (height σ ps) (mx ps wk) (height σ wk)

/-- Height part of the rank: pawn moves dominate every king manoeuvre. -/
def U (h : Nat) : Nat := 84 * (6 - h)

variable {P : Plan}

/-- `n` is a certified rank of the board. -/
def Cert (P : Plan) (σ : Colour) (q : Position) (n : Nat) : Prop :=
  ∃ sk ps wk, Cfg q σ sk ps wk ∧
    ((q.turn = σ ∧ ¬ PawnSees σ ps wk ∧ ∃ j, SAt P j σ sk ps wk ∧ n = U (height σ ps) + (2 * j + 1)) ∨
     (q.turn = σ.opp ∧ ∃ j, WAt P j σ sk ps wk ∧ n = U (height σ ps) + (2 * j + 2)))

theorem cert_pos {σ : Colour} {q : Position} {n : Nat} (c : Cert P σ q n) : 1 ≤ n := by
  obtain ⟨_, _, _, _, ⟨_, _, j, _, rfl⟩ | ⟨_, j, _, rfl⟩⟩ := c <;> omega

/-- The certified rank determines the pawn height band. -/
theorem cert_range {σ : Colour} {q : Position} {n : Nat} {a p b : Square} (c : Cert P σ q n)
    (other : IsKPK q σ a p b) : U (height σ p) + 1 ≤ n ∧ n ≤ U (height σ p) + 82 := by
  obtain ⟨sk, ps, wk, cfg, ⟨_, _, j, sat, rfl⟩ | ⟨_, j, sat, rfl⟩⟩ := c
  · have same := pawn_square_unique cfg.material other
    have := P.S_le sat
    subst same; omega
  · have same := pawn_square_unique cfg.material other
    have := P.W_le sat
    subst same; omega

theorem cfg_congr {q r : Position} {σ : Colour} {sk ps wk : Square} (board : q.board = r.board)
    (rights : q.castling = r.castling) (c : Cfg q σ sk ps wk) : Cfg r σ sk ps wk :=
  ⟨⟨c.material.1, c.material.2.1, c.material.2.2.1, board ▸ c.material.2.2.2⟩,
    c.far, c.low, c.high, rights ▸ c.rights⟩

theorem cert_congr {σ : Colour} {q r : Position} {n : Nat} (board : q.board = r.board)
    (turn : q.turn = r.turn) (rights : q.castling = r.castling) (c : Cert P σ q n) : Cert P σ r n := by
  obtain ⟨sk, ps, wk, cfg, side⟩ := c
  refine ⟨sk, ps, wk, cfg_congr board rights cfg, ?_⟩
  rw [← turn]; exact side

theorem exists_least {P : Nat → Prop} (h : ∃ n, P n) : ∃ n, P n ∧ ∀ m, P m → n ≤ m := by
  obtain ⟨n, hn⟩ := h
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases smaller : ∃ k, k < n ∧ P k
    · obtain ⟨k, lt, hk⟩ := smaller
      exact ih k lt hk
    · refine ⟨n, hn, fun m hm => ?_⟩
      apply Classical.byContradiction
      intro no
      exact smaller ⟨m, by omega, hm⟩

open Classical in
/-- The least element of a nonempty set of naturals. -/
noncomputable def leastOf (P : Nat → Prop) : Nat :=
  if h : ∃ n, P n then Classical.choose (exists_least h) else 0

/-- The least certified rank; a function of the repetition key. -/
noncomputable def rnk (P : Plan) (σ : Colour) (q : Position) : Nat := leastOf (Cert P σ q)

theorem rnk_spec {σ : Colour} {q : Position} (h : ∃ n, Cert P σ q n) : Cert P σ q (rnk P σ q) := by
  classical
  simp only [rnk, leastOf, dite_eq_left h]
  exact (Classical.choose_spec (exists_least h)).1

theorem rnk_le {σ : Colour} {q : Position} {n : Nat} (c : Cert P σ q n) : rnk P σ q ≤ n := by
  classical
  have h : ∃ n, Cert P σ q n := ⟨n, c⟩
  simp only [rnk, leastOf, dite_eq_left h]
  exact (Classical.choose_spec (exists_least h)).2 n c

theorem rnk_key {σ : Colour} {q r : Position}
    (same : RawRepetition.key q = RawRepetition.key r) : rnk P σ q = rnk P σ r := by
  have board : q.board = r.board := by
    simpa only [RawRepetition.key, RawRepetition.normalizeEP] using congrArg Position.board same
  have turn : q.turn = r.turn := by
    simpa only [RawRepetition.key, RawRepetition.normalizeEP] using congrArg Position.turn same
  have rights : q.castling = r.castling := by
    simpa only [RawRepetition.key, RawRepetition.normalizeEP] using congrArg Position.castling same
  have equal : Cert P σ q = Cert P σ r := by
    funext n
    exact propext ⟨cert_congr board turn rights, cert_congr board.symm turn.symm rights.symm⟩
  simp only [rnk, equal]

theorem weak_cfg {q r : Position} {σ : Colour} {sk ps wk t : Square}
    (h : Cfg q σ sk ps wk) (legal : Legal q r) (material : IsKPK r σ sk ps t) : Cfg r σ sk ps t :=
  ⟨material, LoneKing.kings_apart_after (by decide) material legal, h.low, h.high,
    noRights_after_legal h.rights legal⟩

theorem safe_of_no_capture {σ : Colour} {sk ps wk : Square}
    (h : ¬ Capture (mx ps sk) (height σ sk) (mx ps ps) (height σ ps) (mx ps wk) (height σ wk))
    (distinct : ps ≠ wk) : LoneKing.Safe sk ps wk := by
  by_cases adjacent : dInf ps wk = 1
  · right
    apply Classical.byContradiction
    intro notNear
    apply h
    refine ⟨?_, fun near => notNear ((near_iff σ ps sk ps).mpr near)⟩
    rw [dInf_comm] at adjacent
    exact (near_iff σ ps wk ps).mp adjacent
  · left
    have zero : dInf ps wk ≠ 0 := fun e => distinct (dInf_eq_zero_iff.mp e)
    omega

/-- Every weak reply stays certified with a smaller rank and the same pawn. -/
theorem weak_progress {σ : Colour} {q : Position} {n : Nat} (c : Cert P σ q n) (turn : q.turn = σ.opp) :
    (∃ r, Legal q r) ∧ ∀ r, Legal q r → ∃ n', n' < n ∧ Cert P σ r n' ∧
      ∃ a p b a' b', IsKPK q σ a p b ∧ IsKPK r σ a' p b' := by
  obtain ⟨sk, ps, wk, cfg, ⟨wrong, _⟩ | ⟨_, j, sat, rfl⟩⟩ := c
  · exact False.elim (opp_ne σ (wrong.symm.trans turn))
  obtain ⟨noCapture, ⟨x, y, step⟩, all⟩ := P.weak (dom_of_cfg cfg) sat
  constructor
  · obtain ⟨r, _, legal, _⟩ := legal_of_weak_step cfg turn step
    exact ⟨r, legal⟩
  · intro r legal
    obtain ⟨t, material, nextTurn, dist⟩ := LoneKing.safe_reply cfg.material turn
      (safe_of_no_capture noCapture cfg.material.2.2.1) legal
    have st := weak_step_of_legal cfg turn legal material dist
    obtain ⟨i, hi, sati⟩ := all _ _ st
    have nc := weak_cfg cfg legal material
    refine ⟨U (height σ ps) + (2 * i + 1), by omega, ⟨sk, ps, t, nc, Or.inl ⟨nextTurn, ?_, i, sati, rfl⟩⟩,
      sk, ps, wk, sk, t, cfg.material, material⟩
    exact fun sees => st.2.2.2.2.2 ((att_iff σ ps t).mp sees)

theorem push_layer (P : Plan) {j : Nat} {σ : Colour} {sk ps wk t : Square} {y : Nat}
    (file : t.1 = ps.1) (rank : height σ t = y)
    (h : P.W j (mx ps sk) (height σ sk) (mx ps ps) y (mx ps wk) (height σ wk)) :
    WAt P j σ sk t wk := by
  have e (z : Square) : mx t z = mx ps z := mx_congr file z
  have self : mx ps t = mx ps ps := by simp only [mx, file]
  simp only [WAt, e, self, rank]
  exact h

theorem pawn_cert {σ : Colour} {q : Position} {sk ps wk t : Square} {j : Nat} {m : Move}
    (h : Cfg q σ sk ps wk) (turn : q.turn = σ) (legal : isLegal q m = true)
    (material : IsKPK (play q m) σ sk t wk) (high : height σ t ≤ 6) (up : height σ ps < height σ t)
    (sat : WAt P j σ sk t wk) :
    Cert P σ (play q m) (U (height σ t) + (2 * j + 2)) :=
  ⟨sk, t, wk, ⟨material, h.far, by have := h.low; omega, high,
    noRights_after_legal h.rights ⟨m, legal, rfl⟩⟩, Or.inr ⟨by rw [play_turn, turn], j, sat, rfl⟩⟩

/-- Outcome of the planned strong move. -/
def Planned (P : Plan) (σ : Colour) (q : Position) (n : Nat) (m : Move) : Prop :=
  (∃ n', n' < n ∧ Cert P σ (play q m) n' ∧
    ∃ a p b a' b', IsKPK q σ a p b ∧ IsKPK (play q m) σ a' p b') ∨
  (∃ n', n' < n ∧ Cert P σ (play q m) n' ∧ ∃ a p b, IsKPK q σ a p b ∧ m.src = p) ∨
  (∃ sk ps wk t k, IsKPK q σ sk ps wk ∧ 2 ≤ dInf sk wk ∧ Push q σ ps t ∧
    t.2.val = lastRank σ ∧ m = promote ps t k ∧ (k = .queen ∨ k = .rook) ∧
    ForceMate σ (play q m))

theorem strong_progress {σ : Colour} {q : Position} {n : Nat} (c : Cert P σ q n) (turn : q.turn = σ) :
    ∃ m, isLegal q m = true ∧ Planned P σ q n m := by
  obtain ⟨sk, ps, wk, cfg, ⟨_, safe, j, sat, rfl⟩ | ⟨wrong, _⟩⟩ := c
  rotate_left
  · exact False.elim (opp_ne σ (turn.symm.trans wrong))
  have Dm : DomS (mx ps sk) (height σ sk) (mx ps ps) (height σ ps) (mx ps wk) (height σ wk) :=
    ⟨dom_of_cfg cfg, fun attack => safe ((att_iff σ ps wk).mpr attack)⟩
  have low := cfg.low
  have high := cfg.high
  have hj := P.S_le sat
  have hm := cfg.material
  have far := cfg.far
  rcases P.strong Dm sat with pushes | ⟨l, rfl, x, y, step, wl⟩
  · rcases pushes with ⟨fr, lim, l, hl, wl⟩ | ⟨one, fr1, fr2, l, hl, wl⟩ |
        ⟨six, fr, sf, good⟩ | ⟨six, fr, sf, good⟩
    · obtain ⟨t, file, rank, push⟩ := push_of_free cfg (y := height σ ps + 1) (by omega) rfl fr
      let m : Move := ⟨ps, t, none⟩
      have legal : isLegal q m = true := (pawn_legal_iff hm turn rfl far).mpr
        ⟨push, (promo_none_iff σ ps t).mpr (by omega)⟩
      have material : IsKPK (play q m) σ sk t wk := pawn_play_material hm turn (m := m) rfl push
      have bound := P.W_le wl
      refine ⟨m, legal, Or.inr (Or.inl ⟨_, ?_, pawn_cert cfg turn legal material (by omega) (by omega)
        (push_layer P file rank wl), sk, ps, wk, hm, rfl⟩)⟩
      simp only [U, rank]; omega
    · have one' := one
      obtain ⟨t, file, rank, push⟩ := double_of_free cfg one fr1 fr2
      let m : Move := ⟨ps, t, none⟩
      have legal : isLegal q m = true := (pawn_legal_iff hm turn rfl far).mpr
        ⟨push, (promo_none_iff σ ps t).mpr (by omega)⟩
      have material : IsKPK (play q m) σ sk t wk := pawn_play_material hm turn (m := m) rfl push
      have bound := P.W_le wl
      refine ⟨m, legal, Or.inr (Or.inl ⟨_, ?_, pawn_cert cfg turn legal material (by omega) (by omega)
        (push_layer P file rank wl), sk, ps, wk, hm, rfl⟩)⟩
      simp only [U, rank, one]; omega
    · obtain ⟨t, file, rank, push⟩ := push_of_free cfg (y := 7) (by omega) (by omega) fr
      have top : TopSquare σ ps t := ⟨file, rank⟩
      have last : t.2.val = lastRank σ := (promotion_rank σ t).mpr rank
      have win := (queen_successor_iff hm turn push).mpr
        (promoted_good .queen (Or.inl rfl) cfg turn push top sf good)
      exact ⟨promote ps t .queen, promotion_legal hm turn far push last .queen,
        Or.inr (Or.inr ⟨sk, ps, wk, t, .queen, hm, far, push, last, rfl, Or.inl rfl, win⟩)⟩
    · obtain ⟨t, file, rank, push⟩ := push_of_free cfg (y := 7) (by omega) (by omega) fr
      have top : TopSquare σ ps t := ⟨file, rank⟩
      have last : t.2.val = lastRank σ := (promotion_rank σ t).mpr rank
      have win := (rook_successor_iff hm turn push).mpr
        (promoted_good .rook (Or.inr rfl) cfg turn push top sf good)
      exact ⟨promote ps t .rook, promotion_legal hm turn far push last .rook,
        Or.inr (Or.inr ⟨sk, ps, wk, t, .rook, hm, far, push, last, rfl, Or.inr rfl, win⟩)⟩
  · obtain ⟨m, t, legal, _, material, nextTurn, rfl, rfl⟩ := legal_of_king_step cfg turn step
    have nextFar := (apart_iff σ ps t wk).mpr step.2.2.2.2
    have nc : Cfg (play q m) σ t ps wk :=
      ⟨material, nextFar, low, high, noRights_after_legal cfg.rights ⟨m, legal, rfl⟩⟩
    refine ⟨m, legal, Or.inl ⟨U (height σ ps) + (2 * l + 2), by omega,
      ⟨t, ps, wk, nc, Or.inr ⟨nextTurn, l, wl, rfl⟩⟩, sk, ps, wk, t, wk, hm, material⟩⟩

theorem promoted_bound {σ : Colour} {q : Position} {sk ps wk t : Square} {k : PromoPiece}
    (h : IsKPK q σ sk ps wk) (turn : q.turn = σ) (push : Push q σ ps t)
    (hk : k = .queen ∨ k = .rook) (win : ForceMate σ (play q (promote ps t k))) :
    MateWithin σ 98 (play q (promote ps t k)) := by
  have nextTurn : (play q (promote ps t k)).turn = σ.opp := by rw [play_turn, turn]
  rcases hk with rfl | rfl
  · have material := promotion_material h turn push .queen
    rcases (KQK.weak_force_safe_iff material nextTurn).mp win with mate | ⟨safe, moves⟩
    · exact mateWithin_mono (show MateWithin σ 0 _ from ⟨nextTurn, mate⟩) (by decide)
    · exact KQK.safe_weak_entry_bound material nextTurn safe moves
  · exact KRKCentral.weak98 (promotion_material h turn push .rook) nextTurn win

/-- Board-level forced mate with an explicit sufficient ply bound. -/
theorem cert_bound (N : Nat) : ∀ {σ : Colour} {q : Position} {n : Nat}, n ≤ N → Cert P σ q n →
    MateWithin σ (100 + N) q := by
  induction N with
  | zero =>
    intro σ q n le c
    have := cert_pos c
    omega
  | succ N ih =>
    intro σ q n le c
    rcases colour_cases σ q.turn with turn | turn
    · obtain ⟨m, legal, plan⟩ := strong_progress c turn
      have step : Legal q (play q m) := ⟨m, legal, rfl⟩
      rcases plan with ⟨n', lt, next, _⟩ | ⟨n', lt, next, _⟩ |
          ⟨sk, ps, wk, t, k, hm, _, push, _, rfl, hk, win⟩
      · exact choose_bound turn step (ih (by omega) next)
      · exact choose_bound turn step (ih (by omega) next)
      · exact choose_bound turn step
          (mateWithin_mono (promoted_bound hm turn push hk win) (Nat.le_trans (by decide : 98 ≤ 100) (Nat.le_add_right 100 N)))
    · obtain ⟨moves, all⟩ := weak_progress c turn
      have every : ∀ r, Legal q r → MateWithin σ (100 + N) r := by
        intro r legal
        obtain ⟨n', lt, next, _⟩ := all r legal
        exact ih (by omega) next
      have live : ¬ DeadK q := by
        obtain ⟨r, legal⟩ := moves
        obtain ⟨t, reach, goal⟩ := mateWithin_sound (every r legal)
        exact fun dead => dead ⟨t, reachK_cons legal reach, goal.2⟩
      exact Or.inr ⟨live, Or.inr ⟨turn, moves, every⟩⟩

theorem within_mono {σ : Colour} {s : FreshGame.State} {n m : Nat}
    (h : FreshGame.Within σ n s) (hle : n ≤ m) : FreshGame.Within σ m s := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  clear hle
  induction k generalizing n s with
  | zero => exact h
  | succ k ih =>
    have step : ∀ {n : Nat} {s : FreshGame.State}, FreshGame.Within σ n s →
        FreshGame.Within σ (n + 1) s := by
      intro n
      induction n with
      | zero => intro s w; exact Or.inl w
      | succ n ih2 =>
        intro s w
        rcases w with goal | ⟨ongoing, strong | weak⟩
        · exact Or.inl goal
        · obtain ⟨turn, t, st, rest⟩ := strong
          exact Or.inr ⟨ongoing, Or.inl ⟨turn, t, st, ih2 rest⟩⟩
        · obtain ⟨turn, claim, moves, all⟩ := weak
          exact Or.inr ⟨ongoing, Or.inr ⟨turn, claim, moves, fun t st => ih2 (all t st)⟩⟩
    exact step (ih h)

/-- Every earlier board has a larger rank, hence a different key. -/
def Sep (P : Plan) (σ : Colour) (s : FreshGame.State) : Prop :=
  ∀ r ∈ s.past, (∃ a p b, IsKPK r σ a p b) ∧ rnk P σ s.board < rnk P σ r

/-- Quiet plies consume rank inside one pawn-height band. -/
def ClockOK (P : Plan) (σ : Colour) (s : FreshGame.State) : Prop :=
  ∀ a p b, IsKPK s.board σ a p b → s.clock + rnk P σ s.board ≤ U (height σ p) + 82

theorem sep_count {σ : Colour} {s : FreshGame.State} (sep : Sep P σ s) :
    FreshGame.occurrences s = 1 := by
  apply FreshGame.occurrences_one_of_key_ne
  intro r member same
  have lt := (sep r member).2
  have eq := rnk_key (P := P) (σ := σ) same
  omega

theorem sep_after {σ : Colour} {s : FreshGame.State} {m : Move} (sep : Sep P σ s)
    (material : ∃ a p b, IsKPK s.board σ a p b)
    (lower : rnk P σ (play s.board m) < rnk P σ s.board) : Sep P σ (FreshGame.afterMove s m) := by
  intro r member
  change r ∈ s.board :: s.past at member
  rcases List.mem_cons.mp member with rfl | old
  · exact ⟨material, lower⟩
  · exact ⟨(sep r old).1, Nat.lt_trans lower (sep r old).2⟩

theorem clock_small {σ : Colour} {s : FreshGame.State} {n : Nat} (c : Cert P σ s.board n)
    (clock : ClockOK P σ s) : s.clock ≤ 82 := by
  have spec := rnk_spec (⟨n, c⟩ : ∃ n, Cert P σ s.board n)
  obtain ⟨a, p, b, cfg, _⟩ := c
  have range := cert_range spec cfg.material
  have bound := clock a p b cfg.material
  omega

theorem lift (N : Nat) : ∀ {σ : Colour} {s : FreshGame.State}, (∃ n, Cert P σ s.board n) →
    rnk P σ s.board ≤ N → Sep P σ s → ClockOK P σ s → FreshGame.Within σ (100 + N) s := by
  induction N with
  | zero =>
    intro σ s cert le _ _
    have := cert_pos (rnk_spec cert)
    omega
  | succ N ih =>
    intro σ s cert le sep clock
    have c := rnk_spec cert
    have small := clock_small c clock
    have force := cert_bound _ (Nat.le_refl _) c
    have count := sep_count sep
    have material : ∃ a p b, IsKPK s.board σ a p b := by
      obtain ⟨a, p, b, cfg, _⟩ := c
      exact ⟨a, p, b, cfg.material⟩
    have live : ¬ DeadK s.board := forceMate_not_dead ⟨_, force⟩
    have rights : s.board.castling = noRights := by
      obtain ⟨a, p, b, cfg, _⟩ := c
      exact cfg.rights
    have quiet : ∀ m a p b a' b', isLegal s.board m = true → IsKPK s.board σ a p b →
        IsKPK (play s.board m) σ a' p b' → ∀ n', n' < rnk P σ s.board → Cert P σ (play s.board m) n' →
        FreshGame.Within σ (100 + N) (FreshGame.afterMove s m) := by
      intro m a p b a' b' legal hm hn n' lt next
      have lower : rnk P σ (FreshGame.afterMove s m).board ≤ n' := rnk_le next
      have lower' : rnk P σ (play s.board m) ≤ n' := rnk_le next
      apply ih ⟨n', next⟩ (by omega) (sep_after sep material (by omega))
      intro a2 p2 b2 hm2
      have samePawn := pawn_square_unique hn hm2
      subst samePawn
      have clk := FreshGame.afterMove_clock_le s m
      have base := clock a p b hm
      change (FreshGame.afterMove s m).clock + rnk P σ (play s.board m) ≤ _
      omega
    have pawnMove : ∀ m a p b, isLegal s.board m = true → s.board.turn = σ →
        IsKPK s.board σ a p b → m.src = p → ∀ n', n' < rnk P σ s.board →
        Cert P σ (play s.board m) n' →
        FreshGame.Within σ (100 + N) (FreshGame.afterMove s m) := by
      intro m a p b legal turn hm src n' lt next
      have lower : rnk P σ (FreshGame.afterMove s m).board ≤ n' := rnk_le next
      have lower' : rnk P σ (play s.board m) ≤ n' := rnk_le next
      apply ih ⟨n', next⟩ (by omega) (sep_after sep material (by omega))
      intro a2 p2 b2 hm2
      change (FreshGame.afterMove s m).clock + rnk P σ (play s.board m) ≤ _
      rw [pawn_resets_clock hm turn src]
      have spec := rnk_spec (⟨n', next⟩ : ∃ n, Cert P σ (play s.board m) n)
      have range := cert_range spec hm2
      omega
    rcases colour_cases σ s.board.turn with turn | turn
    · obtain ⟨m, legal, plan⟩ := strong_progress c turn
      have ongoing : FreshGame.Ongoing s :=
        ⟨live, ⟨_, m, legal, rfl⟩, by omega, by omega⟩
      have step : FreshGame.BoardStep s (FreshGame.afterMove s m) := ⟨ongoing, m, legal, rfl⟩
      refine Or.inr ⟨ongoing, Or.inl ⟨turn, _, step, ?_⟩⟩
      rcases plan with ⟨n', lt, next, a, p, b, a', b', hm, hn⟩ | ⟨n', lt, next, a, p, b, hm, src⟩ |
          ⟨sk, ps, wk, t, k, hm, far, push, last, rfl, hk, win⟩
      · exact quiet m a p b a' b' legal hm hn n' lt next
      · exact pawnMove m a p b legal turn hm src n' lt next
      · have past : ∀ q ∈ s.past, ∃ a p b, IsKPK q σ a p b := fun q member => (sep q member).1
        have rest : FreshGame.Within σ 98 (FreshGame.afterMove s (promote ps t k)) := by
          rcases hk with rfl | rfl
          · exact queen_prefix_continuation hm turn far rights past push last win
          · exact rook_prefix_continuation hm turn far rights past push last win
        exact within_mono rest (Nat.le_trans (by decide : 98 ≤ 100) (Nat.le_add_right 100 N))
    · obtain ⟨moves, all⟩ := weak_progress c turn
      have ongoing : FreshGame.Ongoing s := ⟨live, moves, by omega, by omega⟩
      have child : ∀ m, isLegal s.board m = true →
          FreshGame.Within σ (100 + N) (FreshGame.afterMove s m) ∧
            rnk P σ (play s.board m) < rnk P σ s.board ∧ (∃ n, Cert P σ (play s.board m) n) := by
        intro m legal
        obtain ⟨n', lt, next, a, p, b, a', b', hm, hn⟩ := all _ ⟨m, legal, rfl⟩
        exact ⟨quiet m a p b a' b' legal hm hn n' lt next, by have := rnk_le next; omega, n', next⟩
      have noClaim : ¬ FreshGame.CanClaim s := by
        rintro (current | ⟨m, legal, intended⟩)
        · rcases current with over | repetition <;> omega
        · have nextSep := sep_after (m := m) sep material (child m legal).2.1
          have nextCount := sep_count nextSep
          have nextClock := FreshGame.afterMove_clock_le s m
          rcases intended with over | repetition <;> omega
      obtain ⟨r, m, legal, rfl⟩ := moves
      refine Or.inr ⟨ongoing, Or.inr ⟨turn, noClaim, ⟨_, ongoing, m, legal, rfl⟩, ?_⟩⟩
      rintro t ⟨_, m', legal', rfl⟩
      exact (child m' legal').1

/-- A certified fresh root is an actual win with a sufficient explicit ply bound. -/
theorem fresh_cert_win {σ : Colour} {q : Position} {n : Nat} (c : Cert P σ q n) :
    FreshGame.Within σ 604 (FreshGame.fresh q) := by
  have cert : ∃ n, Cert P σ q n := ⟨n, c⟩
  have spec := rnk_spec cert
  have bound : rnk P σ q ≤ 504 := by
    obtain ⟨a, p, b, cfg, side⟩ := id spec
    have range := cert_range spec cfg.material
    have low := cfg.low
    simp only [U] at range
    omega
  have clock : ClockOK P σ (FreshGame.fresh q) := by
    intro a p b hm
    change 0 + rnk P σ q ≤ _
    have range := cert_range spec hm
    omega
  exact lift 504 (s := FreshGame.fresh q) cert bound
    (fun r member => False.elim (List.not_mem_nil member)) clock

/-- A fresh root inside a plan, strong side to move, is an actual win. -/
theorem fresh_plan_strong {σ : Colour} {q : Position} {sk ps wk : Square} {j : Nat}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk) (turn : q.turn = σ)
    (safe : ¬ PawnSees σ ps wk) (sat : SAt P j σ sk ps wk) :
    FreshGame.Within σ 604 (FreshGame.fresh q) :=
  fresh_cert_win (P := P) ⟨sk, ps, wk, fresh_cfg h fresh, Or.inl ⟨turn, safe, j, sat, rfl⟩⟩

/-- A fresh root inside a plan, weak side to move, is an actual win. -/
theorem fresh_plan_weak {σ : Colour} {q : Position} {sk ps wk : Square} {j : Nat}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk) (turn : q.turn = σ.opp)
    (sat : WAt P j σ sk ps wk) : FreshGame.Within σ 604 (FreshGame.fresh q) :=
  fresh_cert_win (P := P) ⟨sk, ps, wk, fresh_cfg h fresh, Or.inr ⟨turn, j, sat, rfl⟩⟩

end EndgameChess.Rules.KPK.Coord
