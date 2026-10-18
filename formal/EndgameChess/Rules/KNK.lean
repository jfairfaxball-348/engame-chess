import EndgameChess.Rules.Outcome

/-!
# EC-C003 — King and knight versus king is a dead position, over the rules kernel

Faithful formalisation of `proofs/EC-C003_KNK.md` (S011, Gate L), stated directly over
the general FIDE 2023 rules kernel (`Rules.Legal`, `ReachK`, `MatedK`, `DeadK`). There is
no bespoke move model. The branch where the lone king captures the knight is discharged
by the frozen K vs K result `dead_of_legal_into_KK` (EC-T0003).

Lemma map (prose → Lean):
- N0: `kings_apart_of_legal`, `strong_not_inCheck`;
- N1: `knightGeom_iff`, `knight_not_orth` (a checking knight attacks no orthogonal
  neighbour of the king), `ne_of_knight_adj`;
- N2: `escape_square`, `weak_has_move` (by the `h`/`v` construction, not enumeration);
- N3: `step_closed`;
- N4: `reach_cases`, `not_mated_of_reach`;
- main: `dead_of_legal_into_KNK`, `arisen_KNK_dead`, `knk_drawn_by_rule`.
-/

namespace EndgameChess.Rules

open EndgameChess.KK

/-! ## The K+N vs K board -/

/-- Colour-`σ` king on `sk`, colour-`σ` knight on `ns`, colour-`σ.opp` king on `wk`,
nothing else. -/
def knkBoard (σ : Colour) (sk ns wk : Square) : Board := fun s =>
  if s = sk then some ⟨σ, .king⟩
  else if s = ns then some ⟨σ, .knight⟩
  else if s = wk then some ⟨σ.opp, .king⟩
  else none

/-- Exactly king + knight of colour `σ` against the other colour's lone king. Turn,
castling rights and en-passant target are arbitrary. -/
def IsKNK (q : Position) (σ : Colour) (sk ns wk : Square) : Prop :=
  sk ≠ ns ∧ sk ≠ wk ∧ ns ≠ wk ∧ q.board = knkBoard σ sk ns wk

theorem knkBoard_some {σ : Colour} {sk ns wk s : Square} {pc : Piece}
    (h : knkBoard σ sk ns wk s = some pc) :
    (s = sk ∧ pc = ⟨σ, .king⟩) ∨ (s = ns ∧ pc = ⟨σ, .knight⟩) ∨
      (s = wk ∧ pc = ⟨σ.opp, .king⟩) := by
  unfold knkBoard at h
  by_cases h1 : s = sk
  · subst h1; simp at h; exact Or.inl ⟨rfl, h.symm⟩
  · by_cases h2 : s = ns
    · subst h2; simp [h1] at h; exact Or.inr (Or.inl ⟨rfl, h.symm⟩)
    · by_cases h3 : s = wk
      · subst h3; simp [h1, h2] at h; exact Or.inr (Or.inr ⟨rfl, h.symm⟩)
      · simp [h1, h2, h3] at h

theorem knkBoard_eq_none {σ : Colour} {sk ns wk s : Square} :
    knkBoard σ sk ns wk s = none ↔ s ≠ sk ∧ s ≠ ns ∧ s ≠ wk := by
  unfold knkBoard
  by_cases h1 : s = sk <;> by_cases h2 : s = ns <;> by_cases h3 : s = wk <;> simp_all

theorem knkBoard_sk {σ : Colour} {sk ns wk : Square} :
    knkBoard σ sk ns wk sk = some ⟨σ, .king⟩ := by
  simp [knkBoard]

theorem knkBoard_ns {σ : Colour} {sk ns wk : Square} (h : sk ≠ ns) :
    knkBoard σ sk ns wk ns = some ⟨σ, .knight⟩ := by
  have : ¬ ns = sk := fun e => h e.symm
  simp [knkBoard, this]

theorem knkBoard_wk {σ : Colour} {sk ns wk : Square} (h1 : sk ≠ wk) (h2 : ns ≠ wk) :
    knkBoard σ sk ns wk wk = some ⟨σ.opp, .king⟩ := by
  have e1 : ¬ wk = sk := fun e => h1 e.symm
  have e2 : ¬ wk = ns := fun e => h2 e.symm
  simp [knkBoard, e1, e2]

theorem nrp_knkBoard {q : Position} {σ : Colour} {sk ns wk : Square}
    (h : q.board = knkBoard σ sk ns wk) : NRP q := by
  intro s pc hs
  rw [h] at hs
  rcases knkBoard_some hs with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp

/-! ## Attack and check on a K+N vs K board (king and knight attacks ignore the board) -/

theorem attacked_knk {σ : Colour} {sk ns wk : Square} (h12 : sk ≠ ns) (h13 : sk ≠ wk)
    (h23 : ns ≠ wk) (t : Square) (c : Colour) :
    attacked (knkBoard σ sk ns wk) t c = true ↔
      (c = σ ∧ (dInf sk t = 1 ∨ knightGeom ns t = true)) ∨ (c = σ.opp ∧ dInf wk t = 1) := by
  rw [attacked_iff]
  constructor
  · rintro ⟨s, pc, hb, hc, ha⟩
    rcases knkBoard_some hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨hc.symm, Or.inl (by simpa [attacksFrom, kingGeom_iff] using ha)⟩
    · exact Or.inl ⟨hc.symm, Or.inr (by simpa [attacksFrom] using ha)⟩
    · exact Or.inr ⟨hc.symm, by simpa [attacksFrom, kingGeom_iff] using ha⟩
  · rintro (⟨rfl, hk | hn⟩ | ⟨rfl, hk⟩)
    · exact ⟨sk, _, knkBoard_sk, rfl, by simpa [attacksFrom, kingGeom_iff] using hk⟩
    · exact ⟨ns, _, knkBoard_ns h12, rfl, by simpa [attacksFrom] using hn⟩
    · exact ⟨wk, _, knkBoard_wk h13 h23, rfl, by simpa [attacksFrom, kingGeom_iff] using hk⟩

theorem kingSq_knk {σ : Colour} {sk ns wk s : Square} {c : Colour} (h13 : sk ≠ wk)
    (h23 : ns ≠ wk) :
    knkBoard σ sk ns wk s = some ⟨c, .king⟩ ↔ (c = σ ∧ s = sk) ∨ (c = σ.opp ∧ s = wk) := by
  constructor
  · intro h
    rcases knkBoard_some h with ⟨e, he⟩ | ⟨_, he⟩ | ⟨e, he⟩
    · simp only [Piece.mk.injEq] at he; exact Or.inl ⟨he.1, e⟩
    · simp at he
    · simp only [Piece.mk.injEq] at he; exact Or.inr ⟨he.1, e⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact knkBoard_sk
    · exact knkBoard_wk h13 h23

/-- The lone king is in check iff the strong king is adjacent or the knight attacks it. -/
theorem inCheck_weak_knk {q : Position} {σ : Colour} {sk ns wk : Square} (h12 : sk ≠ ns)
    (h13 : sk ≠ wk) (h23 : ns ≠ wk) (hb : q.board = knkBoard σ sk ns wk) :
    inCheck q σ.opp = true ↔ dInf sk wk = 1 ∨ knightGeom ns wk = true := by
  rw [inCheck_iff, hb]
  constructor
  · rintro ⟨s, hs, hat⟩
    rcases (kingSq_knk h13 h23).1 hs with ⟨e, _⟩ | ⟨_, rfl⟩
    · exact absurd e.symm (opp_ne _)
    · rw [opp_opp] at hat
      rcases (attacked_knk h12 h13 h23 _ _).1 hat with ⟨_, h⟩ | ⟨e, _⟩
      · exact h
      · exact absurd e (opp_ne _)
  · intro h
    refine ⟨wk, (kingSq_knk h13 h23).2 (Or.inr ⟨rfl, rfl⟩), ?_⟩
    rw [opp_opp, attacked_knk h12 h13 h23]
    exact Or.inl ⟨rfl, h⟩

/-- The strong king is in check iff the lone king is adjacent. -/
theorem inCheck_strong_knk {q : Position} {σ : Colour} {sk ns wk : Square} (h12 : sk ≠ ns)
    (h13 : sk ≠ wk) (h23 : ns ≠ wk) (hb : q.board = knkBoard σ sk ns wk) :
    inCheck q σ = true ↔ dInf wk sk = 1 := by
  rw [inCheck_iff, hb]
  constructor
  · rintro ⟨s, hs, hat⟩
    rcases (kingSq_knk h13 h23).1 hs with ⟨_, rfl⟩ | ⟨e, _⟩
    · rcases (attacked_knk h12 h13 h23 _ _).1 hat with ⟨e, _⟩ | ⟨_, hk⟩
      · exact absurd e.symm (opp_ne _)
      · exact hk
    · exact absurd e (opp_ne _)
  · intro h
    refine ⟨sk, (kingSq_knk h13 h23).2 (Or.inl ⟨rfl, rfl⟩), ?_⟩
    rw [attacked_knk h12 h13 h23]
    exact Or.inr ⟨rfl, h⟩

theorem colour_cases (σ c : Colour) : c = σ ∨ c = σ.opp := by
  cases σ <;> cases c <;> simp [Colour.opp]

/-! ## N0: the last move was legal, so the kings are apart and the strong king is safe -/

theorem kings_apart_of_legal {p q : Position} {σ : Colour} {sk ns wk : Square}
    (hl : Legal p q) (hk : IsKNK q σ sk ns wk) : 2 ≤ dInf sk wk := by
  obtain ⟨h12, h13, h23, hb⟩ := hk
  have h0 : dInf sk wk ≠ 0 := fun h => h13 (dInf_eq_zero_iff.1 h)
  have h1 : dInf sk wk ≠ 1 := by
    intro h1
    have hsafe := legal_mover_safe hl
    rcases colour_cases σ p.turn with e | e <;> rw [e] at hsafe
    · rw [(inCheck_strong_knk h12 h13 h23 hb).2 (by rw [dInf_comm]; exact h1)] at hsafe
      cases hsafe
    · rw [(inCheck_weak_knk h12 h13 h23 hb).2 (Or.inl h1)] at hsafe
      cases hsafe
  omega

theorem strong_not_inCheck {q : Position} {σ : Colour} {sk ns wk : Square}
    (hk : IsKNK q σ sk ns wk) (hfar : 2 ≤ dInf sk wk) : inCheck q σ = false := by
  obtain ⟨h12, h13, h23, hb⟩ := hk
  cases h : inCheck q σ
  · rfl
  · have := (inCheck_strong_knk h12 h13 h23 hb).1 h
    rw [dInf_comm] at this; omega

/-! ## N1: knight geometry -/

theorem knightGeom_iff {s t : Square} :
    knightGeom s t = true ↔
      (absDiff s.1.val t.1.val = 1 ∧ absDiff s.2.val t.2.val = 2) ∨
      (absDiff s.1.val t.1.val = 2 ∧ absDiff s.2.val t.2.val = 1) := by
  simp only [knightGeom, dx, dy, absDiff, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
  omega

/-- **N1(c).** A knight attacking `k` attacks no orthogonal neighbour of `k` (colour). -/
theorem knight_not_orth {n k t : Square} (hn : knightGeom n k = true)
    (ht : absDiff k.1.val t.1.val + absDiff k.2.val t.2.val = 1) : knightGeom n t = false := by
  rw [knightGeom_iff] at hn
  cases h : knightGeom n t
  · rfl
  · rw [knightGeom_iff] at h
    simp only [absDiff] at hn ht h
    omega

/-- **N1(b).** A square adjacent to `k` is not the square of a knight attacking `k`. -/
theorem ne_of_knight_adj {n k t : Square} (hn : knightGeom n k = true) (ht : dInf k t = 1) :
    t ≠ n := by
  rintro rfl
  rw [knightGeom_iff] at hn
  simp only [dInf, absDiff] at hn ht
  omega

/-! ## N2: a checked lone king always has an orthogonal escape -/

theorem exists_adj (a : Fin 8) : ∃ a' : Fin 8, absDiff a.val a'.val = 1 := by
  revert a; decide

/-- **N2, geometric core.** With the kings apart and the knight checking `wk`, one of the
two orthogonal neighbours `h` (same rank) and `v` (same file) is attacked by neither the
strong king nor the knight. -/
theorem escape_square {sk ns wk : Square} (hfar : 2 ≤ dInf sk wk)
    (hn : knightGeom ns wk = true) :
    ∃ s, dInf wk s = 1 ∧ 2 ≤ dInf sk s ∧ knightGeom ns s = false := by
  obtain ⟨a', ha⟩ := exists_adj wk.1
  obtain ⟨b', hb⟩ := exists_adj wk.2
  let h : Square := (a', wk.2)
  let v : Square := (wk.1, b')
  have hh1 : dInf wk h = 1 := by simp only [h, dInf, absDiff] at ha ⊢; omega
  have hv1 : dInf wk v = 1 := by simp only [v, dInf, absDiff] at hb ⊢; omega
  have hhn : knightGeom ns h = false :=
    knight_not_orth hn (by simp only [h, absDiff] at ha ⊢; omega)
  have hvn : knightGeom ns v = false :=
    knight_not_orth hn (by simp only [v, absDiff] at hb ⊢; omega)
  by_cases hs : 2 ≤ dInf sk h
  · exact ⟨h, hh1, hs, hhn⟩
  · refine ⟨v, hv1, ?_, hvn⟩
    simp only [h, v, dInf, absDiff] at hs hfar ha hb ⊢
    omega

/-- **N2.** A checked lone king (kings apart) has a legal move: the kernel move from `wk`
to the square given by `escape_square`. -/
theorem weak_has_move {q : Position} {σ : Colour} {sk ns wk : Square}
    (hk : IsKNK q σ sk ns wk) (ht : q.turn = σ.opp) (hfar : 2 ≤ dInf sk wk)
    (hc : inCheck q σ.opp = true) : ∃ r, Legal q r := by
  obtain ⟨h12, h13, h23, hb⟩ := hk
  have hn : knightGeom ns wk = true := by
    rcases (inCheck_weak_knk h12 h13 h23 hb).1 hc with h | h
    · omega
    · exact h
  obtain ⟨s, hs1, hs2, hs3⟩ := escape_square hfar hn
  have hsk : s ≠ sk := by
    rintro rfl; rw [(dInf_eq_zero_iff).2 rfl] at hs2; omega
  have hsn : s ≠ ns := ne_of_knight_adj hn hs1
  have hsw : s ≠ wk := by
    rintro rfl; rw [(dInf_eq_zero_iff).2 rfl] at hs1; cases hs1
  let m : Move := ⟨wk, s, none⟩
  have hsrc : q.board m.src = some ⟨q.turn, .king⟩ := by
    show q.board wk = _
    rw [hb, ht]; exact knkBoard_wk h13 h23
  have hdst : q.board s = none := by rw [hb]; exact knkBoard_eq_none.2 ⟨hsk, hsn, hsw⟩
  have hp : isPseudo q m = true := by
    rw [isPseudo_of_king hsrc]
    have hg : kingGeom wk s = true := kingGeom_iff.2 hs1
    simp [m, targetOK, hdst, hg]
  have hnrp : NRP q := nrp_knkBoard hb
  have hb' : (play q m).board = knkBoard σ sk ns s := by
    rw [play_nrp hnrp hp]
    funext x
    show (if x = s then q.board wk else if x = wk then none else q.board x) = _
    rw [hb]
    unfold knkBoard
    by_cases e1 : x = s
    · subst e1; simp [hsk, hsn, Ne.symm h13, Ne.symm h23]
    · by_cases e2 : x = wk
      · subst e2; simp [e1, Ne.symm h13, Ne.symm h23]
      · simp [e1, e2]
  have hchk : inCheck (play q m) q.turn = false := by
    rw [ht]
    cases h : inCheck (play q m) σ.opp
    · rfl
    · rcases (inCheck_weak_knk h12 (Ne.symm hsk) (Ne.symm hsn) hb').1 h with e | e
      · omega
      · rw [hs3] at e; cases e
  exact ⟨play q m, ⟨m, by simp [isLegal, hp, hchk], rfl⟩⟩

/-! ## N3: closure — a legal move from K+N vs K gives K+N vs K or K vs K -/

theorem targetOK_some {p : Position} {t : Square} {pc : Piece} (h : targetOK p t = true)
    (hb : p.board t = some pc) : pc.colour ≠ p.turn ∧ pc.kind ≠ .king := by
  unfold targetOK at h
  rw [hb] at h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  exact h

theorem targetOK_of_isPseudo {p : Position} {m : Move} (h : isPseudo p m = true) :
    targetOK p m.dst = true := by
  unfold isPseudo at h
  split at h
  · contradiction
  · simp only [Bool.and_eq_true] at h
    exact h.1.2

theorem step_closed {r r' : Position} {σ : Colour} {sk ns wk : Square}
    (hk : IsKNK r σ sk ns wk) (hl : Legal r r') :
    (∃ a b c, IsKNK r' σ a b c) ∨ (∃ w b, IsKK r' w b) := by
  obtain ⟨h12, h13, h23, hb⟩ := hk
  obtain ⟨m, hm, rfl⟩ := hl
  have hp : isPseudo r m = true := by
    unfold isLegal at hm; simp only [Bool.and_eq_true] at hm; exact hm.1
  have htg := targetOK_of_isPseudo hp
  obtain ⟨pc, hsrc, hcol⟩ := own_of_isPseudo hp
  have hboard : (play r m).board =
      fun x => if x = m.dst then r.board m.src else if x = m.src then none else r.board x := by
    rw [play_nrp (nrp_knkBoard hb) hp]
  -- the destination is never a king square
  have hdk : m.dst ≠ sk := by
    intro e
    have := (targetOK_some htg (by rw [hb, e]; exact knkBoard_sk)).2
    exact this rfl
  have hdw : m.dst ≠ wk := by
    intro e
    have := (targetOK_some htg (by rw [hb, e]; exact knkBoard_wk h13 h23)).2
    exact this rfl
  rw [hb] at hsrc
  rcases knkBoard_some hsrc with ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨e, rfl⟩
  · -- the strong king moves
    have hdn : m.dst ≠ ns := by
      intro e'
      have := (targetOK_some htg (by rw [hb, e']; exact knkBoard_ns h12)).1
      exact this hcol
    refine Or.inl ⟨m.dst, ns, wk, hdn, hdw, h23, ?_⟩
    rw [hboard]; funext x; rw [hb, e]; unfold knkBoard
    by_cases e1 : x = m.dst
    · subst e1; simp
    · by_cases e2 : x = sk
      · subst e2; simp [e1, h12, h13]
      · simp [e1, e2]
  · -- the knight moves
    refine Or.inl ⟨sk, m.dst, wk, Ne.symm hdk, h13, hdw, ?_⟩
    rw [hboard]; funext x; rw [hb, e]; unfold knkBoard
    by_cases e1 : x = m.dst
    · subst e1; simp [hdk, Ne.symm h12]
    · by_cases e2 : x = ns
      · subst e2; simp [e1, Ne.symm h12, h23]
      · simp [e1, e2]
  · -- the lone king moves, possibly capturing the knight
    by_cases hcap : m.dst = ns
    · refine Or.inr ?_
      cases σ with
      | white =>
        refine ⟨sk, ns, h12, ?_⟩
        rw [hboard]; funext x; rw [hb, e, hcap]; unfold knkBoard kkBoard
        by_cases e1 : x = ns
        · subst e1; simp [Ne.symm h12, Ne.symm h13, h23.symm, Colour.opp]
        · by_cases e2 : x = wk
          · subst e2; simp [e1, Ne.symm h13]
          · simp [e1, e2]
      | black =>
        refine ⟨ns, sk, Ne.symm h12, ?_⟩
        rw [hboard]; funext x; rw [hb, e, hcap]; unfold knkBoard kkBoard
        by_cases e1 : x = ns
        · subst e1; simp [Ne.symm h13, h23.symm, Colour.opp]
        · by_cases e2 : x = wk
          · subst e2; simp [e1, Ne.symm h13]
          · by_cases e3 : x = sk
            · subst e3; simp [e1, e2]
            · simp [e1, e2, e3]
    · refine Or.inl ⟨sk, ns, m.dst, h12, Ne.symm hdk, Ne.symm hcap, ?_⟩
      rw [hboard]; funext x; rw [hb, e]; unfold knkBoard
      by_cases e1 : x = m.dst
      · subst e1; simp [hdk, hcap, Ne.symm h13, Ne.symm h23]
      · by_cases e2 : x = wk
        · subst e2; simp [e1, Ne.symm h13, Ne.symm h23]
        · simp [e1, e2]

/-! ## N4: induction over move sequences -/

/-- Every position reachable from a K+N vs K position produced by a legal move is either
such a position itself, or reachable from a K vs K position produced by a legal move. -/
theorem reach_cases {q r : Position} (hq : ∃ p, Legal p q) (hk : ∃ σ a b c, IsKNK q σ a b c)
    (hr : ReachK q r) :
    ((∃ p, Legal p r) ∧ ∃ σ a b c, IsKNK r σ a b c) ∨
      (∃ r0 w b, (∃ p, Legal p r0) ∧ IsKK r0 w b ∧ ReachK r0 r) := by
  induction hr with
  | refl => exact Or.inl ⟨hq, hk⟩
  | @tail r1 r2 _ hl ih =>
    rcases ih with ⟨_, σ, a, b, c, hk1⟩ | ⟨r0, w, b, hp0, hkk, hr0⟩
    · rcases step_closed hk1 hl with ⟨a', b', c', hk2⟩ | ⟨w, b, hkk⟩
      · exact Or.inl ⟨⟨r1, hl⟩, σ, a', b', c', hk2⟩
      · exact Or.inr ⟨r2, w, b, ⟨r1, hl⟩, hkk, ReachK.refl _⟩
    · exact Or.inr ⟨r0, w, b, hp0, hkk, ReachK.tail hr0 hl⟩

/-- No K+N vs K position produced by a legal move is checkmate. -/
theorem not_mated_KNK {p r : Position} {σ : Colour} {sk ns wk : Square} (hl : Legal p r)
    (hk : IsKNK r σ sk ns wk) : ¬ MatedK r := by
  rintro ⟨hc, hno⟩
  have hfar := kings_apart_of_legal hl hk
  rcases colour_cases σ r.turn with e | e
  · rw [e, strong_not_inCheck hk hfar] at hc; cases hc
  · rw [e] at hc
    exact hno (weak_has_move hk e hfar hc)

/-! ## Main theorems -/

/-- **EC-C003 (kernel form).** A K+N vs K position (either orientation) produced by any
legal move — from any material, with any flags — is dead. -/
theorem dead_of_legal_into_KNK {p q : Position} {σ : Colour} {sk ns wk : Square}
    (hl : Legal p q) (hk : IsKNK q σ sk ns wk) : DeadK q := by
  rintro ⟨r, hr, hm⟩
  rcases reach_cases ⟨p, hl⟩ ⟨σ, sk, ns, wk, hk⟩ hr with
    ⟨⟨p', hl'⟩, σ', a, b, c, hk'⟩ | ⟨r0, w, b, ⟨p0, hl0⟩, hkk, hr0⟩
  · exact not_mated_KNK hl' hk' hm
  · exact dead_of_legal_into_KK hl0 hkk ⟨r, hr0, hm⟩

theorem initial_not_KNK (σ : Colour) (sk ns wk : Square) : ¬ IsKNK initial σ sk ns wk := by
  rintro ⟨_, _, _, hb⟩
  have h := congrFun hb ((0 : Fin 8), (1 : Fin 8))
  rw [initial_a2] at h
  simp only [knkBoard] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp only [Option.some.injEq, Piece.mk.injEq] at h
        exact absurd h.2 (by decide)
      · simp at h

/-- **EC-C003, arisen form.** Every K+N vs K position (either orientation) that has arisen
in a game is dead. -/
theorem arisen_KNK_dead {q : Position} {σ : Colour} {sk ns wk : Square} (ha : Arisen q)
    (hk : IsKNK q σ sk ns wk) : DeadK q := by
  cases ha with
  | refl => exact absurd hk (initial_not_KNK σ sk ns wk)
  | tail _ hl => exact dead_of_legal_into_KNK hl hk

/-- Under the rule encoding `Rule5_2_2`, every arisen K+N vs K position is an immediate
draw. -/
theorem knk_drawn_by_rule {q : Position} {σ : Colour} {sk ns wk : Square} (ha : Arisen q)
    (hk : IsKNK q σ sk ns wk) : Rule5_2_2 q .draw :=
  ⟨ha, arisen_KNK_dead ha hk, rfl⟩

/-! ## Non-vacuity (kernel-checked by `decide`) -/

/-- A K+N vs K board as a concrete `Position` with no flags. -/
def knkPos (σ : Colour) (sk ns wk : Square) (t : Colour) : Position :=
  { board := knkBoard σ sk ns wk, turn := t, castling := noRights, ep := none }

/-- White Kc6, Na4, Black Ka8, White to move; Nb6+ is legal and gives check. -/
def knkPreCheck : Position := knkPos .white ((2 : Fin 8), (5 : Fin 8)) ((0 : Fin 8), (3 : Fin 8))
  ((0 : Fin 8), (7 : Fin 8)) .white

def nb6 : Move := ⟨((0 : Fin 8), (3 : Fin 8)), ((1 : Fin 8), (5 : Fin 8)), none⟩

/-- The theorem's hypothesis is satisfiable with the knight giving check: Nb6+ is legal,
produces K+N vs K, puts Black in check, and the result is dead. -/
theorem knight_check_example :
    Legal knkPreCheck (play knkPreCheck nb6) ∧
    IsKNK (play knkPreCheck nb6) .white ((2 : Fin 8), (5 : Fin 8)) ((1 : Fin 8), (5 : Fin 8))
      ((0 : Fin 8), (7 : Fin 8)) ∧
    inCheck (play knkPreCheck nb6) .black = true ∧
    DeadK (play knkPreCheck nb6) := by
  have hleg : isLegal knkPreCheck nb6 = true := by decide
  have hall : ∀ s ∈ allSquares, (play knkPreCheck nb6).board s =
      knkBoard .white ((2 : Fin 8), (5 : Fin 8)) ((1 : Fin 8), (5 : Fin 8))
        ((0 : Fin 8), (7 : Fin 8)) s := by decide
  have hk : IsKNK (play knkPreCheck nb6) .white ((2 : Fin 8), (5 : Fin 8))
      ((1 : Fin 8), (5 : Fin 8)) ((0 : Fin 8), (7 : Fin 8)) :=
    ⟨by decide, by decide, by decide, funext fun s => hall s (mem_allSquares s)⟩
  have hl : Legal knkPreCheck (play knkPreCheck nb6) := ⟨nb6, hleg, rfl⟩
  exact ⟨hl, hk, by decide, dead_of_legal_into_KNK hl hk⟩

/-- Black Ka8, White Kb6 + Nc6, Black to move: stalemate (no check, no legal move).
Stalemates exist in the class, so the theorem is not "every position has a move". -/
theorem knk_stalemate_example :
    inCheck (knkPos .white ((1 : Fin 8), (5 : Fin 8)) ((2 : Fin 8), (5 : Fin 8))
      ((0 : Fin 8), (7 : Fin 8)) .black) .black = false ∧
    legalMoves (knkPos .white ((1 : Fin 8), (5 : Fin 8)) ((2 : Fin 8), (5 : Fin 8))
      ((0 : Fin 8), (7 : Fin 8)) .black) = [] := by
  decide

/-- Black Kb2 takes the unprotected Nc3 (White Kh8): the capture branch into K vs K. -/
theorem knight_capture_example :
    let p := knkPos .white ((7 : Fin 8), (7 : Fin 8)) ((2 : Fin 8), (2 : Fin 8))
      ((1 : Fin 8), (1 : Fin 8)) .black
    let m : Move := ⟨((1 : Fin 8), (1 : Fin 8)), ((2 : Fin 8), (2 : Fin 8)), none⟩
    Legal p (play p m) ∧ IsKK (play p m) ((7 : Fin 8), (7 : Fin 8)) ((2 : Fin 8), (2 : Fin 8)) := by
  intro p m
  have hleg : isLegal p m = true := by decide
  have hall : ∀ s ∈ allSquares, (play p m).board s =
      kkBoard ((7 : Fin 8), (7 : Fin 8)) ((2 : Fin 8), (2 : Fin 8)) s := by decide
  exact ⟨⟨m, hleg, rfl⟩, by decide, funext fun s => hall s (mem_allSquares s)⟩

end EndgameChess.Rules
