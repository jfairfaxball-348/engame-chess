import EndgameChess.Rules.KRKLive.Basic

/-!
# EC-C008 end-game half — Lemmas M, E, C, W and S (S021)

Faithful formalisation of §3–§4 of `proofs/EC-C008_KRK_LIVE.md` (route v3, P2–P5), in the
KRK move model of `Rules.KRKLive.Basic`. Every lemma is a **schema over arbitrary
squares**, proved from coordinate inequalities, never by enumerating positions. The model
moves are kernel-legal (`step_sound`) and a model mate is a kernel mate (`mate_sound`).

Coordinates: a square is `(file, rank)` with values `0…7`; a1 = `(0,0)`, h8 = `(7,7)`.
The strong king `S` is normalised (`Normal`: `sx ≤ 3`, `sy ≥ 2`, F4).

Lemma map (prose → Lean):
- tempo pairs `G` (h8 ↔ g8) and `H` (h8 ↔ h7) with their regions: `TempoPair`, `TempoPair.Mem`,
  `TempoPair.Region`, `tempo_step`, `lone_step_region`;
- Lemma M: `krk_lemmaM`;
- Lemma E: `krk_lemmaE_lone` (induction on `j`), `krk_lemmaE`;
- Lemma C: `Conn`, `rect_minus_box_conn` (rectangle minus box), `krk_conn_region` (instance);
- Lemma W: `krk_lemmaW` (induction on the path given by Lemma C);
- Lemma S: `krk_lemmaS`; kernel form `krk_settled_live` (rook on h8, strong side to move,
  `S` normalised, lone king not in check ⇒ `¬DeadK`);
- non-vacuity: `krkM_mate_example`, `krkM_example`, `krkS_rank8_example`,
  `krkS_g7_example`.

Lemma M is stated without the prose bound `a ≤ 4`: it follows from `r ≥ a + 2`, `r ≤ 7`.
-/

namespace EndgameChess.Rules

set_option linter.unusedSimpArgs false

open EndgameChess.KK

/-! ## Tempo pairs and regions -/

/-- The two tempo pairs: `G` = {h8, g8}, `H` = {h8, h7}. -/
inductive TempoPair
  | G
  | H
  deriving DecidableEq, Repr

/-- The rook stands on a square of the pair. -/
def TempoPair.Mem : TempoPair → Square → Prop
  | .G, s => s.2.val = 7 ∧ (s.1.val = 7 ∨ s.1.val = 6)
  | .H, s => s.1.val = 7 ∧ (s.2.val = 7 ∨ s.2.val = 6)

/-- The pair's region: `G` files a–f × ranks 1–7, `H` files a–g × ranks 1–6, each minus
`N1[S]`. -/
def TempoPair.Region (sk : Square) : TempoPair → Square → Prop
  | .G, s => s.1.val ≤ 5 ∧ s.2.val ≤ 6 ∧ 2 ≤ dInf sk s
  | .H, s => s.1.val ≤ 6 ∧ s.2.val ≤ 5 ∧ 2 ≤ dInf sk s

theorem TempoPair.region_far {P : TempoPair} {sk s : Square} (h : P.Region sk s) : 2 ≤ dInf sk s := by
  cases P <;> exact h.2.2

/-- From a square of the pair, the rook sees no square of the region (not even along a
line), and does not stand on one. -/
theorem TempoPair.no_line {P : TempoPair} {sk rs t : Square} (hm : P.Mem rs) (ht : P.Region sk t) :
    ¬ RookLine rs t ∧ t ≠ rs := by
  rw [ne_iff_coords]
  cases P <;> simp only [TempoPair.Mem, TempoPair.Region, RookLine, true_and, and_true, true_or, or_true] at hm ht ⊢ <;> omega

/-- **Tempo move.** With `S` on files a–d and `L` in the region, the rook moves to the
other square of its pair. -/
theorem tempo_step (P : TempoPair) {sk rs wk : Square} (hm : P.Mem rs) (hS : sk.1.val ≤ 3)
    (hw : P.Region sk wk) :
    ∃ rs', P.Mem rs' ∧ StepM ⟨sk, rs, wk, true⟩ ⟨sk, rs', wk, false⟩ := by
  have hfar := TempoPair.region_far hw
  cases P with
  | G =>
    simp only [TempoPair.Mem, TempoPair.Region, true_and, and_true, true_or, or_true] at hm hw
    rcases hm with ⟨hy, hx | hx⟩
    · refine ⟨(⟨6, by decide⟩, ⟨7, by decide⟩), ⟨rfl, by decide⟩,
        StepM.rook ?_ ?_ ?_ ?_ ?_ hfar⟩ <;>
        simp only [RookLine, OnSeg, ne_iff_coords, true_and, and_true, true_or, or_true] <;> omega
    · refine ⟨(⟨7, by decide⟩, ⟨7, by decide⟩), ⟨rfl, by decide⟩,
        StepM.rook ?_ ?_ ?_ ?_ ?_ hfar⟩ <;>
        simp only [RookLine, OnSeg, ne_iff_coords, true_and, and_true, true_or, or_true] <;> omega
  | H =>
    simp only [TempoPair.Mem, TempoPair.Region, true_and, and_true, true_or, or_true] at hm hw
    rcases hm with ⟨hx, hy | hy⟩
    · refine ⟨(⟨7, by decide⟩, ⟨6, by decide⟩), ⟨rfl, by decide⟩,
        StepM.rook ?_ ?_ ?_ ?_ ?_ hfar⟩ <;>
        simp only [RookLine, OnSeg, ne_iff_coords, true_and, and_true, true_or, or_true] <;> omega
    · refine ⟨(⟨7, by decide⟩, ⟨7, by decide⟩), ⟨rfl, by decide⟩,
        StepM.rook ?_ ?_ ?_ ?_ ?_ hfar⟩ <;>
        simp only [RookLine, OnSeg, ne_iff_coords, true_and, and_true, true_or, or_true] <;> omega

/-- **Lone-king step into the region.** Legal whichever square of the pair holds the
rook: the target is not adjacent to `S`, and the rook's lines miss the region. -/
theorem lone_step_region {P : TempoPair} {sk rs wk t : Square} (hm : P.Mem rs)
    (hd : dInf wk t = 1) (ht : P.Region sk t) :
    StepM ⟨sk, rs, wk, false⟩ ⟨sk, rs, t, true⟩ := by
  obtain ⟨hl, hne⟩ := TempoPair.no_line hm ht
  exact StepM.lone hd hne (TempoPair.region_far ht) (fun h => hl h.1)

/-! ## Lemma M (mate pattern) -/

/-- **Lemma M.** `L = (a,0)`, `S = (a,2)`, the rook on `(r,y)` with `r ≥ a+2`, `y ≥ 1`,
the strong side to move: `R → (r,0)` is legal and mates. -/
theorem krk_lemmaM {sk rs wk : Square} (hL : wk.2.val = 0) (hSx : sk.1.val = wk.1.val)
    (hSy : sk.2.val = 2) (hr : wk.1.val + 2 ≤ rs.1.val) (hy : 1 ≤ rs.2.val) :
    WinM ⟨sk, rs, wk, true⟩ := by
  let t : Square := (rs.1, ⟨0, by decide⟩)
  have ht1 : t.1.val = rs.1.val := rfl
  have ht2 : t.2.val = 0 := rfl
  refine winM_of_step (StepM.rook (t := t) ?_ ?_ ?_ ?_ ?_ ?_) (winM_of_mate ⟨rfl, ?_, ?_⟩)
  all_goals simp only [RookSees, RookLine, OnSeg, ne_iff_coords, dInf, absDiff, ht1, ht2, true_and, and_true, true_or, or_true]
  all_goals omega

/-! ## Lemma E (escort, P3–P5) -/

/-- **Lemma E, lone king to move**, by induction on `j`: `L = (a,j)`, `S = (a,j+2)`,
`a ≤ 3`, `j ≤ 5`, the rook on a square of a tempo pair. -/
theorem krk_lemmaE_lone (P : TempoPair) : ∀ (j : Nat) {sk rs wk : Square}, P.Mem rs →
    wk.1.val ≤ 3 → wk.2.val = j → j ≤ 5 → sk.1.val = wk.1.val → sk.2.val = j + 2 →
    WinM ⟨sk, rs, wk, false⟩ := by
  intro j
  induction j with
  | zero =>
    intro sk rs wk hm ha hj _ hSx hSy
    -- shuttle: L → (a+1, 0), rook tempo, L → (a, 0), then Lemma M
    let t : Square := (⟨wk.1.val + 1, by omega⟩, ⟨0, by decide⟩)
    have hreg : ∀ u : Square, u.1.val ≤ 4 → u.2.val = 0 → (u.1.val + 1 = sk.1.val ∨
        u.1.val = sk.1.val + 1 ∨ u.1.val = sk.1.val) → P.Region sk u := by
      intro u h1 h2 h3
      cases P <;> simp only [TempoPair.Region, dInf, absDiff, true_and, and_true, true_or, or_true] <;> omega
    have ht : P.Region sk t := hreg t (by simp only [t, true_and, and_true, true_or, or_true] <;> omega) rfl (by simp only [t, true_and, and_true, true_or, or_true] <;> omega)
    have hw : P.Region sk wk := hreg wk (by omega) hj (by omega)
    refine winM_of_step (lone_step_region hm (by simp only [t, dInf, absDiff, true_and, and_true, true_or, or_true] <;> omega) ht) ?_
    obtain ⟨rs', hm', hs⟩ := tempo_step P hm (by omega) ht
    refine winM_of_step hs (winM_of_step (lone_step_region hm'
      (by simp only [t, dInf, absDiff, true_and, and_true, true_or, or_true] <;> omega) hw) ?_)
    apply krk_lemmaM hj hSx hSy
    · cases P <;> simp only [TempoPair.Mem, true_and, and_true, true_or, or_true] at hm' <;> omega
    · cases P <;> simp only [TempoPair.Mem, true_and, and_true, true_or, or_true] at hm' <;> omega
  | succ j ih =>
    intro sk rs wk hm ha hj hj5 hSx hSy
    -- L → (a, j), then S → (a, j+2)
    let t : Square := (wk.1, ⟨j, by omega⟩)
    let u : Square := (sk.1, ⟨j + 2, by omega⟩)
    have ht : P.Region sk t := by
      cases P <;> simp only [TempoPair.Region, t, dInf, absDiff, true_and, and_true, true_or, or_true] <;> omega
    refine winM_of_step (lone_step_region hm (by simp only [t, dInf, absDiff, true_and, and_true, true_or, or_true] <;> omega) ht) ?_
    have hu : u ≠ rs := by
      rw [ne_iff_coords]; cases P <;> (simp only [TempoPair.Mem, u, true_and, and_true, true_or, or_true] at hm ⊢; try omega)
    refine winM_of_step (StepM.king (by simp only [u, dInf, absDiff, true_and, and_true, true_or, or_true] <;> omega) hu
      (by simp only [u, t, dInf, absDiff, true_and, and_true, true_or, or_true] <;> omega)) ?_
    exact ih hm (by simp only [t, true_and, and_true, true_or, or_true] <;> omega) rfl (by omega) (by simp only [u, t, true_and, and_true, true_or, or_true] <;> omega)
      (by simp only [u, true_and, and_true, true_or, or_true] <;> omega)

/-- **Lemma E**, strong side to move. -/
theorem krk_lemmaE (P : TempoPair) {sk rs wk : Square} (hm : P.Mem rs) (ha : wk.1.val ≤ 3)
    (hj : wk.2.val ≤ 5) (hSx : sk.1.val = wk.1.val) (hSy : sk.2.val = wk.2.val + 2) :
    WinM ⟨sk, rs, wk, true⟩ := by
  by_cases h0 : wk.2.val = 0
  · apply krk_lemmaM h0 hSx (by omega)
    · cases P <;> simp only [TempoPair.Mem, true_and, and_true, true_or, or_true] at hm <;> omega
    · cases P <;> simp only [TempoPair.Mem, true_and, and_true, true_or, or_true] at hm <;> omega
  · have hw : P.Region sk wk := by
      cases P <;> simp only [TempoPair.Region, dInf, absDiff, true_and, and_true, true_or, or_true] <;> omega
    obtain ⟨rs', hm', hs⟩ := tempo_step P hm (by omega) hw
    exact winM_of_step hs (krk_lemmaE_lone P _ hm' ha rfl hj hSx hSy)

/-! ## Lemma C (region connectivity) -/

/-- King-step paths inside a set of squares `R`. -/
inductive Conn (R : Square → Prop) : Square → Square → Prop
  | refl {a : Square} : R a → Conn R a a
  | step {a b c : Square} : R a → dInf a b = 1 → Conn R b c → Conn R a c

theorem Conn.mem_left {R : Square → Prop} {a c : Square} (h : Conn R a c) : R a := by
  cases h with
  | refl h => exact h
  | step h _ _ => exact h

theorem Conn.mem_right {R : Square → Prop} {a c : Square} (h : Conn R a c) : R c := by
  induction h with
  | refl h => exact h
  | step _ _ _ ih => exact ih

theorem Conn.trans {R : Square → Prop} {a b c : Square} (h1 : Conn R a b) (h2 : Conn R b c) :
    Conn R a c := by
  induction h1 with
  | refl _ => exact h2
  | step ha hd _ ih => exact Conn.step ha hd (ih h2)

theorem Conn.snoc {R : Square → Prop} {a b c : Square} (h : Conn R a b) (hd : dInf b c = 1)
    (hc : R c) : Conn R a c :=
  h.trans (Conn.step h.mem_right hd (Conn.refl hc))

theorem Conn.symm {R : Square → Prop} {a b : Square} (h : Conn R a b) : Conn R b a := by
  induction h with
  | refl h => exact Conn.refl h
  | step ha hd _ ih => exact ih.snoc (by rw [dInf_comm]; exact hd) ha

/-- Walking along a rank from file `x` to file `c`, through squares of `R`. -/
theorem conn_rank {R : Square → Prop} (y : Fin 8) : ∀ (n : Nat) (x c : Fin 8),
    absDiff x.val c.val = n →
    (∀ z : Fin 8, min x.val c.val ≤ z.val → z.val ≤ max x.val c.val → R (z, y)) →
    Conn R (x, y) (c, y) := by
  intro n
  induction n with
  | zero =>
    intro x c hn hR
    have : x = c := Fin.ext (by simp only [absDiff, true_and, and_true, true_or, or_true] at hn; omega)
    subst this
    exact Conn.refl (hR x (by omega) (by omega))
  | succ n ih =>
    intro x c hn hR
    simp only [absDiff, true_and, and_true, true_or, or_true] at hn
    by_cases hlt : x.val < c.val
    · let x' : Fin 8 := ⟨x.val + 1, by omega⟩
      refine Conn.step (hR x (by omega) (by omega)) (by simp only [x', dInf, absDiff, true_and, and_true, true_or, or_true] <;> omega)
        (ih x' c (by simp only [x', absDiff, true_and, and_true, true_or, or_true] <;> omega) fun z h1 h2 => hR z ?_ ?_)
      · simp only [x', true_and, and_true, true_or, or_true] at h1; omega
      · simp only [x', true_and, and_true, true_or, or_true] at h2; omega
    · let x' : Fin 8 := ⟨x.val - 1, by omega⟩
      refine Conn.step (hR x (by omega) (by omega)) (by simp only [x', dInf, absDiff, true_and, and_true, true_or, or_true] <;> omega)
        (ih x' c (by simp only [x', absDiff, true_and, and_true, true_or, or_true] <;> omega) fun z h1 h2 => hR z ?_ ?_)
      · simp only [x', true_and, and_true, true_or, or_true] at h1; omega
      · simp only [x', true_and, and_true, true_or, or_true] at h2; omega

/-- Walking along a file from rank `y` to rank `c`, through squares of `R`. -/
theorem conn_file {R : Square → Prop} (x : Fin 8) : ∀ (n : Nat) (y c : Fin 8),
    absDiff y.val c.val = n →
    (∀ z : Fin 8, min y.val c.val ≤ z.val → z.val ≤ max y.val c.val → R (x, z)) →
    Conn R (x, y) (x, c) := by
  intro n
  induction n with
  | zero =>
    intro y c hn hR
    have : y = c := Fin.ext (by simp only [absDiff, true_and, and_true, true_or, or_true] at hn; omega)
    subst this
    exact Conn.refl (hR y (by omega) (by omega))
  | succ n ih =>
    intro y c hn hR
    simp only [absDiff, true_and, and_true, true_or, or_true] at hn
    by_cases hlt : y.val < c.val
    · let y' : Fin 8 := ⟨y.val + 1, by omega⟩
      refine Conn.step (hR y (by omega) (by omega)) (by simp only [y', dInf, absDiff, true_and, and_true, true_or, or_true] <;> omega)
        (ih y' c (by simp only [y', absDiff, true_and, and_true, true_or, or_true] <;> omega) fun z h1 h2 => hR z ?_ ?_)
      · simp only [y', true_and, and_true, true_or, or_true] at h1; omega
      · simp only [y', true_and, and_true, true_or, or_true] at h2; omega
    · let y' : Fin 8 := ⟨y.val - 1, by omega⟩
      refine Conn.step (hR y (by omega) (by omega)) (by simp only [y', dInf, absDiff, true_and, and_true, true_or, or_true] <;> omega)
        (ih y' c (by simp only [y', absDiff, true_and, and_true, true_or, or_true] <;> omega) fun z h1 h2 => hR z ?_ ?_)
      · simp only [y', true_and, and_true, true_or, or_true] at h1; omega
      · simp only [y', true_and, and_true, true_or, or_true] at h2; omega

/-- **Lemma C.** Let `R` be the rectangle `[x0,x1] × [y0,y1]` minus the box
`[bx0,bx1] × [by0,by1]`, and suppose some column `c` and some row `ρ` of the rectangle
miss the box (the box spans neither the full width nor the full height). Then every
square of `R` is joined to `(c, ρ)` by a path of king steps inside `R` (in fact rook
steps of length one). -/
theorem rect_minus_box_conn {R : Square → Prop} {x0 x1 y0 y1 bx0 bx1 by0 by1 : Nat}
    (hR : ∀ q : Square, R q ↔ (x0 ≤ q.1.val ∧ q.1.val ≤ x1 ∧ y0 ≤ q.2.val ∧ q.2.val ≤ y1) ∧
      ¬ (bx0 ≤ q.1.val ∧ q.1.val ≤ bx1 ∧ by0 ≤ q.2.val ∧ q.2.val ≤ by1))
    (c ρ : Fin 8) (hc : x0 ≤ c.val ∧ c.val ≤ x1 ∧ (c.val < bx0 ∨ bx1 < c.val))
    (hρ : y0 ≤ ρ.val ∧ ρ.val ≤ y1 ∧ (ρ.val < by0 ∨ by1 < ρ.val)) :
    ∀ q, R q → Conn R q (c, ρ) := by
  intro q hq
  obtain ⟨qx, qy⟩ := q
  rw [hR] at hq
  simp only [true_and, and_true, true_or, or_true] at hq
  by_cases hrow : qy.val < by0 ∨ by1 < qy.val
  · -- along `q`'s rank to column `c`, then along column `c` to row `ρ`
    refine (conn_rank qy _ qx c rfl fun z h1 h2 => ?_).trans
      (conn_file c _ qy ρ rfl fun z h1 h2 => ?_)
    · rw [hR]; simp only [true_and, and_true, true_or, or_true] <;> omega
    · rw [hR]; simp only [true_and, and_true, true_or, or_true] <;> omega
  · -- `q`'s rank meets the box, so `q`'s file misses it: along the file, then row `ρ`
    refine (conn_file qx _ qy ρ rfl fun z h1 h2 => ?_).trans
      (conn_rank ρ _ qx c rfl fun z h1 h2 => ?_)
    · rw [hR]; simp only [true_and, and_true, true_or, or_true] <;> omega
    · rw [hR]; simp only [true_and, and_true, true_or, or_true] <;> omega

/-- Lemma C applied to the regions of `G` (6 × 7) and `H` (7 × 6) minus `N1[S]`: any two
squares of a region are joined by a king path inside it. -/
theorem krk_conn_region (P : TempoPair) {sk p q : Square} (hn : Normal sk) (hp : P.Region sk p)
    (hq : P.Region sk q) : Conn (P.Region sk) p q := by
  obtain ⟨hsx, hsy⟩ := hn
  cases P with
  | G =>
    have hR : ∀ s : Square, TempoPair.Region sk .G s ↔
        (0 ≤ s.1.val ∧ s.1.val ≤ 5 ∧ 0 ≤ s.2.val ∧ s.2.val ≤ 6) ∧
        ¬ (sk.1.val - 1 ≤ s.1.val ∧ s.1.val ≤ sk.1.val + 1 ∧
          sk.2.val - 1 ≤ s.2.val ∧ s.2.val ≤ sk.2.val + 1) := by
      intro s; simp only [TempoPair.Region, dInf, absDiff, true_and, and_true, true_or, or_true] <;> omega
    have h1 := rect_minus_box_conn hR ⟨5, by decide⟩ ⟨0, by decide⟩ (by simp only [true_and, and_true, true_or, or_true] <;> omega)
      (by simp only [true_and, and_true, true_or, or_true] <;> omega)
    exact (h1 p hp).trans (h1 q hq).symm
  | H =>
    have hR : ∀ s : Square, TempoPair.Region sk .H s ↔
        (0 ≤ s.1.val ∧ s.1.val ≤ 6 ∧ 0 ≤ s.2.val ∧ s.2.val ≤ 5) ∧
        ¬ (sk.1.val - 1 ≤ s.1.val ∧ s.1.val ≤ sk.1.val + 1 ∧
          sk.2.val - 1 ≤ s.2.val ∧ s.2.val ≤ sk.2.val + 1) := by
      intro s; simp only [TempoPair.Region, dInf, absDiff, true_and, and_true, true_or, or_true] <;> omega
    have h1 := rect_minus_box_conn hR ⟨6, by decide⟩ ⟨0, by decide⟩ (by simp only [true_and, and_true, true_or, or_true] <;> omega)
      (by simp only [true_and, and_true, true_or, or_true] <;> omega)
    exact (h1 p hp).trans (h1 q hq).symm

/-! ## Lemma W (walk, P2) -/

/-- **Lemma W.** The rook on a square of a tempo pair, `L` in the pair's region, `S`
normalised, the strong side to move: mate is reachable. Each round is a rook tempo move
and the lone king's next step along the path to `T = (sx, sy − 2)` given by Lemma C; at
`T`, Lemma E applies. -/
theorem krk_lemmaW (P : TempoPair) {sk rs wk : Square} (hn : Normal sk) (hm : P.Mem rs)
    (hw : P.Region sk wk) : WinM ⟨sk, rs, wk, true⟩ := by
  have hsy := hn.2
  obtain ⟨T, hT1, hT2⟩ : ∃ T : Square, T.1.val = sk.1.val ∧ T.2.val + 2 = sk.2.val :=
    ⟨(sk.1, ⟨sk.2.val - 2, by omega⟩), rfl, by simp only; omega⟩
  have hT : P.Region sk T := by
    obtain ⟨hsx, hsy⟩ := hn
    cases P <;> simp only [TempoPair.Region, dInf, absDiff, true_and, and_true, true_or, or_true] <;> omega
  have hpath := krk_conn_region P hn hw hT
  clear hw
  induction hpath generalizing rs with
  | @refl a _ =>
    obtain ⟨hsx, hsy⟩ := hn
    exact krk_lemmaE P hm (by omega) (by omega) (by omega) (by omega)
  | @step a b _ ha hd hbc ih =>
    obtain ⟨rs', hm', hs⟩ := tempo_step P hm hn.1 ha
    exact winM_of_step hs (winM_of_step (lone_step_region hm' hd hbc.mem_left) (ih hm' hT1 hT2 hT))

/-! ## Lemma S (settling after P1) -/

/-- h8. -/
def sqH8 : Square := (⟨7, by decide⟩, ⟨7, by decide⟩)

/-- g8. -/
def sqG8 : Square := (⟨6, by decide⟩, ⟨7, by decide⟩)

/-- **Lemma S.** The rook on h8, the strong side to move, `S` normalised, the kings apart
and the lone king not in check. Then mate is reachable, via one of four cases:
1. `L` in region `G`: Lemma W with `G`;
2. `L` on the g-file, ranks 1–6: Lemma W with `H`;
3. `L = g7`: `Rh8–g8+`, `Kf6`, then Lemma W with `G`;
4. `L` on rank 8 (shielded by `S`): `Rh8–g8`, `L` one rank down, then Lemma W with `G`. -/
theorem krk_lemmaS {sk wk : Square} (hn : Normal sk) (hfar : 2 ≤ dInf sk wk) (hwr : wk ≠ sqH8)
    (hns : ¬ RookSees sqH8 wk sk wk) : WinM ⟨sk, sqH8, wk, true⟩ := by
  have hcases : (wk.1.val ≤ 5 ∧ wk.2.val ≤ 6) ∨ (wk.1.val = 6 ∧ wk.2.val ≤ 5) ∨
      (wk.1.val = 6 ∧ wk.2.val = 6) ∨
      (wk.1.val ≤ 5 ∧ wk.2.val = 7 ∧ sk.2.val = 7 ∧ wk.1.val + 2 ≤ sk.1.val) := by
    obtain ⟨hsx, hsy⟩ := hn
    rw [ne_iff_coords] at hwr
    simp only [RookSees, RookLine, OnSeg, sqH8, dInf, absDiff, true_and, and_true, true_or, or_true] at hns hfar hwr
    omega
  have hG8 : TempoPair.Mem .G sqG8 := ⟨rfl, Or.inr rfl⟩
  -- `Rh8–g8` is legal whenever `L` is not on g8 or h8
  have hrg : wk.1.val ≤ 6 → wk.2.val ≤ 6 ∨ wk.1.val ≤ 5 →
      StepM ⟨sk, sqH8, wk, true⟩ ⟨sk, sqG8, wk, false⟩ := by
    intro h1 h2
    obtain ⟨hsx, hsy⟩ := hn
    refine StepM.rook ?_ ?_ ?_ ?_ ?_ hfar <;>
      simp only [RookLine, OnSeg, ne_iff_coords, sqH8, sqG8, true_and, and_true, true_or, or_true] <;> omega
  rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩
  · exact krk_lemmaW .G hn ⟨rfl, Or.inl rfl⟩ ⟨h1, h2, hfar⟩
  · exact krk_lemmaW .H hn ⟨rfl, Or.inl rfl⟩ ⟨by omega, h2, hfar⟩
  · -- `L = g7`: `Rh8–g8+`, `Kg7–f6`
    let f6 : Square := (⟨5, by decide⟩, ⟨5, by decide⟩)
    have hf6 : TempoPair.Region sk .G f6 := by
      obtain ⟨hsx, hsy⟩ := hn
      simp only [TempoPair.Region, f6, dInf, absDiff, true_and, and_true, true_or, or_true] <;> omega
    refine winM_of_step (hrg (by omega) (by omega)) (winM_of_step
      (lone_step_region hG8 (by simp only [f6, dInf, absDiff, true_and, and_true, true_or, or_true] <;> omega) hf6) ?_)
    exact krk_lemmaW .G hn hG8 hf6
  · -- `L` on rank 8, shielded by `S`: `Rh8–g8`, then `L` one rank down
    let t : Square := (wk.1, ⟨6, by decide⟩)
    have ht : TempoPair.Region sk .G t := by
      simp only [TempoPair.Region, t, dInf, absDiff, true_and, and_true, true_or, or_true] <;> omega
    refine winM_of_step (hrg (by omega) (by omega)) (winM_of_step
      (lone_step_region hG8 (by simp only [t, dInf, absDiff, true_and, and_true, true_or, or_true] <;> omega) ht) ?_)
    exact krk_lemmaW .G hn hG8 ht

/-! ## Kernel form of the end-game half -/

/-- **End-game half, kernel form.** A K+R vs K kernel position (any flags) with the rook on
h8, the strong side to move, the strong king normalised and the lone king not in check, is
not dead. (P1 of S022 brings every normalised legal position to this situation or mates.) -/
theorem krk_settled_live {q : Position} {σ : Colour} {sk wk : Square}
    (hk : IsKRK q σ sk sqH8 wk) (ht : q.turn = σ) (hn : Normal sk)
    (hc : inCheck q σ.opp = false) : ¬ DeadK q := by
  obtain ⟨h12, h13, h23, hb⟩ := hk
  have hno : ¬ (dInf sk wk = 1 ∨ RookSees sqH8 wk sk wk) := by
    intro h; rw [(inCheck_weak_krk h12 h13 h23 hb).2 h] at hc; cases hc
  have h0 : dInf sk wk ≠ 0 := fun h => h13 (dInf_eq_zero_iff.1 h)
  have hfar : 2 ≤ dInf sk wk := by
    have : dInf sk wk ≠ 1 := fun h => hno (Or.inl h)
    omega
  exact not_deadK_of_winM ⟨⟨h12, h13, h23, hb⟩, by simp [ht]⟩
    (krk_lemmaS hn hfar (Ne.symm h23) (fun h => hno (Or.inr h)))

/-! ## Non-vacuity (kernel-checked by `decide`) -/

def sqC3 : Square := (⟨2, by decide⟩, ⟨2, by decide⟩)
def sqH5 : Square := (⟨7, by decide⟩, ⟨4, by decide⟩)
def sqC1 : Square := (⟨2, by decide⟩, ⟨0, by decide⟩)

/-- White Kc3, Rh5, Black Kc1, White to move: Lemma M with `a = 2`, `r = 7`, `y = 4`. -/
def mPos : Position := krkPos .white sqC3 sqH5 sqC1 .white

def rh1 : Move := ⟨sqH5, (⟨7, by decide⟩, ⟨0, by decide⟩), none⟩

set_option maxRecDepth 8192 in
/-- Lemma M's move, checked directly by the kernel generator: Rh5–h1 is legal, gives
check, and leaves Black without a legal move. -/
theorem krkM_mate_example :
    isLegal mPos rh1 = true ∧ inCheck (play mPos rh1) .black = true ∧
      legalMoves (play mPos rh1) = [] := by
  decide

/-- The same position is not dead **through `krk_lemmaM`** and the model soundness. -/
theorem krkM_example : ¬ DeadK mPos :=
  not_deadK_of_winM (a := ⟨sqC3, sqH5, sqC1, true⟩)
    ⟨⟨by decide, by decide, by decide, rfl⟩, rfl⟩
    (krk_lemmaM rfl rfl rfl (by decide) (by decide))

/-- White Kd8, Rh8, Black Ka8, White to move: Lemma S case 4 (the lone king on rank 8,
shielded by the strong king). -/
def sRank8Pos : Position :=
  krkPos .white (⟨3, by decide⟩, ⟨7, by decide⟩) sqH8 (⟨0, by decide⟩, ⟨7, by decide⟩) .white

theorem krkS_rank8_example : inCheck sRank8Pos .black = false ∧ ¬ DeadK sRank8Pos :=
  ⟨by decide, krk_settled_live ⟨by decide, by decide, by decide, rfl⟩ rfl
    ⟨by decide, by decide⟩ (by decide)⟩

/-- White Kb3, Rh8, Black Kg7, White to move: Lemma S case 3 (`L = g7`). -/
def sG7Pos : Position :=
  krkPos .white (⟨1, by decide⟩, ⟨2, by decide⟩) sqH8 (⟨6, by decide⟩, ⟨6, by decide⟩) .white

theorem krkS_g7_example : inCheck sG7Pos .black = false ∧ ¬ DeadK sG7Pos :=
  ⟨by decide, krk_settled_live ⟨by decide, by decide, by decide, rfl⟩ rfl
    ⟨by decide, by decide⟩ (by decide)⟩

end EndgameChess.Rules
