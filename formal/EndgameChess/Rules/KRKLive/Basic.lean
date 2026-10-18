import EndgameChess.Rules.KRK

/-!
# EC-C008 infrastructure — K+R vs K over the rules kernel (S021)

Shared definitions and lemmas for the formalisation of `proofs/EC-C008_KRK_LIVE.md`.
The frozen module `Rules.KRK` (EC-T0006) is imported, never edited.

- **Rook geometry in coordinates:** `RookLine`, `OnSeg`, and the bridges `lineGeom_iff`,
  `isBetween_iff_onSeg` from the kernel's `lineGeom` / `isBetween`.
- **Attack and check on `krkBoard`:** `attacked_krk`, `inCheck_weak_krk`,
  `inCheck_strong_krk` (the rook's attack uses `pathClear`, characterised by `RookSees`).
- **Moves:** `play_board_simple` (board after a move that is not a pawn move, promotion
  or castling); the kernel legality of a rook move, a strong-king step and a lone-king step
  on `krkBoard`, for **any** castling rights and en-passant target.
- **The KRK move model** `StepM` / `MateM` / `WinM`: a geometric description of the
  moves the route uses, stated only through `dInf`, `RookLine` and `OnSeg`. Soundness:
  `step_sound`, `mate_sound`, `not_deadK_of_winM` (a model mate gives a kernel
  `ReachK` path to a kernel `MatedK` position).
- **F4 (reflections):** `BoardSym` with the four reflections `symId`, `symX`, `symY`,
  `symXY`; `winM_of_sym` and `exists_sym_normal`.

**Choice recorded (S021):** the kernel as a whole is *not* reflection-invariant (castling
starts from the e-file and pawns move in one direction), so F4 is proved for the KRK move
model, whose definitions use only reflection-invariant geometry. The model's moves are
then transported to the kernel by the soundness lemmas, which hold whatever the flags.
-/

namespace EndgameChess.Rules

open EndgameChess.KK

/-! ## Rook geometry in coordinates -/

/-- Distinct squares on a common file or rank. -/
def RookLine (s t : Square) : Prop :=
  ¬ (s.1.val = t.1.val ∧ s.2.val = t.2.val) ∧ (s.1.val = t.1.val ∨ s.2.val = t.2.val)

/-- `r` lies strictly between `s` and `t` on their common file or rank. -/
def OnSeg (s r t : Square) : Prop :=
  (s.1.val = t.1.val ∧ r.1.val = s.1.val ∧
    ((s.2.val < r.2.val ∧ r.2.val < t.2.val) ∨ (t.2.val < r.2.val ∧ r.2.val < s.2.val))) ∨
  (s.2.val = t.2.val ∧ r.2.val = s.2.val ∧
    ((s.1.val < r.1.val ∧ r.1.val < t.1.val) ∨ (t.1.val < r.1.val ∧ r.1.val < s.1.val)))

/-- A rook on `rs` sees `t` when the only other pieces stand on `a` and `b`. -/
def RookSees (rs t a b : Square) : Prop := RookLine rs t ∧ ¬ OnSeg rs a t ∧ ¬ OnSeg rs b t

theorem ne_iff_coords {s t : Square} : s ≠ t ↔ ¬ (s.1.val = t.1.val ∧ s.2.val = t.2.val) := by
  rw [Ne, square_eq_iff]

theorem lineGeom_iff {s t : Square} : lineGeom s t = true ↔ RookLine s t := by
  simp only [lineGeom, dx, dy, RookLine, Bool.and_eq_true, bne_iff_ne, ne_eq, square_eq_iff,
    Bool.or_eq_true, beq_iff_eq]
  omega

theorem mul_aux {a b c d : Int} (hd : d = 0) (hb : b ≠ 0) : a * b = c * d ↔ a = 0 := by
  subst hd
  rw [Int.mul_zero, Int.mul_eq_zero]
  exact ⟨fun h => h.resolve_right hb, fun h => Or.inl h⟩

theorem mul_aux' {a b c d : Int} (hb : b = 0) (hd : d ≠ 0) : a * b = c * d ↔ c = 0 := by
  subst hb
  rw [Int.mul_zero, eq_comm, Int.mul_eq_zero]
  exact ⟨fun h => h.resolve_right hd, fun h => Or.inl h⟩

/-- On a rook line, the kernel's `isBetween` is the coordinate `OnSeg`. -/
theorem isBetween_iff_onSeg {s r t : Square} (h : RookLine s t) :
    isBetween s r t = true ↔ OnSeg s r t := by
  obtain ⟨hne, hl⟩ := h
  simp only [isBetween, dx, dy, Bool.and_eq_true, bne_iff_ne, ne_eq, square_eq_iff, beq_iff_eq]
  rcases hl with hl | hl
  · have hd : ((t.1.val : Int) - (s.1.val : Int)) = 0 := by omega
    have hb : ((t.2.val : Int) - (s.2.val : Int)) ≠ 0 := by omega
    rw [mul_aux hd hb]
    simp only [OnSeg, dInf, absDiff]
    omega
  · have hd : ((t.2.val : Int) - (s.2.val : Int)) = 0 := by omega
    have hb : ((t.1.val : Int) - (s.1.val : Int)) ≠ 0 := by omega
    rw [mul_aux' hd hb]
    simp only [OnSeg, dInf, absDiff]
    omega

theorem pathClear_iff {b : Board} {s t : Square} :
    pathClear b s t = true ↔ ∀ r, isBetween s r t = true → b r = none := by
  unfold pathClear
  rw [all_allSquares]
  apply forall_congr'
  intro r
  cases isBetween s r t <;> simp

theorem not_onSeg_self (s t : Square) : ¬ OnSeg s s t := by
  simp only [OnSeg]; omega

theorem not_onSeg_end (s t : Square) : ¬ OnSeg s t t := by
  simp only [OnSeg]; omega

/-! ## The K+R vs K board -/

theorem krkBoard_some {σ : Colour} {sk rs wk s : Square} {pc : Piece}
    (h : krkBoard σ sk rs wk s = some pc) :
    (s = sk ∧ pc = ⟨σ, .king⟩) ∨ (s = rs ∧ pc = ⟨σ, .rook⟩) ∨
      (s = wk ∧ pc = ⟨σ.opp, .king⟩) := by
  unfold krkBoard at h
  by_cases h1 : s = sk
  · subst h1; simp at h; exact Or.inl ⟨rfl, h.symm⟩
  · by_cases h2 : s = rs
    · subst h2; simp [h1] at h; exact Or.inr (Or.inl ⟨rfl, h.symm⟩)
    · by_cases h3 : s = wk
      · subst h3; simp [h1, h2] at h; exact Or.inr (Or.inr ⟨rfl, h.symm⟩)
      · simp [h1, h2, h3] at h

theorem krkBoard_eq_none {σ : Colour} {sk rs wk s : Square} :
    krkBoard σ sk rs wk s = none ↔ s ≠ sk ∧ s ≠ rs ∧ s ≠ wk := by
  unfold krkBoard
  by_cases h1 : s = sk <;> by_cases h2 : s = rs <;> by_cases h3 : s = wk <;> simp_all

theorem krkBoard_sk {σ : Colour} {sk rs wk : Square} :
    krkBoard σ sk rs wk sk = some ⟨σ, .king⟩ := by
  simp [krkBoard]

theorem krkBoard_rs {σ : Colour} {sk rs wk : Square} (h : sk ≠ rs) :
    krkBoard σ sk rs wk rs = some ⟨σ, .rook⟩ := by
  have : ¬ rs = sk := fun e => h e.symm
  simp [krkBoard, this]

theorem krkBoard_wk {σ : Colour} {sk rs wk : Square} (h1 : sk ≠ wk) (h2 : rs ≠ wk) :
    krkBoard σ sk rs wk wk = some ⟨σ.opp, .king⟩ := by
  have e1 : ¬ wk = sk := fun e => h1 e.symm
  have e2 : ¬ wk = rs := fun e => h2 e.symm
  simp [krkBoard, e1, e2]

/-- The rook's attack on a K+R vs K board: a clear file or rank, where only the two kings
can block. -/
theorem rook_attacks_krk {σ : Colour} {sk rs wk : Square} (h12 : sk ≠ rs) (t : Square) :
    attacksFrom (krkBoard σ sk rs wk) ⟨σ, .rook⟩ rs t = true ↔ RookSees rs t sk wk := by
  simp only [attacksFrom, Bool.and_eq_true, lineGeom_iff, pathClear_iff, RookSees]
  constructor
  · rintro ⟨hl, hp⟩
    refine ⟨hl, fun hs => ?_, fun hw => ?_⟩
    · have := hp sk ((isBetween_iff_onSeg hl).2 hs)
      rw [krkBoard_sk] at this; cases this
    · have := hp wk ((isBetween_iff_onSeg hl).2 hw)
      rw [krkBoard_eq_none] at this
      exact this.2.2 rfl
  · rintro ⟨hl, hs, hw⟩
    refine ⟨hl, fun r hr => ?_⟩
    rw [isBetween_iff_onSeg hl] at hr
    refine krkBoard_eq_none.2 ⟨?_, ?_, ?_⟩
    · rintro rfl; exact hs hr
    · rintro rfl; exact not_onSeg_self _ _ hr
    · rintro rfl; exact hw hr

theorem attacked_krk {σ : Colour} {sk rs wk : Square} (h12 : sk ≠ rs) (h13 : sk ≠ wk)
    (h23 : rs ≠ wk) (t : Square) (c : Colour) :
    attacked (krkBoard σ sk rs wk) t c = true ↔
      (c = σ ∧ (dInf sk t = 1 ∨ RookSees rs t sk wk)) ∨ (c = σ.opp ∧ dInf wk t = 1) := by
  rw [attacked_iff]
  constructor
  · rintro ⟨s, pc, hb, hc, ha⟩
    rcases krkBoard_some hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨hc.symm, Or.inl (by simpa [attacksFrom, kingGeom_iff] using ha)⟩
    · exact Or.inl ⟨hc.symm, Or.inr ((rook_attacks_krk h12 t).1 ha)⟩
    · exact Or.inr ⟨hc.symm, by simpa [attacksFrom, kingGeom_iff] using ha⟩
  · rintro (⟨rfl, hk | hr⟩ | ⟨rfl, hk⟩)
    · exact ⟨sk, _, krkBoard_sk, rfl, by simpa [attacksFrom, kingGeom_iff] using hk⟩
    · exact ⟨rs, _, krkBoard_rs h12, rfl, (rook_attacks_krk h12 t).2 hr⟩
    · exact ⟨wk, _, krkBoard_wk h13 h23, rfl, by simpa [attacksFrom, kingGeom_iff] using hk⟩

theorem kingSq_krk {σ : Colour} {sk rs wk s : Square} {c : Colour} (h13 : sk ≠ wk)
    (h23 : rs ≠ wk) :
    krkBoard σ sk rs wk s = some ⟨c, .king⟩ ↔ (c = σ ∧ s = sk) ∨ (c = σ.opp ∧ s = wk) := by
  constructor
  · intro h
    rcases krkBoard_some h with ⟨e, he⟩ | ⟨_, he⟩ | ⟨e, he⟩
    · simp only [Piece.mk.injEq] at he; exact Or.inl ⟨he.1, e⟩
    · simp at he
    · simp only [Piece.mk.injEq] at he; exact Or.inr ⟨he.1, e⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact krkBoard_sk
    · exact krkBoard_wk h13 h23

/-- The lone king is in check iff the strong king is adjacent or the rook sees it. -/
theorem inCheck_weak_krk {q : Position} {σ : Colour} {sk rs wk : Square} (h12 : sk ≠ rs)
    (h13 : sk ≠ wk) (h23 : rs ≠ wk) (hb : q.board = krkBoard σ sk rs wk) :
    inCheck q σ.opp = true ↔ dInf sk wk = 1 ∨ RookSees rs wk sk wk := by
  rw [inCheck_iff, hb]
  constructor
  · rintro ⟨s, hs, hat⟩
    rcases (kingSq_krk h13 h23).1 hs with ⟨e, _⟩ | ⟨_, rfl⟩
    · exact absurd e.symm (opp_ne _)
    · rw [opp_opp] at hat
      rcases (attacked_krk h12 h13 h23 _ _).1 hat with ⟨_, h⟩ | ⟨e, _⟩
      · exact h
      · exact absurd e (opp_ne _)
  · intro h
    refine ⟨wk, (kingSq_krk h13 h23).2 (Or.inr ⟨rfl, rfl⟩), ?_⟩
    rw [opp_opp, attacked_krk h12 h13 h23]
    exact Or.inl ⟨rfl, h⟩

/-- The strong king is in check iff the lone king is adjacent (F2). -/
theorem inCheck_strong_krk {q : Position} {σ : Colour} {sk rs wk : Square} (h12 : sk ≠ rs)
    (h13 : sk ≠ wk) (h23 : rs ≠ wk) (hb : q.board = krkBoard σ sk rs wk) :
    inCheck q σ = true ↔ dInf wk sk = 1 := by
  rw [inCheck_iff, hb]
  constructor
  · rintro ⟨s, hs, hat⟩
    rcases (kingSq_krk h13 h23).1 hs with ⟨_, rfl⟩ | ⟨e, _⟩
    · rcases (attacked_krk h12 h13 h23 _ _).1 hat with ⟨e, _⟩ | ⟨_, hk⟩
      · exact absurd e.symm (opp_ne _)
      · exact hk
    · exact absurd e (opp_ne _)
  · intro h
    refine ⟨sk, (kingSq_krk h13 h23).2 (Or.inl ⟨rfl, rfl⟩), ?_⟩
    rw [attacked_krk h12 h13 h23]
    exact Or.inr ⟨rfl, h⟩

/-! ## The board after a simple move -/

/-- The board after a move that is not a pawn move, carries no promotion and, if it is a
king move, is a one-square step (so not castling): the piece arrives and its square
empties. -/
theorem play_board_simple {p : Position} {m : Move} {k : PieceType}
    (hb : p.board m.src = some ⟨p.turn, k⟩) (hnp : k ≠ .pawn) (hpro : m.promo = none)
    (hk : k = .king → dInf m.src m.dst = 1) :
    (play p m).board = fun s => if s = m.dst then some ⟨p.turn, k⟩
                                else if s = m.src then none else p.board s := by
  have hpawn : (some (⟨p.turn, k⟩ : Piece) == some ⟨p.turn, .pawn⟩) = false := by
    rw [Bool.eq_false_iff]; simpa using hnp
  have hcas : ¬ (k = .king ∧ m.src = ((4 : Fin 8), homeRank p.turn) ∧
        m.dst = ((6 : Fin 8), homeRank p.turn)) ∧
      ¬ (k = .king ∧ m.src = ((4 : Fin 8), homeRank p.turn) ∧
        m.dst = ((2 : Fin 8), homeRank p.turn)) := by
    constructor
    · rintro ⟨hkk, hs, hd⟩; exact (not_castle_of_step (c := p.turn) (hk hkk)).1 ⟨hs, hd⟩
    · rintro ⟨hkk, hs, hd⟩; exact (not_castle_of_step (c := p.turn) (hk hkk)).2 ⟨hs, hd⟩
  funext s
  simp only [play, hb, hpro, hpawn, Bool.false_and, Bool.false_eq_true, ite_false,
    beq_iff_eq, Option.some.injEq, Piece.mk.injEq, true_and, Bool.and_eq_true]
  by_cases h1 : s = m.dst
  · simp [h1]
  · by_cases h2 : s = m.src
    · simp [h2]
    · simp only [h1, h2, ite_false]
      by_cases hkk : k = .king
      · have hn1 : ¬ (m.src = ((4 : Fin 8), homeRank p.turn) ∧
            m.dst = ((6 : Fin 8), homeRank p.turn)) := fun hh => hcas.1 ⟨hkk, hh.1, hh.2⟩
        have hn2 : ¬ (m.src = ((4 : Fin 8), homeRank p.turn) ∧
            m.dst = ((2 : Fin 8), homeRank p.turn)) := fun hh => hcas.2 ⟨hkk, hh.1, hh.2⟩
        subst hkk
        simp [hn1, hn2]
      · simp [hkk]

theorem legal_of_pseudo {q : Position} {m : Move} (hp : isPseudo q m = true)
    (hc : inCheck (play q m) q.turn = false) : Legal q (play q m) :=
  ⟨m, by simp [isLegal, hp, hc], rfl⟩

/-! ## The KRK move model -/

/-- A K+R vs K configuration: strong king, rook, lone king, and whether the strong side
is to move. The colour `σ` of the strong side is supplied separately (`Matches`). -/
structure KRKState where
  sk : Square
  rs : Square
  wk : Square
  strong : Bool
  deriving DecidableEq, Repr

/-- The moves the route uses, by their geometric legality conditions:
- `rook`: along a clear file or rank, onto an empty square (the strong king is safe since
  the kings are apart);
- `king`: a strong-king step onto an empty square not adjacent to the lone king;
- `lone`: a non-capturing lone-king step onto a square attacked neither by the strong king
  nor by the rook (evaluated on the board after the move). -/
inductive StepM : KRKState → KRKState → Prop
  | rook {sk rs wk t : Square} : RookLine rs t → ¬ OnSeg rs sk t → ¬ OnSeg rs wk t →
      t ≠ sk → t ≠ wk → 2 ≤ dInf sk wk → StepM ⟨sk, rs, wk, true⟩ ⟨sk, t, wk, false⟩
  | king {sk rs wk t : Square} : dInf sk t = 1 → t ≠ rs → 2 ≤ dInf t wk →
      StepM ⟨sk, rs, wk, true⟩ ⟨t, rs, wk, false⟩
  | lone {sk rs wk t : Square} : dInf wk t = 1 → t ≠ rs → 2 ≤ dInf sk t →
      ¬ RookSees rs t sk t → StepM ⟨sk, rs, wk, false⟩ ⟨sk, rs, t, true⟩

/-- Model checkmate: the lone king is to move and the rook gives check; every neighbour of
the lone king is adjacent to the strong king, or is a non-rook square seen by the rook once
the lone king stands on it. (A capture of the rook is excluded by the first alternative:
the rook is then protected.) -/
def MateM (a : KRKState) : Prop :=
  a.strong = false ∧ RookSees a.rs a.wk a.sk a.wk ∧
    ∀ t, dInf a.wk t = 1 → dInf a.sk t ≤ 1 ∨ (t ≠ a.rs ∧ RookSees a.rs t a.sk t)

/-- A model checkmate is reachable by model moves. -/
def WinM (a : KRKState) : Prop := ∃ b, Chain StepM a b ∧ MateM b

/-- The kernel position `q` is the K+R vs K configuration `a` with strong colour `σ`
(any castling rights and en-passant target). -/
def Matches (q : Position) (σ : Colour) (a : KRKState) : Prop :=
  IsKRK q σ a.sk a.rs a.wk ∧ q.turn = (if a.strong then σ else σ.opp)

theorem winM_of_mate {a : KRKState} (h : MateM a) : WinM a := ⟨a, Chain.refl a, h⟩

theorem winM_of_step {a b : KRKState} (hs : StepM a b) (hw : WinM b) : WinM a := by
  obtain ⟨c, hc, hm⟩ := hw
  refine ⟨c, ?_, hm⟩
  clear hm
  induction hc with
  | refl => exact Chain.tail (Chain.refl _) hs
  | tail _ h ih => exact Chain.tail ih h

theorem ne_of_rookLine {s t : Square} (h : RookLine s t) : t ≠ s := by
  intro e; subst e; exact h.1 ⟨rfl, rfl⟩

theorem ne_of_dInf_pos {s t : Square} (h : 1 ≤ dInf s t) : s ≠ t := by
  intro e; subst e; rw [(dInf_eq_zero_iff).2 rfl] at h; omega

/-! ## Soundness of the model for the kernel -/

/-- Each model move is a kernel-legal move, whatever the castling rights and en-passant
target of the kernel position. -/
theorem step_sound {q : Position} {σ : Colour} {a b : KRKState} (hq : Matches q σ a)
    (hs : StepM a b) : ∃ q', Legal q q' ∧ Matches q' σ b := by
  obtain ⟨⟨h12, h13, h23, hb⟩, ht⟩ := hq
  cases hs with
  | @rook sk rs wk t hl hs hw hts htw hfar =>
    simp only [ite_true] at ht h12 h13 h23 hb
    let m : Move := ⟨rs, t, none⟩
    have hsrc : q.board m.src = some ⟨q.turn, .rook⟩ := by
      rw [hb, ht]; exact krkBoard_rs h12
    have htr : t ≠ rs := ne_of_rookLine hl
    have hdst : q.board m.dst = none := by rw [hb]; exact krkBoard_eq_none.2 ⟨hts, htr, htw⟩
    have hatt : attacksFrom q.board ⟨q.turn, .rook⟩ m.src m.dst = true := by
      rw [hb, ht]; exact (rook_attacks_krk h12 t).2 ⟨hl, hs, hw⟩
    have hp : isPseudo q m = true := by
      unfold isPseudo; rw [hsrc]; simp [targetOK, hdst, hatt, m]
    have hb' : (play q m).board = krkBoard σ sk t wk := by
      rw [play_board_simple hsrc (by decide) rfl (by intro h; cases h)]
      funext x
      show (if x = t then some ⟨q.turn, .rook⟩ else if x = rs then none else q.board x) = _
      rw [hb, ht]; unfold krkBoard
      by_cases e1 : x = t
      · subst e1; simp [hts]
      · by_cases e2 : x = rs
        · subst e2; simp [e1, Ne.symm h12, h23]
        · simp [e1, e2]
    have hc : inCheck (play q m) q.turn = false := by
      rw [ht]
      cases h : inCheck (play q m) σ
      · rfl
      · have := (inCheck_strong_krk (Ne.symm hts) h13 htw hb').1 h
        rw [dInf_comm] at this; omega
    exact ⟨play q m, legal_of_pseudo hp hc,
      ⟨Ne.symm hts, h13, htw, hb'⟩, by rw [play_turn, ht]; rfl⟩
  | @king sk rs wk t hd htr hfar =>
    simp only [ite_true] at ht h12 h13 h23 hb
    let m : Move := ⟨sk, t, none⟩
    have hsrc : q.board m.src = some ⟨q.turn, .king⟩ := by
      rw [hb, ht]; exact krkBoard_sk
    have hts : t ≠ sk := Ne.symm (ne_of_dInf_pos (s := sk) (t := t) (by omega))
    have htw : t ≠ wk := ne_of_dInf_pos (s := t) (t := wk) (by omega)
    have hdst : q.board m.dst = none := by rw [hb]; exact krkBoard_eq_none.2 ⟨hts, htr, htw⟩
    have hp : isPseudo q m = true := by
      rw [isPseudo_of_king hsrc]
      have hg : kingGeom sk t = true := kingGeom_iff.2 hd
      simp [targetOK, hdst, hg, m]
    have hb' : (play q m).board = krkBoard σ t rs wk := by
      rw [play_board_simple hsrc (by decide) rfl (fun _ => hd)]
      funext x
      show (if x = t then some ⟨q.turn, .king⟩ else if x = sk then none else q.board x) = _
      rw [hb, ht]; unfold krkBoard
      by_cases e1 : x = t
      · subst e1; simp
      · by_cases e2 : x = sk
        · subst e2; simp [e1, h12, h13]
        · simp [e1, e2]
    have hc : inCheck (play q m) q.turn = false := by
      rw [ht]
      cases h : inCheck (play q m) σ
      · rfl
      · have := (inCheck_strong_krk htr htw h23 hb').1 h
        rw [dInf_comm] at this; omega
    exact ⟨play q m, legal_of_pseudo hp hc, ⟨htr, htw, h23, hb'⟩, by rw [play_turn, ht]; rfl⟩
  | @lone sk rs wk t hd htr hfar hsee =>
    simp only [Bool.false_eq_true, ite_false] at ht h12 h13 h23 hb
    let m : Move := ⟨wk, t, none⟩
    have hsrc : q.board m.src = some ⟨q.turn, .king⟩ := by
      rw [hb, ht]; exact krkBoard_wk h13 h23
    have hts : t ≠ sk := Ne.symm (ne_of_dInf_pos (s := sk) (t := t) (by omega))
    have htw : t ≠ wk := Ne.symm (ne_of_dInf_pos (s := wk) (t := t) (by omega))
    have hdst : q.board m.dst = none := by rw [hb]; exact krkBoard_eq_none.2 ⟨hts, htr, htw⟩
    have hp : isPseudo q m = true := by
      rw [isPseudo_of_king hsrc]
      have hg : kingGeom wk t = true := kingGeom_iff.2 hd
      simp [targetOK, hdst, hg, m]
    have hb' : (play q m).board = krkBoard σ sk rs t := by
      rw [play_board_simple hsrc (by decide) rfl (fun _ => hd)]
      funext x
      show (if x = t then some ⟨q.turn, .king⟩ else if x = wk then none else q.board x) = _
      rw [hb, ht]; unfold krkBoard
      by_cases e1 : x = t
      · subst e1; simp [hts, htr]
      · by_cases e2 : x = wk
        · subst e2; simp [e1, Ne.symm h13, Ne.symm h23]
        · simp [e1, e2]
    have hc : inCheck (play q m) q.turn = false := by
      rw [ht]
      cases h : inCheck (play q m) σ.opp
      · rfl
      · rcases (inCheck_weak_krk h12 (Ne.symm hts) (Ne.symm htr) hb').1 h with e | e
        · omega
        · exact absurd e hsee
    exact ⟨play q m, legal_of_pseudo hp hc, ⟨h12, Ne.symm hts, Ne.symm htr, hb'⟩,
      by rw [play_turn, ht, opp_opp]; rfl⟩

/-- A model checkmate is a kernel checkmate: the lone king is in check, and every kernel
move of it (including a capture of the rook) leaves it in check. -/
theorem mate_sound {q : Position} {σ : Colour} {a : KRKState} (hq : Matches q σ a)
    (hm : MateM a) : MatedK q := by
  obtain ⟨⟨h12, h13, h23, hb⟩, ht⟩ := hq
  obtain ⟨hst, hsee, hall⟩ := hm
  rw [hst] at ht
  simp only [Bool.false_eq_true, ite_false] at ht
  refine ⟨?_, ?_⟩
  · rw [ht]; exact (inCheck_weak_krk h12 h13 h23 hb).2 (Or.inr hsee)
  · rintro ⟨q', m, hm, rfl⟩
    have hp : isPseudo q m = true := by
      unfold isLegal at hm; simp only [Bool.and_eq_true] at hm; exact hm.1
    have hchk := not_inCheck_after_legal hm
    obtain ⟨pc, hpc, hcol⟩ := own_of_isPseudo hp
    rw [hb] at hpc
    rcases krkBoard_some hpc with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨esrc, rfl⟩
    · rw [ht] at hcol; exact opp_ne _ hcol
    · rw [ht] at hcol; exact opp_ne _ hcol
    · have hsrc : q.board m.src = some ⟨q.turn, .king⟩ := by
        rw [hb, ht, esrc]; exact krkBoard_wk h13 h23
      have hnc : canCastle q m = false := by
        apply canCastle_false_of_noRook
        intro s hs
        rw [hb, ht] at hs
        rcases krkBoard_some hs with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩
        · simp at h
        · simp only [Piece.mk.injEq] at h; exact opp_ne _ h.1.symm
        · simp at h
      rw [isPseudo_of_king hsrc, hnc] at hp
      simp only [Bool.or_false, Bool.and_eq_true, Option.isNone_iff_eq_none] at hp
      obtain ⟨htg, hpro, hg⟩ := hp
      have hd : dInf m.src m.dst = 1 := kingGeom_iff.1 hg
      rw [esrc] at hd
      have hdk : m.dst ≠ a.sk := by
        intro e
        have := (targetOK_some htg (by rw [hb, e]; exact krkBoard_sk)).2
        exact this rfl
      have hdw : m.dst ≠ a.wk := Ne.symm (ne_of_dInf_pos (s := a.wk) (t := m.dst) (by omega))
      have hbp := play_board_simple hsrc (by decide) hpro (fun _ => by rw [esrc]; exact hd)
      rw [ht] at hchk
      by_cases hcap : m.dst = a.rs
      · -- capture of the rook: the strong king is adjacent and gives check
        rcases hall m.dst hd with hk | ⟨hne, _⟩
        · have hk1 : dInf a.sk m.dst = 1 := by
            have := ne_of_dInf_pos (s := a.sk) (t := m.dst)
            have h0 : dInf a.sk m.dst ≠ 0 := fun h0 => hdk (dInf_eq_zero_iff.1 h0).symm
            omega
          have : inCheck (play q m) σ.opp = true := by
            rw [inCheck_iff]
            refine ⟨m.dst, by rw [hbp, ht]; simp, ?_⟩
            rw [attacked_iff, opp_opp]
            refine ⟨a.sk, ⟨σ, .king⟩, ?_, rfl, by simpa [attacksFrom, kingGeom_iff] using hk1⟩
            rw [hbp, hb, ht, esrc]
            simp [Ne.symm hdk, h13, krkBoard_sk]
          rw [this] at hchk; cases hchk
        · exact absurd hcap hne
      · have hb' : (play q m).board = krkBoard σ a.sk a.rs m.dst := by
          rw [hbp]
          funext x
          rw [hb, ht, esrc]; unfold krkBoard
          by_cases e1 : x = m.dst
          · subst e1; simp [hdk, hcap]
          · by_cases e2 : x = a.wk
            · subst e2; simp [e1, Ne.symm h13, Ne.symm h23]
            · simp [e1, e2]
        have : inCheck (play q m) σ.opp = true := by
          rw [inCheck_weak_krk h12 (Ne.symm hdk) (Ne.symm hcap) hb']
          rcases hall m.dst hd with hk | ⟨_, hs⟩
          · left
            have h0 : dInf a.sk m.dst ≠ 0 := fun h0 => hdk (dInf_eq_zero_iff.1 h0).symm
            omega
          · exact Or.inr hs
        rw [this] at hchk; cases hchk

/-- Model moves give a kernel series of legal moves. -/
theorem chain_sound {σ : Colour} {a b : KRKState} (hc : Chain StepM a b) :
    ∀ q, Matches q σ a → ∃ q', ReachK q q' ∧ Matches q' σ b := by
  induction hc with
  | refl => intro q hq; exact ⟨q, ReachK.refl q, hq⟩
  | tail _ hs ih =>
    intro q hq
    obtain ⟨q1, hr, hq1⟩ := ih q hq
    obtain ⟨q2, hl, hq2⟩ := step_sound hq1 hs
    exact ⟨q2, ReachK.tail hr hl, hq2⟩

/-- **Soundness.** A reachable model checkmate makes the kernel position not dead. -/
theorem not_deadK_of_winM {q : Position} {σ : Colour} {a : KRKState} (hq : Matches q σ a)
    (hw : WinM a) : ¬ DeadK q := by
  obtain ⟨b, hc, hm⟩ := hw
  obtain ⟨q', hr, hq'⟩ := chain_sound hc q hq
  exact fun hd => hd ⟨q', hr, mate_sound hq' hm⟩

/-! ## F4: reflections of the board -/

/-- A symmetry of the board preserving king distance and rook geometry; an involution. -/
structure BoardSym where
  f : Square → Square
  invol : ∀ s, f (f s) = s
  dInf_eq : ∀ s t, dInf (f s) (f t) = dInf s t
  line_iff : ∀ s t, RookLine (f s) (f t) ↔ RookLine s t
  seg_iff : ∀ s r t, OnSeg (f s) (f r) (f t) ↔ OnSeg s r t

theorem BoardSym.ne_iff (g : BoardSym) {s t : Square} : g.f s ≠ g.f t ↔ s ≠ t := by
  constructor
  · intro h e; exact h (by rw [e])
  · intro h e; exact h (by rw [← g.invol s, e, g.invol])

theorem BoardSym.sees_iff (g : BoardSym) (rs t a b : Square) :
    RookSees (g.f rs) (g.f t) (g.f a) (g.f b) ↔ RookSees rs t a b := by
  simp only [RookSees, g.line_iff, g.seg_iff]

def KRKState.map (g : BoardSym) (a : KRKState) : KRKState :=
  ⟨g.f a.sk, g.f a.rs, g.f a.wk, a.strong⟩

theorem KRKState.map_map (g : BoardSym) (a : KRKState) : (a.map g).map g = a := by
  simp [KRKState.map, g.invol]

theorem step_map (g : BoardSym) {a b : KRKState} (h : StepM a b) :
    StepM (a.map g) (b.map g) := by
  cases h with
  | rook hl hs hw hts htw hfar =>
    exact StepM.rook ((g.line_iff _ _).2 hl) (by rwa [g.seg_iff]) (by rwa [g.seg_iff])
      ((g.ne_iff).2 hts) ((g.ne_iff).2 htw) (by rwa [g.dInf_eq])
  | king hd htr hfar =>
    exact StepM.king (by rwa [g.dInf_eq]) ((g.ne_iff).2 htr) (by rwa [g.dInf_eq])
  | lone hd htr hfar hsee =>
    exact StepM.lone (by rwa [g.dInf_eq]) ((g.ne_iff).2 htr) (by rwa [g.dInf_eq])
      (by rwa [g.sees_iff])

theorem mate_map (g : BoardSym) {a : KRKState} (h : MateM a) : MateM (a.map g) := by
  obtain ⟨hst, hsee, hall⟩ := h
  refine ⟨hst, (g.sees_iff _ _ _ _).2 hsee, fun t ht => ?_⟩
  have ht' : dInf a.wk (g.f t) = 1 := by
    rw [← g.dInf_eq, g.invol]; exact ht
  rcases hall (g.f t) ht' with hk | ⟨hne, hs⟩
  · left; simp only [KRKState.map]; rw [← g.invol t, g.dInf_eq]; exact hk
  · right
    simp only [KRKState.map]
    rw [← g.invol t]
    exact ⟨(g.ne_iff).2 hne, (g.sees_iff _ _ _ _).2 hs⟩

theorem winM_map (g : BoardSym) {a : KRKState} (h : WinM a) : WinM (a.map g) := by
  obtain ⟨b, hc, hm⟩ := h
  refine ⟨b.map g, ?_, mate_map g hm⟩
  clear hm
  induction hc with
  | refl => exact Chain.refl _
  | tail _ hs ih => exact Chain.tail ih (step_map g hs)

/-- **F4.** It suffices to reach a model mate from a reflected configuration. -/
theorem winM_of_sym (g : BoardSym) {a : KRKState} (h : WinM (a.map g)) : WinM a := by
  have := winM_map g h
  rwa [KRKState.map_map] at this

def symId : BoardSym where
  f s := s
  invol _ := rfl
  dInf_eq _ _ := rfl
  line_iff _ _ := Iff.rfl
  seg_iff _ _ _ := Iff.rfl

/-- Reflection in the files: `x ↦ 7 − x`. -/
def symX : BoardSym where
  f s := ((⟨7 - s.1.val, by omega⟩ : Fin 8), s.2)
  invol s := by rw [square_eq_iff]; dsimp only; omega
  dInf_eq s t := by simp only [dInf, absDiff]; omega
  line_iff s t := by simp only [RookLine]; omega
  seg_iff s r t := by simp only [OnSeg]; omega

/-- Reflection in the ranks: `y ↦ 7 − y`. -/
def symY : BoardSym where
  f s := (s.1, (⟨7 - s.2.val, by omega⟩ : Fin 8))
  invol s := by rw [square_eq_iff]; dsimp only; omega
  dInf_eq s t := by simp only [dInf, absDiff]; omega
  line_iff s t := by simp only [RookLine]; omega
  seg_iff s r t := by simp only [OnSeg]; omega

/-- Both reflections. -/
def symXY : BoardSym where
  f s := (⟨7 - s.1.val, by omega⟩, ⟨7 - s.2.val, by omega⟩)
  invol s := by rw [square_eq_iff]; dsimp only; omega
  dInf_eq s t := by simp only [dInf, absDiff]; omega
  line_iff s t := by simp only [RookLine]; omega
  seg_iff s r t := by simp only [OnSeg]; omega

/-- The strong king is normalised: on files a–d and ranks 3–8 (`sx ≤ 3`, `sy ≥ 2`). -/
def Normal (s : Square) : Prop := s.1.val ≤ 3 ∧ 2 ≤ s.2.val

/-- **F4 normalisation.** Some reflection puts any square into the normal frame. -/
theorem exists_sym_normal (s : Square) : ∃ g : BoardSym, Normal (g.f s) := by
  by_cases hx : s.1.val ≤ 3 <;> by_cases hy : 2 ≤ s.2.val
  · exact ⟨symId, hx, hy⟩
  · exact ⟨symY, hx, by simp only [symY]; omega⟩
  · exact ⟨symX, by simp only [symX]; omega, hy⟩
  · exact ⟨symXY, by simp only [symXY]; omega, by simp only [symXY]; omega⟩

end EndgameChess.Rules
