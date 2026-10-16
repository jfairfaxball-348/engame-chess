import EndgameChess.Rules.AgreeKK
import EndgameChess.KBK

/-!
# Rules kernel K2 — K+B vs K agreement (closes gap G1 for EC-T0002)

Embeds the frozen EC-T0002 model (`EndgameChess.KBK`) into the general kernel and proves:
- `isBetween_iff_between`: on a diagonal, the kernel's "strictly between" (collinearity
  by products + additivity of `dInf`) equals KBK's `between`;
- `bishop_kbk`: kernel bishop attack on a K+B vs K board equals `KBK.bishopAttacks`;
- `legal_ofKBK_iff`: from an embedded `LKBK` configuration, the kernel's legal successors
  are exactly the embeddings of the `KBK.Step` successors (including the capture of the
  bishop, which leaves K vs K);
- `deadK_embPos_iff` / `deadK_ofKBK_iff`: kernel-dead ⇔ `KBK.Dead`;
- `kernel_dead_KBK`: every `LKBK` configuration is dead in the kernel.

`KBK.lean` and `KK.lean` are imported, not edited.
-/

namespace EndgameChess.Rules

open EndgameChess.KK

/-! ## Geometry: diagonals and betweenness -/

theorem diagGeom_iff_onDiag {s t : Square} : diagGeom s t = true ↔ KBK.onDiag s t := by
  unfold diagGeom KBK.onDiag dx dy
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq]
  unfold absDiff
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩

/-- On a diagonal, the kernel's `isBetween` coincides with KBK's `between`. -/
theorem isBetween_iff_between {X r t : Square} (hd : KBK.onDiag X t) :
    isBetween X r t = true ↔ KBK.between X r t := by
  obtain ⟨hXt, hdd⟩ := hd
  unfold isBetween KBK.between KBK.onDiag
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, dx, dy]
  rw [Ne, square_eq_iff] at hXt
  simp only [square_eq_iff]
  simp only [dInf, absDiff] at hdd ⊢
  rcases (show ((t.2.val : Int) - X.2.val) = ((t.1.val : Int) - X.1.val) ∨
      ((t.2.val : Int) - X.2.val) = -((t.1.val : Int) - X.1.val) by omega) with he | he
  · have hd0 : ((t.1.val : Int) - X.1.val) ≠ 0 := by omega
    rw [he, show ∀ a b : Int, a * ((t.1.val : Int) - X.1.val) = b * ((t.1.val : Int) - X.1.val) ↔ a = b
      from fun a b => ⟨Int.eq_of_mul_eq_mul_right hd0, fun h => by rw [h]⟩]
    omega
  · have hd0 : ((t.1.val : Int) - X.1.val) ≠ 0 := by omega
    rw [he, Int.mul_neg, ← Int.neg_mul,
      show ∀ a b : Int, -a * ((t.1.val : Int) - X.1.val) = b * ((t.1.val : Int) - X.1.val) ↔ -a = b
      from fun a b => ⟨Int.eq_of_mul_eq_mul_right hd0, fun h => by rw [h]⟩]
    omega

/-! ## The embedding -/

def sideColour (σ : Colour) : KBK.Side → Colour
  | .strong => σ
  | .weak => σ.opp

def kbkBoard (σ : Colour) (sk bs wk : Square) : Board := fun s =>
  if s = sk then some ⟨σ, .king⟩
  else if s = bs then some ⟨σ, .bishop⟩
  else if s = wk then some ⟨σ.opp, .king⟩
  else none

/-- Embedding of a K+B vs K configuration: the strong side's colour is `strongColour`.
There are no castling rights (no rooks) and no en-passant target (no pawns). -/
def ofKBK (p : KBK.KBKState) : Position :=
  { board := kbkBoard p.strongColour p.sk p.bs p.wk,
    turn := sideColour p.strongColour p.turn, castling := noRights, ep := none }

def embPos : KBK.Pos → Position
  | .kbk p => ofKBK p
  | .kk a => ofKK a

theorem opp_ne (c : Colour) : c ≠ c.opp := by cases c <;> simp [Colour.opp]
theorem opp_opp (c : Colour) : c.opp.opp = c := by cases c <;> rfl

theorem kbkBoard_some {σ : Colour} {sk bs wk s : Square} {pc : Piece}
    (h : kbkBoard σ sk bs wk s = some pc) :
    (s = sk ∧ pc = ⟨σ, .king⟩) ∨ (s = bs ∧ pc = ⟨σ, .bishop⟩) ∨ (s = wk ∧ pc = ⟨σ.opp, .king⟩) := by
  unfold kbkBoard at h
  by_cases h1 : s = sk
  · subst h1; simp at h; exact Or.inl ⟨rfl, h.symm⟩
  · by_cases h2 : s = bs
    · subst h2; simp [h1] at h; exact Or.inr (Or.inl ⟨rfl, h.symm⟩)
    · by_cases h3 : s = wk
      · subst h3; simp [h1, h2] at h; exact Or.inr (Or.inr ⟨rfl, h.symm⟩)
      · simp [h1, h2, h3] at h

theorem kbkBoard_eq_none {σ : Colour} {sk bs wk s : Square} :
    kbkBoard σ sk bs wk s = none ↔ s ≠ sk ∧ s ≠ bs ∧ s ≠ wk := by
  unfold kbkBoard
  by_cases h1 : s = sk <;> by_cases h2 : s = bs <;> by_cases h3 : s = wk <;> simp_all

theorem kbkBoard_sk {σ : Colour} {sk bs wk : Square} : kbkBoard σ sk bs wk sk = some ⟨σ, .king⟩ := by
  simp [kbkBoard]

theorem kbkBoard_bs {σ : Colour} {sk bs wk : Square} (h : sk ≠ bs) :
    kbkBoard σ sk bs wk bs = some ⟨σ, .bishop⟩ := by
  have : ¬ bs = sk := fun e => h e.symm
  simp [kbkBoard, this]

theorem kbkBoard_wk {σ : Colour} {sk bs wk : Square} (h1 : sk ≠ wk) (h2 : bs ≠ wk) :
    kbkBoard σ sk bs wk wk = some ⟨σ.opp, .king⟩ := by
  have e1 : ¬ wk = sk := fun e => h1 e.symm
  have e2 : ¬ wk = bs := fun e => h2 e.symm
  simp [kbkBoard, e1, e2]

theorem pathClear_kbk {σ : Colour} {sk bs wk X t : Square} :
    pathClear (kbkBoard σ sk bs wk) X t = true ↔
      ∀ r, isBetween X r t = true → r ≠ sk ∧ r ≠ bs ∧ r ≠ wk := by
  unfold pathClear
  rw [all_allSquares]
  constructor
  · intro h r hb
    have := h r
    simp only [hb, Bool.not_true, Bool.false_or, Option.isNone_iff_eq_none] at this
    exact kbkBoard_eq_none.1 this
  · intro h r
    cases hb : isBetween X r t
    · simp
    · simp only [Bool.not_true, Bool.false_or, Option.isNone_iff_eq_none]
      exact kbkBoard_eq_none.2 (h r hb)

/-- Kernel bishop attack on a K+B vs K board is KBK's `bishopAttacks` with the kings as
blockers. -/
theorem bishop_kbk {σ : Colour} {sk bs wk t : Square} :
    (diagGeom bs t = true ∧ pathClear (kbkBoard σ sk bs wk) bs t = true) ↔
      KBK.bishopAttacks (KBK.kingsOcc sk wk) bs t := by
  rw [diagGeom_iff_onDiag, pathClear_kbk]
  constructor
  · rintro ⟨hod, hp⟩
    refine ⟨hod, fun r hbet hocc => ?_⟩
    obtain ⟨h1, _, h3⟩ := hp r ((isBetween_iff_between hod).2 hbet)
    rcases hocc with e | e
    · exact h1 e
    · exact h3 e
  · rintro ⟨hod, hb⟩
    refine ⟨hod, fun r hib => ?_⟩
    have hbet := (isBetween_iff_between hod).1 hib
    have hn := hb r hbet
    refine ⟨fun e => hn (Or.inl e), fun e => hbet.1.1 e.symm, fun e => hn (Or.inr e)⟩

/-- Attack on a K+B vs K board. -/
theorem attacked_kbk {σ : Colour} {sk bs wk : Square} (h12 : sk ≠ bs) (h13 : sk ≠ wk)
    (h23 : bs ≠ wk) (t : Square) (c : Colour) :
    attacked (kbkBoard σ sk bs wk) t c = true ↔
      (c = σ ∧ (dInf sk t = 1 ∨ KBK.bishopAttacks (KBK.kingsOcc sk wk) bs t)) ∨
      (c = σ.opp ∧ dInf wk t = 1) := by
  rw [attacked_iff, ← bishop_kbk (σ := σ)]
  constructor
  · rintro ⟨s, pc, hb, hc, ha⟩
    rcases kbkBoard_some hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨hc.symm, Or.inl (by simpa [attacksFrom, kingGeom_iff] using ha)⟩
    · refine Or.inl ⟨hc.symm, Or.inr ?_⟩
      simpa [attacksFrom] using ha
    · exact Or.inr ⟨hc.symm, by simpa [attacksFrom, kingGeom_iff] using ha⟩
  · rintro (⟨rfl, hk | hb⟩ | ⟨rfl, hk⟩)
    · exact ⟨sk, _, kbkBoard_sk, rfl, by simpa [attacksFrom, kingGeom_iff] using hk⟩
    · exact ⟨bs, _, kbkBoard_bs h12, rfl, by simpa [attacksFrom] using hb⟩
    · exact ⟨wk, _, kbkBoard_wk h13 h23, rfl, by simpa [attacksFrom, kingGeom_iff] using hk⟩

def Distinct (p : KBK.KBKState) : Prop := p.sk ≠ p.bs ∧ p.sk ≠ p.wk ∧ p.bs ≠ p.wk

theorem kingSq_kbk {p : KBK.KBKState} (hd : Distinct p) {s : Square} {c : Colour} :
    (ofKBK p).board s = some ⟨c, .king⟩ ↔
      (c = p.strongColour ∧ s = p.sk) ∨ (c = p.strongColour.opp ∧ s = p.wk) := by
  obtain ⟨h12, h13, h23⟩ := hd
  constructor
  · intro h
    rcases kbkBoard_some h with ⟨e, he⟩ | ⟨_, he⟩ | ⟨e, he⟩
    · simp only [Piece.mk.injEq] at he; exact Or.inl ⟨he.1, e⟩
    · simp at he
    · simp only [Piece.mk.injEq] at he; exact Or.inr ⟨he.1, e⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact kbkBoard_sk
    · exact kbkBoard_wk h13 h23

/-- Kernel check of the weak king = `KBK.weakInCheck`. -/
theorem inCheck_weak {p : KBK.KBKState} (hd : Distinct p) :
    inCheck (ofKBK p) p.strongColour.opp = true ↔ KBK.weakInCheck p := by
  obtain ⟨h12, h13, h23⟩ := hd
  rw [inCheck_iff]
  constructor
  · rintro ⟨s, hs, hat⟩
    rcases (kingSq_kbk ⟨h12, h13, h23⟩).1 hs with ⟨e, _⟩ | ⟨_, rfl⟩
    · exact absurd e.symm (opp_ne _)
    · rw [opp_opp] at hat
      rcases (attacked_kbk h12 h13 h23 _ _).1 hat with ⟨_, hk | hb⟩ | ⟨e, _⟩
      · exact Or.inl ((attack_iff_dInf_one _ _).2 hk)
      · exact Or.inr hb
      · exact absurd e (opp_ne _)
  · intro h
    refine ⟨p.wk, (kingSq_kbk ⟨h12, h13, h23⟩).2 (Or.inr ⟨rfl, rfl⟩), ?_⟩
    simp only [ofKBK]
    rw [opp_opp, attacked_kbk h12 h13 h23]
    rcases h with hk | hb
    · exact Or.inl ⟨rfl, Or.inl ((attack_iff_dInf_one _ _).1 hk)⟩
    · exact Or.inl ⟨rfl, Or.inr hb⟩

/-- Kernel check of the strong king = `KBK.strongInCheck`. -/
theorem inCheck_strong {p : KBK.KBKState} (hd : Distinct p) :
    inCheck (ofKBK p) p.strongColour = true ↔ KBK.strongInCheck p := by
  obtain ⟨h12, h13, h23⟩ := hd
  rw [inCheck_iff]
  unfold KBK.strongInCheck
  constructor
  · rintro ⟨s, hs, hat⟩
    rcases (kingSq_kbk ⟨h12, h13, h23⟩).1 hs with ⟨_, rfl⟩ | ⟨e, _⟩
    · rcases (attacked_kbk h12 h13 h23 _ _).1 hat with ⟨e, _⟩ | ⟨_, hk⟩
      · exact absurd e.symm (opp_ne _)
      · exact (attack_iff_dInf_one _ _).2 hk
    · exact absurd e (opp_ne _)
  · intro h
    refine ⟨p.sk, (kingSq_kbk ⟨h12, h13, h23⟩).2 (Or.inl ⟨rfl, rfl⟩), ?_⟩
    simp only [ofKBK]
    rw [attacked_kbk h12 h13 h23]
    exact Or.inr ⟨rfl, (attack_iff_dInf_one _ _).1 h⟩

theorem inCheck_side {p : KBK.KBKState} (hd : Distinct p) (sd : KBK.Side) :
    inCheck (ofKBK p) (sideColour p.strongColour sd) = true ↔ p.inCheck sd := by
  cases sd
  · exact inCheck_strong hd
  · exact inCheck_weak hd

/-! ## `play` on embedded positions -/

/-- The board after a (non-pawn, non-king) piece move without promotion. -/
theorem play_bishopStep {p : Position} {m : Move}
    (hsrc : p.board m.src = some ⟨p.turn, .bishop⟩) (hpro : m.promo = none) :
    play p m = { board := fun s => if s = m.dst then some ⟨p.turn, .bishop⟩
                                   else if s = m.src then none else p.board s,
                 turn := p.turn.opp,
                 castling := updateCastling p.castling p.turn false m.src m.dst,
                 ep := none } := by
  apply Position.ext'
  · intro s
    simp only [play, hsrc, hpro, beq_iff_eq, Option.some.injEq, Piece.mk.injEq,
      reduceCtorEq, Bool.and_eq_true]
    by_cases h1 : s = m.dst
    · simp [h1]
    · by_cases h2 : s = m.src
      · subst h2; simp [h1]
      · simp [h1, h2]
  · rfl
  · have hbk : ((⟨p.turn, .bishop⟩ : Piece) == ⟨p.turn, .king⟩) = false := by
      rw [Bool.eq_false_iff]; simp
    simp [play, hsrc, hbk]
  · simp [play, hsrc]

theorem isPseudo_of_bishop {p : Position} {m : Move}
    (hsrc : p.board m.src = some ⟨p.turn, .bishop⟩) :
    isPseudo p m = (targetOK p m.dst &&
      (m.promo.isNone && attacksFrom p.board ⟨p.turn, .bishop⟩ m.src m.dst)) := by
  unfold isPseudo
  rw [hsrc]
  simp

theorem no_rook_kbk (p : KBK.KBKState) (s : Square) :
    (ofKBK p).board s ≠ some ⟨(ofKBK p).turn, .rook⟩ := by
  intro h
  rcases kbkBoard_some h with ⟨_, he⟩ | ⟨_, he⟩ | ⟨_, he⟩ <;> simp at he

theorem distinct_of_LKBK {p : KBK.KBKState} (h : KBK.LKBK p) : Distinct p := ⟨h.1, h.2.1, h.2.2.1⟩

theorem toKK_ne {c : Colour} {x y : Square} (h : x ≠ y) (t : Colour) :
    (KBK.toKK c x y t).wk ≠ (KBK.toKK c x y t).bk := by
  cases c
  · exact h
  · exact fun e => h e.symm

theorem toKK_dInf (c : Colour) (x y : Square) (t : Colour) :
    dInf (KBK.toKK c x y t).wk (KBK.toKK c x y t).bk = dInf x y := by
  cases c
  · rfl
  · exact dInf_comm _ _

/-- Strong king step. -/
theorem play_strongKing {p : KBK.KBKState} (hd : Distinct p) (ht : p.turn = .strong) {s : Square}
    (h1 : dInf p.sk s = 1) (_hb : s ≠ p.bs) (_hw : s ≠ p.wk) :
    play (ofKBK p) ⟨p.sk, s, none⟩ = ofKBK { p with sk := s, turn := .weak } := by
  have hsrc : (ofKBK p).board p.sk = some ⟨(ofKBK p).turn, .king⟩ := by
    simp only [ofKBK, ht, sideColour]; exact kbkBoard_sk
  have hsk : s ≠ p.sk := by intro e; rw [e, (dInf_eq_zero_iff).2 rfl] at h1; cases h1
  rw [play_kingStep hsrc rfl h1]
  clear hsrc h1
  apply Position.ext'
  · intro x
    obtain ⟨h12, h13, h23⟩ := hd
    simp only [ofKBK, kbkBoard, ht, sideColour]
    by_cases hx : x = s <;> by_cases hk : x = p.sk <;> by_cases hbx : x = p.bs <;>
      by_cases hwx : x = p.wk <;> simp_all
  · simp [ofKBK, ht, sideColour]
  · simp [ofKBK, updateCastling_noRights]
  · simp [ofKBK]

/-- Bishop move. -/
theorem play_bishop {p : KBK.KBKState} (hd : Distinct p) (ht : p.turn = .strong) {s : Square}
    (hk : s ≠ p.sk) (_hw : s ≠ p.wk) (_hsb : s ≠ p.bs) :
    play (ofKBK p) ⟨p.bs, s, none⟩ = ofKBK { p with bs := s, turn := .weak } := by
  obtain ⟨h12, h13, h23⟩ := hd
  have hsrc : (ofKBK p).board p.bs = some ⟨(ofKBK p).turn, .bishop⟩ := by
    simp only [ofKBK, ht, sideColour]; exact kbkBoard_bs h12
  rw [play_bishopStep hsrc rfl]
  clear hsrc
  apply Position.ext'
  · intro x
    simp only [ofKBK, kbkBoard, ht, sideColour]
    by_cases hx : x = s <;> by_cases hkx : x = p.sk <;> by_cases hbx : x = p.bs <;>
      by_cases hwx : x = p.wk <;> simp_all
  · simp [ofKBK, ht, sideColour]
  · simp [ofKBK, updateCastling_noRights]
  · simp [ofKBK]

/-- Weak king step to an empty square. -/
theorem play_weakKing {p : KBK.KBKState} (hd : Distinct p) (ht : p.turn = .weak) {s : Square}
    (h1 : dInf p.wk s = 1) (hk : s ≠ p.sk) (hb : s ≠ p.bs) :
    play (ofKBK p) ⟨p.wk, s, none⟩ = ofKBK { p with wk := s, turn := .strong } := by
  obtain ⟨h12, h13, h23⟩ := hd
  have hsrc : (ofKBK p).board p.wk = some ⟨(ofKBK p).turn, .king⟩ := by
    simp only [ofKBK, ht, sideColour]; exact kbkBoard_wk h13 h23
  have hsw : s ≠ p.wk := by intro e; rw [e, (dInf_eq_zero_iff).2 rfl] at h1; cases h1
  rw [play_kingStep hsrc rfl h1]
  clear hsrc h1
  apply Position.ext'
  · intro x
    simp only [ofKBK, kbkBoard, ht, sideColour]
    by_cases hx : x = s <;> by_cases hkx : x = p.sk <;> by_cases hbx : x = p.bs <;>
      by_cases hwx : x = p.wk <;> simp_all
  · simp [ofKBK, ht, sideColour, opp_opp]
  · simp [ofKBK, updateCastling_noRights]
  · simp [ofKBK]

/-- Weak king captures the bishop: the result is the embedded K vs K position. -/
theorem play_capture {p : KBK.KBKState} (hd : Distinct p) (ht : p.turn = .weak)
    (h1 : dInf p.wk p.bs = 1) :
    play (ofKBK p) ⟨p.wk, p.bs, none⟩ = ofKK (KBK.toKK p.strongColour p.sk p.bs p.strongColour) := by
  obtain ⟨h12, h13, h23⟩ := hd
  have hsrc : (ofKBK p).board p.wk = some ⟨(ofKBK p).turn, .king⟩ := by
    simp only [ofKBK, ht, sideColour]; exact kbkBoard_wk h13 h23
  rw [play_kingStep hsrc rfl h1]
  clear hsrc h1
  apply Position.ext'
  · intro x
    obtain ⟨σ, sk, bs, wk, tn⟩ := p
    simp only at h12 h13 h23 ht ⊢
    subst ht
    cases σ <;>
    · simp only [ofKBK, ofKK, kbkBoard, kkBoard, KBK.toKK, sideColour, Colour.opp]
      by_cases hx : x = bs <;> by_cases hkx : x = sk <;> by_cases hwx : x = wk <;> simp_all
  · simp [ofKBK, ofKK, KBK.toKK, ht, sideColour, opp_opp]
    cases p.strongColour <;> rfl
  · simp [ofKBK, ofKK, updateCastling_noRights]
  · simp [ofKK]

/-! ## Agreement of the step relations -/

theorem turn_ofKBK {p : KBK.KBKState} : (ofKBK p).turn = sideColour p.strongColour p.turn := rfl

/-- **K+B vs K agreement.** From an embedded locally legal K+B vs K configuration, the
kernel's legal successors are exactly the embeddings of the `KBK.Step` successors. -/
theorem legal_ofKBK_iff (p : KBK.KBKState) (hl : KBK.LKBK p) (q : Position) :
    Legal (ofKBK p) q ↔ ∃ b, KBK.Step (.kbk p) b ∧ q = embPos b := by
  have hd := distinct_of_LKBK hl
  obtain ⟨h12, h13, h23⟩ := hd
  constructor
  · rintro ⟨⟨src, dst, pro⟩, hm, rfl⟩
    unfold isLegal at hm
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hm
    obtain ⟨hp, hchk⟩ := hm
    obtain ⟨pc, hb, hc⟩ := own_of_isPseudo hp
    simp only at hb hp hchk ⊢
    rcases kbkBoard_some hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · -- strong king
      have ht : p.turn = .strong := by
        cases e : p.turn
        · rfl
        · rw [turn_ofKBK, e] at hc; exact absurd hc (opp_ne _)
      have hb' : (ofKBK p).board p.sk = some ⟨(ofKBK p).turn, .king⟩ := by
        rw [hb, show p.strongColour = (ofKBK p).turn from hc]
      rw [isPseudo_of_king hb', canCastle_false_of_noRook (no_rook_kbk p)] at hp
      simp only [Bool.or_false, Bool.and_eq_true, Option.isNone_iff_eq_none] at hp
      obtain ⟨htgt, hpro, hgeom⟩ := hp
      subst hpro
      have hd1 := kingGeom_iff.1 hgeom
      have hempty : (ofKBK p).board dst = none := by
        unfold targetOK at htgt
        cases hdb : (ofKBK p).board dst with
        | none => rfl
        | some pc =>
          rw [hdb] at htgt
          rcases kbkBoard_some hdb with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
            simp [turn_ofKBK, ht, sideColour] at htgt
      obtain ⟨_, hdb, hdw⟩ := kbkBoard_eq_none.1 hempty
      rw [play_strongKing ⟨h12, h13, h23⟩ ht hd1 hdb hdw] at hchk ⊢
      refine ⟨.kbk { p with sk := dst, turn := .weak },
        KBK.Step.strongKing ht ((attack_iff_dInf_one _ _).2 hd1) hdb hdw ?_, rfl⟩
      have hd' : Distinct { p with sk := dst, turn := .weak } := ⟨hdb, hdw, h23⟩
      intro hs
      have := (inCheck_strong hd').2 hs
      simp only [ofKBK, sideColour, ht] at hchk this
      rw [this] at hchk; cases hchk
    · -- bishop
      have ht : p.turn = .strong := by
        cases e : p.turn
        · rfl
        · rw [turn_ofKBK, e] at hc; exact absurd hc (opp_ne _)
      have hb' : (ofKBK p).board p.bs = some ⟨(ofKBK p).turn, .bishop⟩ := by
        rw [hb, show p.strongColour = (ofKBK p).turn from hc]
      rw [isPseudo_of_bishop hb'] at hp
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hp
      obtain ⟨htgt, hpro, hatt⟩ := hp
      subst hpro
      simp only [attacksFrom, Bool.and_eq_true] at hatt
      have hba := (bishop_kbk (σ := p.strongColour)).1 hatt
      have hns : dst ≠ p.bs := fun e => hba.1.1 e.symm
      have hnk : dst ≠ p.sk ∧ dst ≠ p.wk := by
        unfold targetOK at htgt
        cases hdb : (ofKBK p).board dst with
        | none => obtain ⟨a, _, c⟩ := kbkBoard_eq_none.1 hdb; exact ⟨a, c⟩
        | some pc =>
          rw [hdb] at htgt
          rcases kbkBoard_some hdb with ⟨_, rfl⟩ | ⟨e, rfl⟩ | ⟨_, rfl⟩
          · simp [turn_ofKBK, ht, sideColour] at htgt
          · exact absurd e hns
          · simp at htgt
      rw [play_bishop ⟨h12, h13, h23⟩ ht hnk.1 hnk.2 hns] at hchk ⊢
      refine ⟨.kbk { p with bs := dst, turn := .weak },
        KBK.Step.bishop ht hba hnk.1 hnk.2 ?_, rfl⟩
      have hd' : Distinct { p with bs := dst, turn := .weak } :=
        ⟨fun e => hnk.1 e.symm, h13, hnk.2⟩
      intro hs
      have := (inCheck_strong hd').2 hs
      simp only [ofKBK, sideColour, ht] at hchk this
      rw [this] at hchk; cases hchk
    · -- weak king
      have ht : p.turn = .weak := by
        cases e : p.turn
        · rw [turn_ofKBK, e] at hc; exact absurd hc.symm (opp_ne _)
        · rfl
      have hb' : (ofKBK p).board p.wk = some ⟨(ofKBK p).turn, .king⟩ := by
        rw [hb, show p.strongColour.opp = (ofKBK p).turn from hc]
      rw [isPseudo_of_king hb', canCastle_false_of_noRook (no_rook_kbk p)] at hp
      simp only [Bool.or_false, Bool.and_eq_true, Option.isNone_iff_eq_none] at hp
      obtain ⟨htgt, hpro, hgeom⟩ := hp
      subst hpro
      have hd1 := kingGeom_iff.1 hgeom
      have hdk : dst ≠ p.sk := by
        intro e; subst e
        unfold targetOK at htgt
        rw [show (ofKBK p).board p.sk = some ⟨p.strongColour, .king⟩ from kbkBoard_sk] at htgt
        simp at htgt
      have hdw : dst ≠ p.wk := by
        intro e; rw [e, (dInf_eq_zero_iff).2 rfl] at hd1; cases hd1
      by_cases hdb : dst = p.bs
      · -- capture of the bishop
        subst hdb
        rw [play_capture ⟨h12, h13, h23⟩ ht hd1] at hchk ⊢
        refine ⟨.kk _, KBK.Step.weakCaptures ht ((attack_iff_dInf_one _ _).2 hd1) ?_, rfl⟩
        intro hka
        have hne := toKK_ne (c := p.strongColour) h12 p.strongColour
        have := (inCheck_ofKK hne (ofKBK p).turn).2
          (by rw [toKK_dInf]; exact (attack_iff_dInf_one _ _).1 hka)
        rw [this] at hchk; cases hchk
      · rw [play_weakKing ⟨h12, h13, h23⟩ ht hd1 hdk hdb] at hchk ⊢
        refine ⟨.kbk { p with wk := dst, turn := .strong },
          KBK.Step.weakKing ht ((attack_iff_dInf_one _ _).2 hd1) hdk hdb ?_, rfl⟩
        have hd' : Distinct { p with wk := dst, turn := .strong } :=
          ⟨h12, fun e => hdk e.symm, fun e => hdb e.symm⟩
        intro hs
        have := (inCheck_weak hd').2 hs
        simp only [ofKBK, sideColour, ht] at hchk this
        rw [this] at hchk; cases hchk
  · rintro ⟨b, hs, rfl⟩
    cases hs with
    | @strongKing _ s ht hadj hb hw hchk =>
      have hd1 := (attack_iff_dInf_one _ _).1 hadj
      refine ⟨⟨p.sk, s, none⟩, ?_, (play_strongKing ⟨h12, h13, h23⟩ ht hd1 hb hw).symm⟩
      have hsrc : (ofKBK p).board p.sk = some ⟨(ofKBK p).turn, .king⟩ := by
        simp only [ofKBK, ht, sideColour]; exact kbkBoard_sk
      unfold isLegal
      rw [isPseudo_of_king hsrc, canCastle_false_of_noRook (no_rook_kbk p),
        play_strongKing ⟨h12, h13, h23⟩ ht hd1 hb hw]
      have hsk : s ≠ p.sk := by intro e; rw [e, (dInf_eq_zero_iff).2 rfl] at hd1; cases hd1
      have htgt : targetOK (ofKBK p) s = true := by
        simp [targetOK, ofKBK, kbkBoard_eq_none.2 ⟨hsk, hb, hw⟩]
      have hd' : Distinct { p with sk := s, turn := .weak } := ⟨hb, hw, h23⟩
      have hnc : inCheck (ofKBK { p with sk := s, turn := .weak }) p.strongColour = false := by
        cases e : inCheck (ofKBK { p with sk := s, turn := .weak }) p.strongColour
        · rfl
        · exact absurd ((inCheck_strong hd').1 e) hchk
      simp only [turn_ofKBK, ht, sideColour] at hnc ⊢
      simp [htgt, kingGeom_iff.2 hd1, hnc]
    | @bishop _ s ht hba hk hw hchk =>
      refine ⟨⟨p.bs, s, none⟩, ?_, (play_bishop ⟨h12, h13, h23⟩ ht hk hw (fun e => hba.1.1 e.symm)).symm⟩
      have hsrc : (ofKBK p).board p.bs = some ⟨(ofKBK p).turn, .bishop⟩ := by
        simp only [ofKBK, ht, sideColour]; exact kbkBoard_bs h12
      unfold isLegal
      rw [isPseudo_of_bishop hsrc, play_bishop ⟨h12, h13, h23⟩ ht hk hw (fun e => hba.1.1 e.symm)]
      have hatt := (bishop_kbk (σ := p.strongColour) (sk := p.sk) (wk := p.wk)).2 hba
      have hsb : s ≠ p.bs := fun e => hba.1.1 e.symm
      have htgt : targetOK (ofKBK p) s = true := by
        simp [targetOK, ofKBK, kbkBoard_eq_none.2 ⟨hk, hsb, hw⟩]
      have hd' : Distinct { p with bs := s, turn := .weak } := ⟨fun e => hk e.symm, h13, hw⟩
      have hnc : inCheck (ofKBK { p with bs := s, turn := .weak }) p.strongColour = false := by
        cases e : inCheck (ofKBK { p with bs := s, turn := .weak }) p.strongColour
        · rfl
        · exact absurd ((inCheck_strong hd').1 e) hchk
      simp only [Bool.and_eq_true, Bool.not_eq_true', Option.isNone_none, true_and]
      refine ⟨⟨htgt, ?_⟩, ?_⟩
      · simp only [attacksFrom, Bool.and_eq_true]; exact hatt
      · rw [turn_ofKBK, ht]; exact hnc
    | @weakKing _ s ht hadj hk hb hchk =>
      have hd1 := (attack_iff_dInf_one _ _).1 hadj
      refine ⟨⟨p.wk, s, none⟩, ?_, (play_weakKing ⟨h12, h13, h23⟩ ht hd1 hk hb).symm⟩
      have hsrc : (ofKBK p).board p.wk = some ⟨(ofKBK p).turn, .king⟩ := by
        simp only [ofKBK, ht, sideColour]; exact kbkBoard_wk h13 h23
      unfold isLegal
      rw [isPseudo_of_king hsrc, canCastle_false_of_noRook (no_rook_kbk p),
        play_weakKing ⟨h12, h13, h23⟩ ht hd1 hk hb]
      have hsw : s ≠ p.wk := by intro e; rw [e, (dInf_eq_zero_iff).2 rfl] at hd1; cases hd1
      have htgt : targetOK (ofKBK p) s = true := by
        simp [targetOK, ofKBK, kbkBoard_eq_none.2 ⟨hk, hb, hsw⟩]
      have hd' : Distinct { p with wk := s, turn := .strong } :=
        ⟨h12, fun e => hk e.symm, fun e => hb e.symm⟩
      have hnc : inCheck (ofKBK { p with wk := s, turn := .strong }) p.strongColour.opp = false := by
        cases e : inCheck (ofKBK { p with wk := s, turn := .strong }) p.strongColour.opp
        · rfl
        · exact absurd ((inCheck_weak hd').1 e) hchk
      simp only [turn_ofKBK, ht, sideColour] at hnc ⊢
      simp [htgt, kingGeom_iff.2 hd1, hnc]
    | weakCaptures ht hadj hna =>
      have hd1 := (attack_iff_dInf_one _ _).1 hadj
      refine ⟨⟨p.wk, p.bs, none⟩, ?_, (play_capture ⟨h12, h13, h23⟩ ht hd1).symm⟩
      have hsrc : (ofKBK p).board p.wk = some ⟨(ofKBK p).turn, .king⟩ := by
        simp only [ofKBK, ht, sideColour]; exact kbkBoard_wk h13 h23
      unfold isLegal
      rw [isPseudo_of_king hsrc, canCastle_false_of_noRook (no_rook_kbk p),
        play_capture ⟨h12, h13, h23⟩ ht hd1]
      have htgt : targetOK (ofKBK p) p.bs = true := by
        simp [targetOK, ofKBK, kbkBoard_bs h12, ht, sideColour, opp_ne]
      have hne := toKK_ne (c := p.strongColour) h12 p.strongColour
      have hnc : inCheck (ofKK (KBK.toKK p.strongColour p.sk p.bs p.strongColour))
          p.strongColour.opp = false := by
        cases e : inCheck (ofKK (KBK.toKK p.strongColour p.sk p.bs p.strongColour)) p.strongColour.opp
        · rfl
        · have := (inCheck_ofKK hne _).1 e
          rw [toKK_dInf] at this
          exact absurd ((attack_iff_dInf_one _ _).2 this) hna
      simp only [turn_ofKBK, ht, sideColour] at hnc ⊢
      simp [htgt, kingGeom_iff.2 hd1, hnc]

/-- On the K vs K side of `KBK.Pos`, `KBK.Step` is `LegalKK`. -/
theorem legal_kk_side (a : KKState) (ha : Admissible a) (q : Position) :
    Legal (ofKK a) q ↔ ∃ b, KBK.Step (.kk a) b ∧ q = embPos b := by
  rw [legal_ofKK_iff a (ne_of_admissible ha)]
  constructor
  · rintro ⟨b, hl, rfl⟩; exact ⟨.kk b, KBK.Step.kk hl, rfl⟩
  · rintro ⟨b, hs, rfl⟩
    cases hs with
    | kk hl => exact ⟨_, hl, rfl⟩

theorem chain_iff_reach_kbk {a b : KBK.Pos} : Chain KBK.Step a b ↔ KBK.Reach a b := by
  constructor
  · intro h; induction h with
    | refl => exact KBK.Reach.refl _
    | tail _ hs ih => exact KBK.Reach.tail ih hs
  · intro h; induction h with
    | refl => exact Chain.refl _
    | tail _ hs ih => exact Chain.tail ih hs

/-- **Deadness agreement** on the whole class `LKBK ∪ AdmKK`. -/
theorem deadK_embPos_iff (a : KBK.Pos) (ha : KBK.Closed a) : DeadK (embPos a) ↔ KBK.Dead a := by
  have := dead_transfer embPos KBK.Step KBK.Closed KBK.Mated
    (fun a ha q => by
      cases a with
      | kbk p => exact legal_ofKBK_iff p ha q
      | kk a => exact legal_kk_side a ha q)
    (fun _ _ ha hs => KBK.closed_of_step hs ha)
    (fun a ha => by
      cases a with
      | kbk p =>
        simp only [embPos, MatedK, KBK.Mated]
        rw [turn_ofKBK, inCheck_side (distinct_of_LKBK ha)]
        have hs := legal_ofKBK_iff p ha
        constructor
        · rintro ⟨hc, hn⟩
          exact ⟨hc, fun ⟨q, hq⟩ => hn ⟨embPos q, (hs _).2 ⟨q, hq, rfl⟩⟩⟩
        · rintro ⟨hc, hn⟩
          refine ⟨hc, fun ⟨q, hq⟩ => ?_⟩
          obtain ⟨b, hb, _⟩ := (hs q).1 hq
          exact hn ⟨b, hb⟩
      | kk a =>
        simp only [embPos, MatedK, KBK.Mated]
        constructor
        · rintro ⟨hc, _⟩
          have ha' : Admissible a := ha
          have := (inCheck_ofKK (ne_of_admissible ha') _).1 hc
          unfold Admissible at ha'; omega
        · rintro (⟨_, hc, _⟩ | ⟨_, hc, _⟩) <;> exact absurd hc (not_inCheck_of_admissible ha _))
    a ha
  rw [this]
  simp only [KBK.Dead, chain_iff_reach_kbk]

theorem deadK_ofKBK_iff (p : KBK.KBKState) (hl : KBK.LKBK p) :
    DeadK (ofKBK p) ↔ KBK.Dead (.kbk p) :=
  deadK_embPos_iff (.kbk p) hl

/-- **Kernel form of EC-T0002.** Every locally legal K+B vs K position is dead in the
kernel. -/
theorem kernel_dead_KBK {p : KBK.KBKState} (hl : KBK.LKBK p) : DeadK (ofKBK p) :=
  (deadK_ofKBK_iff p hl).2 (KBK.dead_of_LKBK hl)

/-! ## Non-vacuity of the agreement hypotheses -/

/-- An admissible K vs K position (Ka1 vs Kc3) has a kernel-legal move, obtained through
the agreement theorem. -/
theorem kernel_kk_has_move : ∃ q, Legal (ofKK ⟨KK.a1, KK.c3, .white⟩) q := by
  have ha : Admissible (⟨KK.a1, KK.c3, .white⟩ : KKState) := by unfold Admissible; decide
  obtain ⟨b, hb⟩ := exists_legal_move_of_admissible ha
  exact ⟨ofKK b, (legal_ofKK_iff _ (ne_of_admissible ha) _).2 ⟨b, hb, rfl⟩⟩

/-- The K+B vs K check position of EC-T0002 (weak Ka1 checked by Bc3; strong Kh8) is
locally legal. Its kernel embedding is in check and has a kernel-legal move. -/
theorem kernel_kbk_check_has_move :
    KBK.LKBK KBK.checkState ∧ inCheck (ofKBK KBK.checkState) (ofKBK KBK.checkState).turn = true ∧
      ∃ q, Legal (ofKBK KBK.checkState) q := by
  have hl : KBK.LKBK KBK.checkState := by
    refine ⟨by decide, by decide, by decide, ?_⟩
    show ¬ kingAttacks KBK.sqA1 KBK.sqH8
    rw [attack_iff_dInf_one]; decide
  refine ⟨hl, ?_, ?_⟩
  · exact (inCheck_side (distinct_of_LKBK hl) KBK.Side.weak).2 KBK.bishop_check_exists
  · obtain ⟨b, hb⟩ := KBK.weak_has_move_of_inCheck hl rfl KBK.bishop_check_exists
    exact ⟨embPos b, (legal_ofKBK_iff _ hl _).2 ⟨b, hb, rfl⟩⟩

end EndgameChess.Rules
