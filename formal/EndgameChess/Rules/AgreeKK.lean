import EndgameChess.Rules.Lemmas

/-!
# Rules kernel K2 — K vs K agreement (closes gap G1 for EC-T0001)

Embeds the frozen EC-T0001 model (`EndgameChess.KK`) into the general kernel and proves:
- `legal_ofKK_iff`: from an embedded K vs K position, the kernel's legal successors are
  exactly the embeddings of the `KK.LegalKK` successors;
- `legalKK_iff_kernel`: `LegalKK a b ↔ Legal (ofKK a) (ofKK b)`;
- `deadK_ofKK_iff`: kernel-dead ⇔ `KK.Dead` on admissible configurations;
- `kernel_dead_KK`: every admissible K vs K position is dead in the kernel.

`KK.lean` is imported, not edited.
-/

namespace EndgameChess.Rules

open EndgameChess.KK

/-- The board with exactly the two kings. -/
def kkBoard (w b : Square) : Board := fun s =>
  if s = w then some ⟨.white, .king⟩ else if s = b then some ⟨.black, .king⟩ else none

/-- Embedding of a K vs K configuration into a kernel position: no castling rights (there
are no rooks) and no en-passant target (there are no pawns). -/
def ofKK (a : KKState) : Position :=
  { board := kkBoard a.wk a.bk, turn := a.turn, castling := noRights, ep := none }

theorem kkBoard_eq_some {a : KKState} (hne : a.wk ≠ a.bk) {s : Square} {pc : Piece} :
    kkBoard a.wk a.bk s = some pc ↔ pc.kind = .king ∧ s = a.king pc.colour := by
  obtain ⟨col, kind⟩ := pc
  unfold kkBoard
  by_cases h1 : s = a.wk
  · subst h1; cases col <;> simp [KKState.king, eq_comm, hne] <;> cases kind <;> simp
  · by_cases h2 : s = a.bk
    · subst h2; cases col <;> simp [KKState.king, h1] <;> cases kind <;> simp
    · cases col <;> simp [KKState.king, h1, h2]

theorem kkBoard_eq_none {w b s : Square} : kkBoard w b s = none ↔ s ≠ w ∧ s ≠ b := by
  unfold kkBoard
  by_cases h1 : s = w <;> by_cases h2 : s = b <;> simp_all

theorem king_ne_opp {a : KKState} (hne : a.wk ≠ a.bk) (c : Colour) : a.king c ≠ a.king c.opp := by
  cases c
  · exact hne
  · exact fun h => hne h.symm

/-- In a two-king board, `c` attacks `t` iff `c`'s king is adjacent to `t`. -/
theorem attacked_kk {a : KKState} (hne : a.wk ≠ a.bk) (t : Square) (c : Colour) :
    attacked (kkBoard a.wk a.bk) t c = true ↔ dInf (a.king c) t = 1 := by
  rw [attacked_iff]
  constructor
  · rintro ⟨s, ⟨col, kind⟩, hb, hc, ha⟩
    obtain ⟨hk, rfl⟩ := (kkBoard_eq_some hne).1 hb
    simp only at hk hc; subst hk hc
    simpa [attacksFrom, kingGeom_iff] using ha
  · intro h
    refine ⟨a.king c, ⟨c, .king⟩, (kkBoard_eq_some hne).2 ⟨rfl, rfl⟩, rfl, ?_⟩
    simpa [attacksFrom, kingGeom_iff] using h

/-- Kernel check on an embedded K vs K position is exactly adjacency of the kings. -/
theorem inCheck_ofKK {a : KKState} (hne : a.wk ≠ a.bk) (c : Colour) :
    inCheck (ofKK a) c = true ↔ dInf a.wk a.bk = 1 := by
  rw [inCheck_iff]
  constructor
  · rintro ⟨s, hs, hat⟩
    obtain ⟨_, rfl⟩ := (kkBoard_eq_some hne).1 hs
    have := (attacked_kk hne _ _).1 hat
    rw [dInf_comm, dInf_king] at this
    simpa using this
  · intro h
    refine ⟨a.king c, (kkBoard_eq_some hne).2 ⟨rfl, rfl⟩, (attacked_kk hne _ _).2 ?_⟩
    rw [dInf_comm, dInf_king]; simpa using h

theorem no_rook_ofKK {a : KKState} (hne : a.wk ≠ a.bk) (s : Square) :
    (ofKK a).board s ≠ some ⟨(ofKK a).turn, .rook⟩ := by
  intro h
  have := ((kkBoard_eq_some hne).1 h).1
  cases this

/-- The kernel's one-square king step from an embedded position is the embedding of
`KKState.moveKing`. -/
theorem play_ofKK {a : KKState} (hne : a.wk ≠ a.bk) {s : Square}
    (h1 : dInf (a.king a.turn) s = 1) (h2 : s ≠ a.king a.turn.opp) :
    play (ofKK a) ⟨a.king a.turn, s, none⟩ = ofKK (a.moveKing s) := by
  have hsrc : (ofKK a).board (a.king a.turn) = some ⟨(ofKK a).turn, .king⟩ :=
    (kkBoard_eq_some hne).2 ⟨rfl, rfl⟩
  rw [play_kingStep hsrc rfl h1]
  apply Position.ext'
  · intro x
    obtain ⟨w, b, t⟩ := a
    cases t <;>
    · simp only [KKState.king, Colour.opp] at h2 hne ⊢
      simp only [ofKK, KKState.moveKing, kkBoard]
      by_cases hx : x = s <;> by_cases hw : x = w <;> by_cases hb : x = b <;> simp_all
  · simp [ofKK, moveKing_turn]
  · simp [ofKK, updateCastling_noRights]
  · simp [ofKK]

/-- **K vs K agreement.** From an embedded K vs K position (kings on distinct squares),
the kernel's legal successors are exactly the embeddings of `KK.LegalKK` successors. -/
theorem legal_ofKK_iff (a : KKState) (hne : a.wk ≠ a.bk) (q : Position) :
    Legal (ofKK a) q ↔ ∃ b, LegalKK a b ∧ q = ofKK b := by
  constructor
  · rintro ⟨⟨src, dst, pro⟩, hm, rfl⟩
    unfold isLegal at hm
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hm
    obtain ⟨hp, hchk⟩ := hm
    obtain ⟨⟨col, kind⟩, hb, hc⟩ := own_of_isPseudo hp
    obtain ⟨hk, hsrc⟩ := (kkBoard_eq_some hne).1 hb
    simp only at hk hc hsrc; subst hk hc hsrc
    rw [isPseudo_of_king hb, canCastle_false_of_noRook (no_rook_ofKK hne)] at hp
    simp only [Bool.or_false, Bool.and_eq_true, Option.isNone_iff_eq_none] at hp
    obtain ⟨htgt, hpro, hgeom⟩ := hp
    subst hpro
    simp only [show (ofKK a).turn = a.turn from rfl] at hgeom hchk hb htgt ⊢
    have hd1 := kingGeom_iff.1 hgeom
    -- the target is empty: every occupied square holds a king
    have hempty : kkBoard a.wk a.bk dst = none := by
      unfold targetOK at htgt
      cases hdb : (ofKK a).board dst with
      | none => simpa [ofKK] using hdb
      | some pc =>
        rw [hdb] at htgt
        have := ((kkBoard_eq_some hne).1 hdb).1
        simp [this] at htgt
    have hdo : dst ≠ a.king a.turn.opp := by
      obtain ⟨h1, h2⟩ := kkBoard_eq_none.1 hempty
      cases ht : a.turn <;> simp [KKState.king, Colour.opp, h1, h2]
    rw [play_ofKK hne hd1 hdo] at hchk ⊢
    refine ⟨a.moveKing dst, (legalKK_iff_prose a _).2 ⟨dst, hd1, hdo, ?_, rfl⟩, rfl⟩
    -- no check after the move: the kings are not adjacent
    have hk := moveKing_kings a dst
    have hne' : (a.moveKing dst).wk ≠ (a.moveKing dst).bk := by
      obtain ⟨w, b, t⟩ := a
      cases t
      · simp only [KKState.moveKing, KKState.king, Colour.opp] at hdo ⊢; exact hdo
      · simp only [KKState.moveKing, KKState.king, Colour.opp] at hdo ⊢; exact fun e => hdo e.symm
    have hn1 : dInf (a.moveKing dst).wk (a.moveKing dst).bk ≠ 1 := by
      intro h; rw [(inCheck_ofKK hne' _).2 h] at hchk; cases hchk
    rw [← dInf_king (a.moveKing dst) a.turn, hk.1, hk.2] at hn1
    have hn0 : dInf dst (a.king a.turn.opp) ≠ 0 := fun h => hdo ((dInf_eq_zero_iff).1 h)
    omega
  · rintro ⟨b, hl, rfl⟩
    obtain ⟨s, h1, h2, h3, rfl⟩ := (legalKK_iff_prose a b).1 hl
    refine ⟨⟨a.king a.turn, s, none⟩, ?_, (play_ofKK hne h1 h2).symm⟩
    unfold isLegal
    have hsrc : (ofKK a).board (a.king a.turn) = some ⟨(ofKK a).turn, .king⟩ :=
      (kkBoard_eq_some hne).2 ⟨rfl, rfl⟩
    rw [isPseudo_of_king hsrc, canCastle_false_of_noRook (no_rook_ofKK hne), play_ofKK hne h1 h2]
    have hso : s ≠ a.king a.turn := by
      intro h; rw [h, (dInf_eq_zero_iff).2 rfl] at h1; cases h1
    have hempty : (ofKK a).board s = none := by
      simp only [ofKK]
      refine kkBoard_eq_none.2 ?_
      cases ht : a.turn <;> simp_all [KKState.king, Colour.opp]
    have htgt : targetOK (ofKK a) s = true := by simp [targetOK, hempty]
    have hk := moveKing_kings a s
    have hne' : (a.moveKing s).wk ≠ (a.moveKing s).bk := by
      intro h
      have h3' := h3
      rw [← hk.1, ← hk.2, dInf_king, h, (dInf_eq_zero_iff).2 rfl] at h3'
      cases h3'
    have hnc : inCheck (ofKK (a.moveKing s)) a.turn = false := by
      cases hc : inCheck (ofKK (a.moveKing s)) a.turn
      · rfl
      · have := (inCheck_ofKK hne' _).1 hc
        rw [← dInf_king (a.moveKing s) a.turn, hk.1, hk.2] at this
        omega
    simp [htgt, kingGeom_iff.2 h1]
    exact hnc

theorem kkBoard_injective {a b : KKState} (ha : a.wk ≠ a.bk) (hb : b.wk ≠ b.bk)
    (h : kkBoard a.wk a.bk = kkBoard b.wk b.bk) : a.wk = b.wk ∧ a.bk = b.bk := by
  have h1 : kkBoard b.wk b.bk a.wk = some ⟨.white, .king⟩ := by
    rw [← h]; exact (kkBoard_eq_some ha).2 ⟨rfl, rfl⟩
  have h2 : kkBoard b.wk b.bk a.bk = some ⟨.black, .king⟩ := by
    rw [← h]; exact (kkBoard_eq_some ha).2 ⟨rfl, rfl⟩
  exact ⟨((kkBoard_eq_some hb).1 h1).2, ((kkBoard_eq_some hb).1 h2).2⟩

theorem ofKK_injective {a b : KKState} (ha : a.wk ≠ a.bk) (hb : b.wk ≠ b.bk)
    (h : ofKK a = ofKK b) : a = b := by
  have hbd : kkBoard a.wk a.bk = kkBoard b.wk b.bk := congrArg Position.board h
  have ht : a.turn = b.turn := congrArg Position.turn h
  obtain ⟨h1, h2⟩ := kkBoard_injective ha hb hbd
  obtain ⟨aw, ab, at'⟩ := a
  obtain ⟨bw, bb, bt⟩ := b
  simp_all

/-- `LegalKK a b ↔ Legal (ofKK a) (ofKK b)` (kings on distinct squares in both). -/
theorem legalKK_iff_kernel (a b : KKState) (ha : a.wk ≠ a.bk) (hb : b.wk ≠ b.bk) :
    LegalKK a b ↔ Legal (ofKK a) (ofKK b) := by
  rw [legal_ofKK_iff a ha]
  constructor
  · intro h; exact ⟨b, h, rfl⟩
  · rintro ⟨b', hl, he⟩
    have hb' : b'.wk ≠ b'.bk := by
      have := admissible_of_legal_step hl
      unfold Admissible at this
      intro e; rw [e, (dInf_eq_zero_iff).2 rfl] at this; cases this
    rw [ofKK_injective hb hb' he]; exact hl

theorem ne_of_admissible {a : KKState} (h : Admissible a) : a.wk ≠ a.bk := by
  intro e; unfold Admissible at h; rw [e, (dInf_eq_zero_iff).2 rfl] at h; cases h

theorem chain_iff_reach {a b : KKState} : Chain LegalKK a b ↔ KK.Reach a b := by
  constructor
  · intro h; induction h with
    | refl => exact KK.Reach.refl _
    | tail _ hs ih => exact KK.Reach.tail ih hs
  · intro h; induction h with
    | refl => exact Chain.refl _
    | tail _ hs ih => exact Chain.tail ih hs

/-- **Deadness agreement.** On admissible K vs K configurations, kernel-dead ⇔ `KK.Dead`. -/
theorem deadK_ofKK_iff (a : KKState) (ha : Admissible a) : DeadK (ofKK a) ↔ KK.Dead a := by
  have := dead_transfer ofKK LegalKK Admissible (fun q => Checkmate .white q ∨ Checkmate .black q)
    (fun a ha q => legal_ofKK_iff a (ne_of_admissible ha) q)
    (fun _ _ _ hs => admissible_of_legal_step hs)
    (fun a ha => by
      constructor
      · rintro ⟨hc, _⟩
        have := (inCheck_ofKK (ne_of_admissible ha) _).1 hc
        unfold Admissible at ha; omega
      · rintro (⟨_, hc, _⟩ | ⟨_, hc, _⟩) <;> exact absurd hc (not_inCheck_of_admissible ha _))
    a ha
  rw [this]
  simp only [KK.Dead, chain_iff_reach]

/-- **Kernel form of EC-T0001.** Every admissible K vs K position is dead in the kernel. -/
theorem kernel_dead_KK {a : KKState} (ha : Admissible a) : DeadK (ofKK a) :=
  (deadK_ofKK_iff a ha).2 (dead_of_admissible ha)

end EndgameChess.Rules
