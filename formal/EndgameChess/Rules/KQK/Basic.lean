import EndgameChess.Rules.LoneKing.Moves
import EndgameChess.Rules.KRKConfinement

/-! Exact queen geometry over the rules kernel. Shared K+X safety is imported. -/
namespace EndgameChess.Rules.KQK
open EndgameChess.KK

abbrev IsKQK := LoneKing.Material .queen
abbrev queenBoard := LoneKing.board .queen
abbrev SafeQueen := LoneKing.Safe

def pos (σ : Colour) (sk qs wk : Square) (turn : Colour) : Position :=
  ⟨queenBoard σ sk qs wk,turn,noRights,none⟩

/-- A clear queen ray, with the two other occupied squares as possible blockers. -/
def QueenSees (qs t a b : Square) : Prop :=
  (diagGeom qs t = true ∨ RookLine qs t) ∧
    isBetween qs a t = false ∧ isBetween qs b t = false

theorem between_self (s t : Square) : isBetween s s t = false := by
  simp [isBetween]

theorem between_end (s t : Square) : isBetween s t t = false := by
  simp [isBetween]

theorem path_clear {k : PieceType} {σ : Colour} {sk xs wk s t : Square} :
    pathClear (LoneKing.board k σ sk xs wk) s t = true ↔
      isBetween s sk t = false ∧ isBetween s xs t = false ∧
      isBetween s wk t = false := by
  rw [pathClear_iff]
  constructor
  · intro h
    have absent (v : Square) (hv : v = sk ∨ v = xs ∨ v = wk) :
        isBetween s v t = false := by
      cases he : isBetween s v t
      · rfl
      · have hn := LoneKing.board_none.mp (h v he)
        rcases hv with rfl | rfl | rfl
        · exact False.elim (hn.1 rfl)
        · exact False.elim (hn.2.1 rfl)
        · exact False.elim (hn.2.2 rfl)
    exact ⟨absent sk (Or.inl rfl),absent xs (Or.inr (Or.inl rfl)),
      absent wk (Or.inr (Or.inr rfl))⟩
  · rintro ⟨hs,hx,hw⟩ v hv
    apply LoneKing.board_none.mpr
    constructor
    · rintro rfl; rw [hs] at hv; cases hv
    · constructor
      · rintro rfl; rw [hx] at hv; cases hv
      · rintro rfl; rw [hw] at hv; cases hv

theorem queen_attacks {σ : Colour} {sk qs wk t : Square} :
    attacksFrom (queenBoard σ sk qs wk) ⟨σ,.queen⟩ qs t = true ↔
      QueenSees qs t sk wk := by
  simp only [attacksFrom,Bool.and_eq_true,Bool.or_eq_true,lineGeom_iff,
    path_clear,between_self,true_and,QueenSees]

theorem rook_sees_queen {qs t a b : Square} (h : RookSees qs t a b) :
    QueenSees qs t a b := by
  refine ⟨Or.inr h.1,?_,?_⟩
  · cases he : isBetween qs a t
    · rfl
    · exact False.elim (h.2.1 ((isBetween_iff_onSeg h.1).mp he))
  · cases he : isBetween qs b t
    · rfl
    · exact False.elim (h.2.2 ((isBetween_iff_onSeg h.1).mp he))

theorem strong_check {q : Position} {σ : Colour} {sk qs wk : Square}
    (h : IsKQK q σ sk qs wk) : inCheck q σ = true ↔ dInf wk sk = 1 :=
  LoneKing.strong_check (by decide) h

theorem weak_check {q : Position} {σ : Colour} {sk qs wk : Square}
    (h : IsKQK q σ sk qs wk) :
    inCheck q σ.opp = true ↔ dInf sk wk = 1 ∨ QueenSees qs wk sk wk := by
  rw [LoneKing.weak_check (by decide) h,queen_attacks]

theorem safe_reply {q r : Position} {σ : Colour} {sk qs wk : Square}
    (h : IsKQK q σ sk qs wk) (ht : q.turn = σ.opp)
    (hs : SafeQueen sk qs wk) (hl : Legal q r) :
    ∃ t, IsKQK r σ sk qs t ∧ r.turn = σ ∧ dInf wk t = 1 ∧
      2 ≤ dInf sk t ∧ ¬ QueenSees qs t sk t := by
  obtain ⟨t,hm,hr,hd⟩ := LoneKing.safe_reply h ht hs hl
  have hn := legal_mover_safe hl
  rw [ht] at hn
  have hnot : ¬ (dInf sk t = 1 ∨ QueenSees qs t sk t) := by
    intro hh
    have hh := (weak_check hm).mpr hh
    rw [hn] at hh; cases hh
  have h0 : dInf sk t ≠ 0 := fun hh => hm.2.1 (dInf_eq_zero_iff.mp hh)
  exact ⟨t,hm,hr,hd,by have := fun h => hnot (Or.inl h); omega,
    fun h => hnot (Or.inr h)⟩

/-- Universal confinement transfers because queen rays include rook rays.
This does not assert that any reply exists. -/
theorem rank_reply {q r : Position} {σ : Colour} {sk qs wk : Square}
    (h : IsKQK q σ sk qs wk) (ht : q.turn = σ.opp)
    (hs : SafeQueen sk qs wk) (hb : sk.2.val < qs.2.val)
    (hw : qs.2.val < wk.2.val) (hl : Legal q r) :
    ∃ t, IsKQK r σ sk qs t ∧ r.turn = σ ∧ qs.2.val < t.2.val := by
  obtain ⟨t,hm,hr,hd,_,hn⟩ := safe_reply h ht hs hl
  exact ⟨t,hm,hr,rook_rank_barrier hb hw hd (Ne.symm hm.2.2.1)
    (fun h => hn (rook_sees_queen h))⟩

theorem force_weak_safe {q : Position} {σ : Colour} {sk qs wk : Square}
    (h : IsKQK q σ sk qs wk) (ht : q.turn = σ.opp)
    (hw : ForceMate σ q) : SafeQueen sk qs wk :=
  LoneKing.force_weak_safe (by decide) h ht hw

end EndgameChess.Rules.KQK
