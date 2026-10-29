import EndgameChess.Rules.KPK.Holding
import EndgameChess.Rules.KQK.BoardOutcome
import EndgameChess.Rules.KRKCentral.Weak
import EndgameChess.Rules.KRKForcing.OutcomeClassification

namespace EndgameChess.Rules.KPK
open EndgameChess.KK

/-- A promotion move with the actual choice retained. -/
def promote (ps t : Square) (k : PromoPiece) : Move := ⟨ps, t, some k⟩

theorem promotion_legal {q : Position} {σ : Colour} {sk ps wk t : Square}
    (h : IsKPK q σ sk ps wk) (ht : q.turn = σ) (far : 2 ≤ dInf sk wk)
    (push : Push q σ ps t) (last : t.2.val = lastRank σ) (k : PromoPiece) :
    isLegal q (promote ps t k) = true := by
  apply (pawn_legal_iff h ht rfl far).mpr
  exact ⟨push, (promo_some_iff σ ps t k).mpr ((promotion_rank σ t).mp last)⟩

theorem promotion_material {q : Position} {σ : Colour} {sk ps wk t : Square}
    (h : IsKPK q σ sk ps wk) (ht : q.turn = σ) (push : Push q σ ps t) (k : PromoPiece) :
    LoneKing.Material k.toKind (play q (promote ps t k)) σ sk t wk :=
  pawn_play_material h ht (m := promote ps t k) rfl push

/-- Neither minor promotion can win, even cooperatively: each is a dead successor. -/
theorem minor_promotion_dead {q : Position} {σ : Colour} {sk ps wk t : Square}
    (h : IsKPK q σ sk ps wk) (ht : q.turn = σ) (far : 2 ≤ dInf sk wk)
    (push : Push q σ ps t) (last : t.2.val = lastRank σ) :
    DeadK (play q (promote ps t .bishop)) ∧ DeadK (play q (promote ps t .knight)) := by
  constructor
  · exact dead_of_legal_into_KBK
      ⟨_, promotion_legal h ht far push last .bishop, rfl⟩
      (promotion_material h ht push .bishop)
  · exact dead_of_legal_into_KNK
      ⟨_, promotion_legal h ht far push last .knight, rfl⟩
      (promotion_material h ht push .knight)

/-- Compose one actual move with a board bound, preserving its exact ply budget. -/
theorem choose_bound {q r : Position} {σ : Colour} {n : Nat}
    (turn : q.turn = σ) (legal : Legal q r) (win : MateWithin σ n r) :
    MateWithin σ (n+1) q := by
  have live : ¬ DeadK q := by
    obtain ⟨t, reach, goal⟩ := mateWithin_sound win
    exact fun dead => dead ⟨t, reachK_cons legal reach, goal.2⟩
  exact Or.inr ⟨live, Or.inl ⟨turn, r, legal, win⟩⟩

/-- The full weak-turn queen criterion, rather than a blanket "promotion wins". -/
theorem queen_promotion_bound {q : Position} {σ : Colour} {sk ps wk t : Square}
    (h : IsKPK q σ sk ps wk) (ht : q.turn = σ) (far : 2 ≤ dInf sk wk)
    (push : Push q σ ps t) (last : t.2.val = lastRank σ)
    (criterion : MatedK (play q (promote ps t .queen)) ∨
      (LoneKing.Safe sk t wk ∧ ∃ r, Legal (play q (promote ps t .queen)) r)) :
    MateWithin σ 99 q := by
  have material := promotion_material h ht push .queen
  have turn : (play q (promote ps t .queen)).turn = σ.opp := by rw [play_turn, ht]
  have bound : MateWithin σ 98 (play q (promote ps t .queen)) := by
    rcases criterion with mate | ⟨safe, moves⟩
    · exact mateWithin_mono (show MateWithin σ 0 _ from ⟨turn, mate⟩) (by decide)
    · exact KQK.safe_weak_entry_bound material turn safe moves
  exact choose_bound ht ⟨_, promotion_legal h ht far push last .queen, rfl⟩ bound

/-- Exact queen successor forcing criterion. This does not classify other root moves. -/
theorem queen_successor_iff {q : Position} {σ : Colour} {sk ps wk t : Square}
    (h : IsKPK q σ sk ps wk) (ht : q.turn = σ) (push : Push q σ ps t) :
    ForceMate σ (play q (promote ps t .queen)) ↔
      MatedK (play q (promote ps t .queen)) ∨
        (LoneKing.Safe sk t wk ∧ ∃ r, Legal (play q (promote ps t .queen)) r) :=
  KQK.weak_force_safe_iff (promotion_material h ht push .queen) (by rw [play_turn, ht])

/-- The rook alternative has its own terminal/safety criterion, with no queen-stalemate assumption. -/
theorem rook_successor_iff {q : Position} {σ : Colour} {sk ps wk t : Square}
    (h : IsKPK q σ sk ps wk) (ht : q.turn = σ) (push : Push q σ ps t) :
    ForceMate σ (play q (promote ps t .rook)) ↔
      MatedK (play q (promote ps t .rook)) ∨
        (LoneKing.Safe sk t wk ∧ ∃ r, Legal (play q (promote ps t .rook)) r) :=
  krk_weak_force_safe_iff (promotion_material h ht push .rook) (by rw [play_turn, ht])

theorem rook_promotion_bound {q : Position} {σ : Colour} {sk ps wk t : Square}
    (h : IsKPK q σ sk ps wk) (ht : q.turn = σ) (far : 2 ≤ dInf sk wk)
    (push : Push q σ ps t) (last : t.2.val = lastRank σ)
    (criterion : MatedK (play q (promote ps t .rook)) ∨
      (LoneKing.Safe sk t wk ∧ ∃ r, Legal (play q (promote ps t .rook)) r)) :
    MateWithin σ 99 q := by
  have material := promotion_material h ht push .rook
  have turn : (play q (promote ps t .rook)).turn = σ.opp := by rw [play_turn, ht]
  have bound := KRKCentral.weak98 material turn ((rook_successor_iff h ht push).mpr criterion)
  exact choose_bound ht ⟨_, promotion_legal h ht far push last .rook, rfl⟩ bound

/-- A safe checking queen promotion is a sufficient geometric winning family. -/
theorem checking_queen_promotion_bound {q : Position} {σ : Colour} {sk ps wk t : Square}
    (h : IsKPK q σ sk ps wk) (ht : q.turn = σ) (far : 2 ≤ dInf sk wk)
    (push : Push q σ ps t) (last : t.2.val = lastRank σ)
    (safe : LoneKing.Safe sk t wk) (check : KQK.QueenSees t wk sk wk) :
    MateWithin σ 99 q := by
  apply queen_promotion_bound h ht far push last
  by_cases moves : ∃ r, Legal (play q (promote ps t .queen)) r
  · exact Or.inr ⟨safe, moves⟩
  · left
    refine ⟨?_, moves⟩
    rw [play_turn, ht]
    exact (KQK.weak_check (promotion_material h ht push .queen)).mpr (Or.inr check)

/-- A fresh KPK root can use the 99-ply composite directly; no history is erased. -/
theorem fresh_checking_queen_promotion {q : Position} {σ : Colour} {sk ps wk t : Square}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk) (ht : q.turn = σ)
    (push : Push q σ ps t) (last : t.2.val = lastRank σ)
    (safe : LoneKing.Safe sk t wk) (check : KQK.QueenSees t wk sk wk) :
    FreshGame.Within σ 99 (FreshGame.fresh q) :=
  FreshGame.fresh_sub100
    (checking_queen_promotion_bound h ht fresh.kings push last safe check) (by decide)

theorem fresh_checking_queen_actual_win {q : Position} {σ : Colour} {sk ps wk t : Square}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk) (ht : q.turn = σ)
    (push : Push q σ ps t) (last : t.2.val = lastRank σ)
    (safe : LoneKing.Safe sk t wk) (check : KQK.QueenSees t wk sk wk) :
    FreshGame.ActualWin σ (FreshGame.fresh q) :=
  FreshGame.actual_win_of_rule ⟨99, fresh_checking_queen_promotion h fresh ht push last safe check⟩

end EndgameChess.Rules.KPK
