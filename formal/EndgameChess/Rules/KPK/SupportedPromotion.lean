import EndgameChess.Rules.KPK.RookPawn
import EndgameChess.Rules.KQK.InteriorEscape
import EndgameChess.Rules.KQK.Symmetry

namespace EndgameChess.Rules.KPK
open EndgameChess.KK

/-- Side-by-side king and pawn on the pawn owner's seventh rank. -/
def SupportedSeventh (σ : Colour) (sk ps : Square) : Prop :=
  height σ sk = 6 ∧ height σ ps = 6 ∧ absDiff sk.1.val ps.1.val = 1

set_option maxHeartbeats 2000000 in
/-- A queen on the eighth rank supported from the seventh cannot stalemate
a lower king. Three local neighbours suffice; no board-position enumeration. -/
theorem supported_white_escape {sk qs wk : Square}
    (sy : sk.2.val = 6) (qy : qs.2.val = 7)
    (adjacent : absDiff sk.1.val qs.1.val = 1)
    (far : 2 ≤ dInf sk wk) (below : wk.2.val ≤ 6) :
    ∃ t, dInf wk t = 1 ∧ 2 ≤ dInf sk t ∧ ¬ KQK.QueenRay qs t := by
  classical
  by_cases escape : ∃ t, dInf wk t = 1 ∧ 2 ≤ dInf sk t ∧ ¬ KQK.QueenRay qs t
  · exact escape
  apply False.elim
  have cover (t : Square) (step : dInf wk t = 1) :
      dInf sk t ≤ 1 ∨ KQK.QueenRay qs t := by
    by_cases safe : 2 ≤ dInf sk t
    · by_cases ray : KQK.QueenRay qs t
      · exact Or.inr ray
      · exact False.elim (escape ⟨t, step, safe, ray⟩)
    · exact Or.inl (by omega)
  let y : Fin 8 := ⟨if wk.2.val = 0 then 1 else wk.2.val - 1, by split <;> omega⟩
  let l : Fin 8 := ⟨if wk.1.val = 0 then 1 else wk.1.val - 1, by split <;> omega⟩
  let r : Fin 8 := ⟨if wk.1.val = 7 then 6 else wk.1.val + 1, by split <;> omega⟩
  have yd : absDiff wk.2.val y.val = 1 := by
    dsimp [y]; split <;> simp only [absDiff] <;> omega
  have ld : absDiff wk.1.val l.val = 1 := by
    dsimp [l]; split <;> simp only [absDiff] <;> omega
  have rd : absDiff wk.1.val r.val = 1 := by
    dsimp [r]; split <;> simp only [absDiff] <;> omega
  have a := cover (wk.1, y) (by simp only [dInf, absDiff] at yd ⊢; omega)
  have b := cover (l, y) (by simp only [dInf, absDiff] at yd ld ⊢; omega)
  have c := cover (r, y) (by simp only [dInf, absDiff] at yd rd ⊢; omega)
  clear cover escape yd ld rd
  by_cases y0 : wk.2.val = 0 <;> by_cases x0 : wk.1.val = 0 <;>
    by_cases x7 : wk.1.val = 7 <;>
    simp [dInf, absDiff, KQK.QueenRay, y, l, r,
      y0, x0, x7, sy, qy] at far adjacent a b c <;> omega

/-- Promotion either checks along the last rank or leaves an explicit legal escape. -/
theorem supported_white_geometry {sk qs wk : Square}
    (sy : sk.2.val = 6) (qy : qs.2.val = 7)
    (adjacent : absDiff sk.1.val qs.1.val = 1)
    (far : 2 ≤ dInf sk wk) (distinct : qs ≠ wk) :
    KQK.QueenSees qs wk sk wk ∨
      ∃ t, dInf wk t = 1 ∧ 2 ≤ dInf sk t ∧ t ≠ qs ∧ ¬ KQK.QueenSees qs t sk t := by
  by_cases top : wk.2.val = 7
  · left
    apply KQK.rook_sees_queen
    refine ⟨⟨?_, Or.inr (by omega)⟩, ?_, not_onSeg_end _ _⟩
    · intro equal
      exact distinct (Prod.ext (Fin.ext equal.1) (Fin.ext equal.2))
    · simp only [OnSeg]; omega
  · obtain ⟨t, step, safe, notRay⟩ := supported_white_escape sy qy adjacent far (by omega)
    right
    refine ⟨t, step, safe, ?_, fun sees => notRay (KQK.sees_ray sees)⟩
    intro same
    apply notRay
    exact Or.inl (by rw [same])

theorem supported_promotion_protected {σ : Colour} {sk ps : Square}
    (support : SupportedSeventh σ sk ps) : dInf sk (promotionSquare σ ps.1) = 1 := by
  obtain ⟨kingRank, _, files⟩ := support
  cases σ <;> simp only [height, promotionSquare, dInf, absDiff] at kingRank files ⊢ <;> omega

theorem supported_promotion_push {q : Position} {σ : Colour} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (support : SupportedSeventh σ sk ps)
    (far : 2 ≤ dInf sk wk) : Push q σ ps (promotionSquare σ ps.1) := by
  have protect := supported_promotion_protected support
  have notKing : promotionSquare σ ps.1 ≠ sk := by
    intro same; rw [same, (dInf_eq_zero_iff.mpr rfl)] at protect; cases protect
  have notPawn : promotionSquare σ ps.1 ≠ ps := by
    intro same
    have heightSame := congrArg (height σ) same
    rw [promotion_square_height, support.2.1] at heightSame
    cases heightSame
  have notWeak : promotionSquare σ ps.1 ≠ wk := by intro same; rw [same] at protect; omega
  refine ⟨by simp [dx, promotionSquare], ?_, Or.inl ?_⟩
  · rw [h.2.2.2]; exact LoneKing.board_none.mpr ⟨notKing, notPawn, notWeak⟩
  · have rank := support.2.1
    cases σ <;> simp only [height, dy, forward, promotionSquare] at rank ⊢ <;> omega

/-- Both-colour transport is used only for queen geometry, after promotion;
no pawn-rule symmetry is assumed. -/
theorem supported_promotion_geometry {σ : Colour} {sk ps wk : Square}
    (support : SupportedSeventh σ sk ps) (far : 2 ≤ dInf sk wk)
    (distinct : promotionSquare σ ps.1 ≠ wk) :
    KQK.QueenSees (promotionSquare σ ps.1) wk sk wk ∨
      ∃ t, dInf wk t = 1 ∧ 2 ≤ dInf sk t ∧ t ≠ promotionSquare σ ps.1 ∧
        ¬ KQK.QueenSees (promotionSquare σ ps.1) t sk t := by
  cases σ with
  | white =>
    exact supported_white_geometry support.1 rfl support.2.2 far distinct
  | black =>
    let g := KQK.reflectY
    have kingRank : (g.f sk).2.val = 6 := support.1
    have queenRank : (g.f (promotionSquare .black ps.1)).2.val = 7 := by rfl
    have files : absDiff (g.f sk).1.val (g.f (promotionSquare .black ps.1)).1.val = 1 := support.2.2
    have apart : 2 ≤ dInf (g.f sk) (g.f wk) := by rw [g.dInf_eq]; exact far
    have ne : g.f (promotionSquare .black ps.1) ≠ g.f wk := g.toBoardSym.ne_iff.mpr distinct
    rcases supported_white_geometry kingRank queenRank files apart ne with check |
        ⟨u, step, safe, notQueen, noCheck⟩
    · exact Or.inl ((g.sees_iff _ _ _ _).mp check)
    · right
      refine ⟨g.f u, ?_, ?_, ?_, ?_⟩
      · have equality := g.dInf_eq (g.f wk) u
        rw [g.invol] at equality
        exact equality.trans step
      · have equality := g.dInf_eq (g.f sk) u
        rw [g.invol] at equality
        omega
      · intro same
        have equality := congrArg g.f same
        rw [g.invol] at equality
        exact notQueen equality
      · intro sees
        have reflected := (g.sees_iff _ _ _ _).mpr sees
        simp only [g.invol] at reflected
        exact noCheck reflected

/-- Exact promotion boundary for the supported seventh-rank region. -/
theorem supported_queen_successor_bound {q : Position} {σ : Colour} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (turn : q.turn = σ)
    (support : SupportedSeventh σ sk ps) (far : 2 ≤ dInf sk wk) :
    MateWithin σ 98 (play q (promote ps (promotionSquare σ ps.1) .queen)) := by
  have push := supported_promotion_push h support far
  have material := promotion_material h turn push .queen
  have nextTurn : (play q (promote ps (promotionSquare σ ps.1) .queen)).turn = σ.opp := by
    rw [play_turn, turn]
  have safe : LoneKing.Safe sk (promotionSquare σ ps.1) wk :=
    Or.inr (supported_promotion_protected support)
  rcases supported_promotion_geometry support far material.2.2.1 with check |
      ⟨t, step, apart, notQueen, notSeen⟩
  · by_cases moves : ∃ r, Legal (play q (promote ps (promotionSquare σ ps.1) .queen)) r
    · exact KQK.safe_weak_entry_bound material nextTurn safe moves
    · have mate : MatedK (play q (promote ps (promotionSquare σ ps.1) .queen)) := by
        refine ⟨?_, moves⟩
        rw [nextTurn]
        exact (KQK.weak_check material).mpr (Or.inr check)
      exact mateWithin_mono (show MateWithin σ 0 _ from ⟨nextTurn, mate⟩) (by decide)
  · obtain ⟨r, legal, _⟩ := KQK.weak_move material nextTurn step notQueen apart notSeen
    exact KQK.safe_weak_entry_bound material nextTurn safe ⟨r, legal⟩

theorem supported_strong_bound {q : Position} {σ : Colour} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (turn : q.turn = σ)
    (support : SupportedSeventh σ sk ps) (far : 2 ≤ dInf sk wk) : MateWithin σ 99 q := by
  have push := supported_promotion_push h support far
  have last : (promotionSquare σ ps.1).2.val = lastRank σ := by cases σ <;> rfl
  exact choose_bound turn ⟨_, promotion_legal h turn far push last .queen, rfl⟩
    (supported_queen_successor_bound h turn support far)

theorem fresh_supported_strong {q : Position} {σ : Colour} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk) (turn : q.turn = σ)
    (support : SupportedSeventh σ sk ps) : FreshGame.Within σ 99 (FreshGame.fresh q) :=
  FreshGame.fresh_sub100 (supported_strong_bound h turn support fresh.kings) (by decide)

theorem supported_pawn_protected {σ : Colour} {sk ps : Square}
    (support : SupportedSeventh σ sk ps) : dInf sk ps = 1 := by
  obtain ⟨kingRank, pawnRank, files⟩ := support
  cases σ <;> simp only [height, dInf, absDiff] at kingRank pawnRank files ⊢ <;> omega

theorem seventh_pawn_attack_near_promotion {σ : Colour} {ps t : Square}
    (rank : height σ ps = 6) (attack : PawnSees σ ps t) :
    dInf (promotionSquare σ ps.1) t = 1 := by
  cases σ <;>
    simp only [height, PawnSees, dx, dy, forward, dInf, absDiff, promotionSquare] at rank attack ⊢ <;>
    omega

theorem supported_below_escape {σ : Colour} {sk ps wk : Square}
    (support : SupportedSeventh σ sk ps) (far : 2 ≤ dInf sk wk)
    (below : height σ wk ≤ 6) :
    ∃ t, dInf wk t = 1 ∧ 2 ≤ dInf sk t ∧ t ≠ ps ∧ ¬ PawnSees σ ps t := by
  have geometry : ∃ t, dInf wk t = 1 ∧ 2 ≤ dInf sk t ∧
      ¬ KQK.QueenSees (promotionSquare σ ps.1) t sk t := by
    cases σ with
    | white =>
      obtain ⟨t, step, safe, notRay⟩ := supported_white_escape
        (qs := promotionSquare .white ps.1) support.1 rfl support.2.2 far below
      exact ⟨t, step, safe, fun seen => notRay (KQK.sees_ray seen)⟩
    | black =>
      let g := KQK.reflectY
      have kingRank : (g.f sk).2.val = 6 := support.1
      have queenRank : (g.f (promotionSquare .black ps.1)).2.val = 7 := by rfl
      have files : absDiff (g.f sk).1.val (g.f (promotionSquare .black ps.1)).1.val = 1 := support.2.2
      have apart : 2 ≤ dInf (g.f sk) (g.f wk) := by rw [g.dInf_eq]; exact far
      obtain ⟨u, step, safe, notRay⟩ := supported_white_escape kingRank queenRank files apart below
      refine ⟨g.f u, ?_, ?_, ?_⟩
      · have equality := g.dInf_eq (g.f wk) u
        rw [g.invol] at equality
        exact equality.trans step
      · have equality := g.dInf_eq (g.f sk) u
        rw [g.invol] at equality
        omega
      · intro seen
        have reflected := (g.sees_iff _ _ _ _).mpr seen
        simp only [g.invol] at reflected
        exact notRay (KQK.sees_ray reflected)
  obtain ⟨t, step, safe, notSeen⟩ := geometry
  refine ⟨t, step, safe, ?_, ?_⟩
  · intro same
    apply notSeen
    apply KQK.near_sees
    rw [same]
    have rank := support.2.1
    cases σ <;> simp only [height, dInf, absDiff, promotionSquare] at rank ⊢ <;> omega
  · intro attack
    exact notSeen (KQK.near_sees (seventh_pawn_attack_near_promotion support.2.1 attack))

theorem supported_weak_has_move {q : Position} {σ : Colour} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (turn : q.turn = σ.opp)
    (support : SupportedSeventh σ sk ps) (far : 2 ≤ dInf sk wk) : ∃ r, Legal q r := by
  by_cases top : height σ wk = 7
  · let t : Square := (wk.1, ps.2)
    have step : dInf wk t = 1 := by
      have pawnRank := support.2.1
      cases σ <;> simp only [height, dInf, absDiff, t] at top pawnRank ⊢ <;> omega
    have apart : 2 ≤ dInf sk t := by
      have kingRank := support.1
      have pawnRank := support.2.1
      cases σ <;> simp only [height, dInf, absDiff, t] at far kingRank pawnRank top ⊢ <;> omega
    have notPawn : t ≠ ps := by
      intro same
      have protect := supported_pawn_protected support
      rw [same] at apart
      omega
    have notAttack : ¬ PawnSees σ ps t := by
      cases σ <;> simp [PawnSees, dy, forward, t]
    obtain ⟨r, legal, _⟩ := weak_move h turn step notPawn apart notAttack
    exact ⟨r, legal⟩
  · have bound := height_le σ wk
    obtain ⟨t, step, apart, notPawn, notAttack⟩ := supported_below_escape support far (by omega)
    obtain ⟨r, legal, _⟩ := weak_move h turn step notPawn apart notAttack
    exact ⟨r, legal⟩

theorem supported_weak_reply {q r : Position} {σ : Colour} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (turn : q.turn = σ.opp)
    (support : SupportedSeventh σ sk ps) (legal : Legal q r) :
    ∃ t, IsKPK r σ sk ps t ∧ r.turn = σ ∧ 2 ≤ dInf sk t := by
  obtain ⟨t, material, nextTurn, _⟩ := LoneKing.safe_reply h turn
    (Or.inr (supported_pawn_protected support)) legal
  exact ⟨t, material, nextTurn, LoneKing.kings_apart_after (by decide) material legal⟩

theorem supported_weak_bound {q : Position} {σ : Colour} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (turn : q.turn = σ.opp)
    (support : SupportedSeventh σ sk ps) (far : 2 ≤ dInf sk wk) : MateWithin σ 100 q := by
  have moves := supported_weak_has_move h turn support far
  have all : ∀ r, Legal q r → MateWithin σ 99 r := by
    intro r legal
    obtain ⟨t, material, nextTurn, apart⟩ := supported_weak_reply h turn support legal
    exact supported_strong_bound material nextTurn support apart
  have live : ¬ DeadK q := by
    obtain ⟨r, legal⟩ := moves
    obtain ⟨t, reach, goal⟩ := mateWithin_sound (all r legal)
    exact fun dead => dead ⟨t, reachK_cons legal reach, goal.2⟩
  exact Or.inr ⟨live, Or.inr ⟨turn, moves, all⟩⟩

end EndgameChess.Rules.KPK
