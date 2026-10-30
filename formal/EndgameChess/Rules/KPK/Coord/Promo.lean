import EndgameChess.Rules.KPK.Coord.Bridge

/-! Queen and rook promotion successors from linear coordinate certificates. -/
namespace EndgameChess.Rules.KPK.Coord
open EndgameChess.KK

/-- A lone-king step off the attacks of a promoted piece is legal. -/
theorem promoted_reply {k : PieceType} {q : Position} {σ : Colour} {sk xs wk t : Square}
    (hq : LoneKing.Material k q σ sk xs wk) (nk : k ≠ .king) (ht : q.turn = σ.opp)
    (hd : dInf wk t = 1) (htq : t ≠ xs) (hfar : 2 ≤ dInf sk t)
    (hn : attacksFrom (LoneKing.board k σ sk xs t) ⟨σ, k⟩ xs t = false) :
    ∃ r, Legal q r := by
  obtain ⟨h12, h13, h23, hb⟩ := hq
  let m : Move := ⟨wk, t, none⟩
  have hsrc : q.board m.src = some ⟨q.turn, .king⟩ := by
    rw [hb, ht]; exact LoneKing.board_wk h13 h23
  have hts : t ≠ sk := Ne.symm (ne_of_dInf_pos (by omega))
  have htw : t ≠ wk := Ne.symm (ne_of_dInf_pos (by omega))
  have hdst : q.board m.dst = none := by
    rw [hb]; exact LoneKing.board_none.mpr ⟨hts, htq, htw⟩
  have hp : isPseudo q m = true := by
    rw [isPseudo_of_king hsrc]
    have hg := kingGeom_iff.mpr hd
    simp [targetOK, hdst, hg, m]
  have hb' : (play q m).board = LoneKing.board k σ sk xs t := by
    rw [play_board_simple hsrc (by decide) rfl (fun _ => hd)]
    funext x
    show (if x = t then some ⟨q.turn, .king⟩ else if x = wk then none else q.board x) = _
    rw [hb, ht]; unfold LoneKing.board
    by_cases e1 : x = t
    · subst e1; simp [hts, htq]
    · by_cases e2 : x = wk
      · subst e2; simp [e1, Ne.symm h13, Ne.symm h23]
      · simp [e1, e2]
  have hm : LoneKing.Material k (play q m) σ sk xs t := ⟨h12, Ne.symm hts, Ne.symm htq, hb'⟩
  have hc : inCheck (play q m) q.turn = false := by
    rw [ht]
    cases he : inCheck (play q m) σ.opp
    · rfl
    · rcases (LoneKing.weak_check nk hm).mp he with hh | hh
      · omega
      · rw [hn] at hh; cases hh
  exact ⟨play q m, legal_of_pseudo hp hc⟩

theorem line_attack {k : PieceType} (hk : k = .queen ∨ k = .rook) {σ : Colour} {sk xs t : Square}
    (line : RookLine xs t) (clear : ¬ OnSeg xs sk t) :
    attacksFrom (LoneKing.board k σ sk xs t) ⟨σ, k⟩ xs t = true := by
  have between : isBetween xs sk t = false := by
    cases he : isBetween xs sk t
    · rfl
    · exact False.elim (clear ((isBetween_iff_onSeg line).mp he))
  have path : pathClear (LoneKing.board k σ sk xs t) xs t = true :=
    KQK.path_clear.mpr ⟨between, KQK.between_self _ _, KQK.between_end _ _⟩
  have geom := lineGeom_iff.mpr line
  rcases hk with rfl | rfl <;> simp [attacksFrom, geom, path]

theorem off_attack_queen {σ : Colour} {sk xs t : Square} (ray : ¬ KQK.QueenRay xs t) :
    attacksFrom (LoneKing.board .queen σ sk xs t) ⟨σ, .queen⟩ xs t = false := by
  cases he : attacksFrom (LoneKing.board .queen σ sk xs t) ⟨σ, .queen⟩ xs t
  · rfl
  · exact False.elim (ray (KQK.sees_ray (KQK.queen_attacks.mp he)))

theorem off_attack_rook {σ : Colour} {sk xs t : Square} (off : ¬ RookLine xs t) :
    attacksFrom (LoneKing.board .rook σ sk xs t) ⟨σ, .rook⟩ xs t = false := by
  cases he : attacksFrom (LoneKing.board .rook σ sk xs t) ⟨σ, .rook⟩ xs t
  · rfl
  · simp only [attacksFrom, Bool.and_eq_true] at he
    exact False.elim (off (lineGeom_iff.mp he.1))

theorem shield_attack {k : PieceType} (hk : k = .queen ∨ k = .rook) {σ : Colour}
    {sk xs t : Square} (line : RookLine xs t) (seg : OnSeg xs sk t) :
    attacksFrom (LoneKing.board k σ sk xs t) ⟨σ, k⟩ xs t = false := by
  have between := (isBetween_iff_onSeg line).mpr seg
  have blocked : pathClear (LoneKing.board k σ sk xs t) xs t = false := by
    cases he : pathClear (LoneKing.board k σ sk xs t) xs t
    · rfl
    · have clear := (KQK.path_clear.mp he).1
      rw [between] at clear; cases clear
  rcases hk with rfl | rfl <;> simp [attacksFrom, blocked]

/-- Oriented reading of a square standing on the promotion rank and file. -/
structure TopSquare (σ : Colour) (ps t : Square) : Prop where
  file : t.1 = ps.1
  rank : height σ t = 7

theorem top_mx {σ : Colour} {ps t : Square} (top : TopSquare σ ps t) : mx ps t = mx ps ps := by
  simp only [mx, top.file]

theorem queen_off {σ : Colour} {ps t u : Square} (top : TopSquare σ ps t)
    (off : OffQueen (mx ps ps) (mx ps u) (height σ u)) : ¬ KQK.QueenRay t u := by
  have rank := top.rank
  have file := congrArg Fin.val top.file
  have ub := u.1.isLt
  have uc := u.2.isLt
  have pb := ps.1.isLt
  cases σ <;> simp only [OffQueen, OffRook, mx, height, KQK.QueenRay] at off rank ⊢ <;>
    split at off <;> omega

theorem rook_off {σ : Colour} {ps t u : Square} (top : TopSquare σ ps t)
    (off : OffRook (mx ps ps) (mx ps u) (height σ u)) : ¬ RookLine t u := by
  have rank := top.rank
  have file := congrArg Fin.val top.file
  have ub := u.1.isLt
  have uc := u.2.isLt
  have pb := ps.1.isLt
  intro line
  have line2 := line.2
  cases σ <;> simp only [OffRook, mx, height] at off rank <;> split at off <;> omega

theorem rank_line {σ : Colour} {ps sk t wk : Square} (top : TopSquare σ ps t) (ne : t ≠ wk)
    (check : RankCheck (mx ps sk) (height σ sk) (mx ps ps) (mx ps wk) (height σ wk)) :
    RookLine t wk ∧ ¬ OnSeg t sk wk := by
  have rank := top.rank
  have file := congrArg Fin.val top.file
  have a1 := sk.1.isLt
  have a2 := sk.2.isLt
  have b1 := wk.1.isLt
  have b2 := wk.2.isLt
  have c1 := ps.1.isLt
  have e1 := t.2.isLt
  obtain ⟨high, clear⟩ := check
  refine ⟨⟨ne_iff_coords.mp ne, Or.inr ?_⟩, ?_⟩
  · apply Classical.byContradiction; intro no
    cases σ <;> simp only [height] at rank high <;> omega
  · intro seg
    apply clear
    simp only [mx, height, OnSeg] at *
    cases σ <;> simp only at * <;> split <;> split at * <;> omega

theorem file_line {σ : Colour} {ps sk t wk : Square} (top : TopSquare σ ps t) (ne : t ≠ wk)
    (check : FileCheck (mx ps sk) (height σ sk) (mx ps ps) (mx ps wk) (height σ wk)) :
    RookLine t wk ∧ ¬ OnSeg t sk wk := by
  have rank := top.rank
  have file := congrArg Fin.val top.file
  have a1 := sk.1.isLt
  have a2 := sk.2.isLt
  have b1 := wk.1.isLt
  have b2 := wk.2.isLt
  have c1 := ps.1.isLt
  have e1 := t.2.isLt
  obtain ⟨same, clear⟩ := check
  have sameFile : ps.1.val = wk.1.val := by
    simp only [mx] at same; split at same <;> omega
  refine ⟨⟨ne_iff_coords.mp ne, Or.inl (by omega)⟩, ?_⟩
  intro seg
  apply clear
  simp only [mx, height, OnSeg] at *
  cases σ <;> simp only at * <;> split <;> split at * <;> omega

theorem shield_line {σ : Colour} {ps sk t u : Square} (top : TopSquare σ ps t)
    (shield : Shielded (mx ps sk) (height σ sk) (mx ps ps) (mx ps u) (height σ u))
    (ne : t ≠ u) (free : t ≠ sk) : RookLine t u ∧ OnSeg t sk u := by
  have rank := top.rank
  have file := congrArg Fin.val top.file
  have a1 := sk.1.isLt
  have a2 := sk.2.isLt
  have b1 := u.1.isLt
  have b2 := u.2.isLt
  have c1 := ps.1.isLt
  have e1 := t.2.isLt
  obtain ⟨same1, same2, below⟩ := shield
  have uf : ps.1.val = u.1.val := by simp only [mx] at same1; split at same1 <;> omega
  have sf : ps.1.val = sk.1.val := by simp only [mx] at same2; split at same2 <;> omega
  have nf := ne_iff_coords.mp free
  refine ⟨⟨ne_iff_coords.mp ne, Or.inl (by omega)⟩, Or.inl ⟨by omega, by omega, ?_⟩⟩
  clear same1 same2
  cases σ <;> simp only [height] at rank below <;> omega

/-- The coordinate certificate supplies the exact successor criterion. -/
theorem promoted_good {q : Position} {σ : Colour} {sk ps wk t : Square} (k : PromoPiece)
    (hk : k = .queen ∨ k = .rook) (h : Cfg q σ sk ps wk) (turn : q.turn = σ)
    (push : Push q σ ps t) (top : TopSquare σ ps t)
    (safe : PieceSafe (mx ps sk) (height σ sk) (mx ps ps) (mx ps wk) (height σ wk))
    (good : RankCheck (mx ps sk) (height σ sk) (mx ps ps) (mx ps wk) (height σ wk) ∨
      FileCheck (mx ps sk) (height σ sk) (mx ps ps) (mx ps wk) (height σ wk) ∨
      ∃ x y, Near (mx ps wk) (height σ wk) x y ∧ x ≤ 7 ∧ y ≤ 7 ∧
        ¬ (x = mx ps ps ∧ y = 7) ∧ Apart (mx ps sk) (height σ sk) x y ∧
        ((match k with | .queen => OffQueen (mx ps ps) x y | _ => OffRook (mx ps ps) x y) ∨
          Shielded (mx ps sk) (height σ sk) (mx ps ps) x y)) :
    MatedK (play q (promote ps t k)) ∨
      (LoneKing.Safe sk t wk ∧ ∃ r, Legal (play q (promote ps t k)) r) := by
  have material := promotion_material h.material turn push k
  have nextTurn : (play q (promote ps t k)).turn = σ.opp := by rw [play_turn, turn]
  have nk : k.toKind ≠ .king := by rcases hk with rfl | rfl <;> decide
  have kk : k.toKind = .queen ∨ k.toKind = .rook := by rcases hk with rfl | rfl <;> simp [PromoPiece.toKind]
  have mt := top_mx top
  have rt := top.rank
  have neW : t ≠ wk := material.2.2.1
  have safeT : LoneKing.Safe sk t wk := by
    by_cases adjacent : dInf t wk = 1
    · right
      apply Classical.byContradiction
      intro notNear
      apply safe
      refine ⟨?_, ?_⟩
      · rw [← mt, ← rt]; rw [dInf_comm] at adjacent; exact (near_iff σ ps wk t).mp adjacent
      · intro near
        apply notNear
        rw [← mt, ← rt] at near
        exact (near_iff σ ps sk t).mpr near
    · left
      have zero : dInf t wk ≠ 0 := fun e => neW (dInf_eq_zero_iff.mp e)
      omega
  have check_case (seen : RookLine t wk ∧ ¬ OnSeg t sk wk) :
      MatedK (play q (promote ps t k)) ∨
        (LoneKing.Safe sk t wk ∧ ∃ r, Legal (play q (promote ps t k)) r) := by
    by_cases moves : ∃ r, Legal (play q (promote ps t k)) r
    · exact Or.inr ⟨safeT, moves⟩
    · left
      refine ⟨?_, moves⟩
      rw [nextTurn]
      exact (LoneKing.weak_check nk material).mpr (Or.inr (line_attack kk seen.1 seen.2))
  rcases good with rc | fc | ⟨x, y, near, hx, hy, notTop, apart, off⟩
  · exact check_case (rank_line top neW rc)
  · exact check_case (file_line top neW fc)
  · obtain ⟨u, rfl, rfl⟩ := exists_square σ ps hx hy
    have step := (near_iff σ ps wk u).mpr near
    have far := (apart_iff σ ps sk u).mpr apart
    have ne : u ≠ t := by
      intro same
      apply notTop
      rw [same, mt, rt]
      exact ⟨rfl, rfl⟩
    refine Or.inr ⟨safeT, ?_⟩
    have none : attacksFrom (LoneKing.board k.toKind σ sk t u) ⟨σ, k.toKind⟩ t u = false := by
      rcases off with off | shield
      · rcases hk with rfl | rfl
        · exact off_attack_queen (queen_off top off)
        · exact off_attack_rook (rook_off top off)
      · obtain ⟨line, seg⟩ := shield_line top shield ne.symm material.1.symm
        exact shield_attack kk line seg
    exact promoted_reply material nk nextTurn step ne far none

end EndgameChess.Rules.KPK.Coord
