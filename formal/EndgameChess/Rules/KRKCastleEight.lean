import EndgameChess.Rules.KRKEightGeometry
import EndgameChess.Rules.KRKSevenReach

namespace EndgameChess.Rules.KRKCastleEight
open EndgameChess.KK KRKNativeFrame KRKFourPlyEscape
set_option maxHeartbeats 400000

theorem seven_bottom_interior {sk rs wk : Square} (sy : sk.2.val = 0)
    (inside : 0 < KRKEdgeDepth.depth wk) (clear : KRKSevenGeometry.Clear sk rs wk) : wk.2.val = 1 := by
  have data := KRKSevenReach.interior_king_near inside clear
  simp only [KRKSixInterior.InnerCorner,dInf,absDiff,sy] at data
  omega

theorem above_covered {sk rs wk t : Square} (sy : sk.2.val = 0) (safe : SafeRook sk rs wk)
    (distance : dInf wk t = 1) (inside : 0 < KRKEdgeDepth.depth t) (height : 2 ≤ t.2.val)
    (every : ∀ u, StepM ⟨sk,rs,wk,false⟩ ⟨sk,rs,u,true⟩ → KRKSevenGeometry.Clear sk rs u) : Covered sk rs t := by
  by_cases king : dInf sk t ≤ 1
  · exact Or.inl king
  by_cases line : RookLine rs t
  · exact Or.inr line
  have apart : t ≠ rs := by
    intro equal
    rcases safe with distant | guarded
    · rw [equal,dInf_comm] at distance; omega
    · rw [equal] at king; omega
  have step : StepM ⟨sk,rs,wk,false⟩ ⟨sk,rs,t,true⟩ :=
    StepM.lone distance apart (by omega) (fun sees => line sees.1)
  have rank := seven_bottom_interior sy inside (every t step)
  omega

theorem rank_prison {sk rs wk : Square} (sy : sk.2.val = 0) (ry : rs.2.val = 0)
    (low : 2 ≤ rs.1.val) (high : rs.1.val ≤ 5)
    (cover : ∀ t, dInf wk t = 1 → 0 < KRKEdgeDepth.depth t → 2 ≤ t.2.val → Covered sk rs t) : wk.2.val = 0 := by
  by_cases bottom : wk.2.val = 0
  · exact bottom
  let x : Nat := if wk.1.val = 0 then 1 else if wk.1.val = 7 then 6
    else if wk.1.val = rs.1.val then rs.1.val - 1 else wk.1.val
  let y : Nat := if wk.2.val ≤ 5 then wk.2.val + 1 else wk.2.val - 1
  have xb : 1 ≤ x ∧ x ≤ 6 ∧ x ≠ rs.1.val ∧ x ≤ wk.1.val + 1 ∧ wk.1.val ≤ x + 1 := by
    dsimp [x]; split <;> (try split) <;> (try split) <;> omega
  have yb : 2 ≤ y ∧ y ≤ 6 ∧ (y + 1 = wk.2.val ∨ wk.2.val + 1 = y) := by
    dsimp [y]; split <;> omega
  let t : Square := (⟨x,by omega⟩,⟨y,by omega⟩)
  have distance : dInf wk t = 1 := by dsimp [t,dInf,absDiff]; omega
  have inside : 0 < KRKEdgeDepth.depth t := by dsimp [t,KRKEdgeDepth.depth]; omega
  have covered := covered_box (cover t distance inside (by dsimp [t]; exact yb.1))
  dsimp [t] at covered
  omega

theorem king_bottom_no_eight {sk rs wk : Square}
    (sx : sk.1.val = 6) (sy : sk.2.val = 0) (rx : rs.1.val = 5) (ry : rs.2.val = 0)
    (far : 2 ≤ dInf sk wk) (clear : KRKEightGeometry.Clear sk rs wk) : False := by
  have every : ∀ t, StepM ⟨sk,rs,wk,false⟩ ⟨sk,rs,t,true⟩ → KRKSevenGeometry.Clear sk rs t :=
    fun t step => clear.2.2 t (KRKCornerWeakBand.step_guard step)
  have rank := rank_prison sy ry (by omega) (by omega) (fun t distance inside height =>
    above_covered sy clear.1 distance inside height every)
  have low : wk.1.val ≤ 4 := by simp only [dInf,absDiff,sx,sy,rank] at far; omega
  let x : Nat := if wk.1.val = 0 then 1 else if wk.1.val = 1 then 2 else wk.1.val
  have xb : 1 ≤ x ∧ x ≤ 4 ∧ x ≤ wk.1.val + 1 ∧ wk.1.val ≤ x + 1 := by
    dsimp [x]; split <;> (try split) <;> omega
  let t : Square := (⟨x,by omega⟩,1)
  have step : StepM ⟨sk,rs,wk,false⟩ ⟨sk,rs,t,true⟩ := by
    refine StepM.lone ?_ ?_ ?_ ?_ <;>
      simp only [t,dInf,absDiff,ne_iff_coords,RookSees,RookLine,OnSeg,sx,sy,rx,ry,rank] <;> omega
  have data := KRKSevenReach.interior_king_near (wk := t)
    (by dsimp [t,KRKEdgeDepth.depth]; omega) (every t step)
  simp only [KRKSixInterior.InnerCorner,t,dInf,absDiff,sx,sy] at data
  omega

theorem queen_bottom_weak_corner {sk rs wk : Square}
    (sx : sk.1.val = 2) (sy : sk.2.val = 0) (rx : rs.1.val = 3) (ry : rs.2.val = 0)
    (far : 2 ≤ dInf sk wk) (clear : KRKEightGeometry.Clear sk rs wk) : wk = ((0 : Fin 8),0) := by
  have every : ∀ t, StepM ⟨sk,rs,wk,false⟩ ⟨sk,rs,t,true⟩ → KRKSevenGeometry.Clear sk rs t :=
    fun t step => clear.2.2 t (KRKCornerWeakBand.step_guard step)
  have rank := rank_prison sy ry (by omega) (by omega) (fun t distance inside height =>
    above_covered sy clear.1 distance inside height every)
  by_cases left : wk.1.val = 0
  · exact Prod.ext (Fin.ext left) (Fin.ext rank)
  have low : 4 ≤ wk.1.val := by simp only [dInf,absDiff,sx,sy,rank] at far; omega
  let x : Nat := if wk.1.val = 7 then 6 else wk.1.val
  have xb : 4 ≤ x ∧ x ≤ 6 ∧ x ≤ wk.1.val + 1 ∧ wk.1.val ≤ x + 1 := by
    dsimp [x]; split <;> omega
  let t : Square := (⟨x,by omega⟩,1)
  have step : StepM ⟨sk,rs,wk,false⟩ ⟨sk,rs,t,true⟩ := by
    refine StepM.lone ?_ ?_ ?_ ?_ <;>
      simp only [t,dInf,absDiff,ne_iff_coords,RookSees,RookLine,OnSeg,sx,sy,rx,ry,rank] <;> omega
  have data := KRKSevenReach.interior_king_near (wk := t)
    (by dsimp [t,KRKEdgeDepth.depth]; omega) (every t step)
  simp only [KRKSixInterior.InnerCorner,t,dInf,absDiff,sx,sy] at data
  omega

theorem frame_map (g : Frame) {sk rs wk : Square} (distinct : sk ≠ rs)
    (clear : KRKEightGeometry.Clear sk rs wk) : KRKEightGeometry.Clear (g.f sk) (g.f rs) (g.f wk) := by
  obtain ⟨safe,⟨t,guard⟩,all⟩ := clear
  have mappedSafe : SafeRook (g.f sk) (g.f rs) (g.f wk) := by simpa only [SafeRook,g.distance] using safe
  have step : StepM ⟨sk,rs,wk,false⟩ ⟨sk,rs,t,true⟩ := StepM.lone guard.1 guard.2.1 guard.2.2.1 guard.2.2.2
  refine ⟨mappedSafe,⟨g.f t,KRKCornerWeakBand.step_guard (g.map_step step)⟩,?_⟩
  intro u next
  have back := g.inverse.map_step (StepM.lone next.1 next.2.1 next.2.2.1 next.2.2.2)
  change StepM ⟨g.r (g.f sk),g.r (g.f rs),g.r (g.f wk),false⟩
    ⟨g.r (g.f sk),g.r (g.f rs),g.r u,true⟩ at back
  simp only [g.left_inv] at back
  have guardBack := KRKCornerWeakBand.step_guard back
  have far := guardBack.2.2.1
  have mapped := KRKSevenReach.frame_map g distinct (ne_of_dInf_pos (by omega)) guardBack.2.1.symm
    far guardBack.2.2.2 (all _ guardBack)
  simpa only [g.right_inv] using mapped

theorem home_king_no_eight {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp) (far : 2 ≤ dInf sk wk)
    (sx : sk.1.val = 6) (sy : sk.2 = homeRank σ) (rx : rs.1.val = 5) (ry : rs.2 = homeRank σ)
    (notMate : ¬MatedK q) (win : MateWithin σ 8 q) : False := by
  have clear := (KRKEightGeometry.kernel_eight_iff material turn notMate).mp win
  cases σ with
  | white => exact king_bottom_no_eight sx (congrArg Fin.val sy) rx (congrArg Fin.val ry) far clear
  | black =>
    have mapped := frame_map (Frame.ofSym symY) material.1 clear
    apply king_bottom_no_eight (sk := symY.f sk) (rs := symY.f rs) (wk := symY.f wk)
      sx (by dsimp [symY]; have := congrArg Fin.val sy; change sk.2.val = 7 at this; omega)
      rx (by dsimp [symY]; have := congrArg Fin.val ry; change rs.2.val = 7 at this; omega)
      (by rwa [symY.dInf_eq]) mapped

theorem home_queen_weak_corner {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp) (far : 2 ≤ dInf sk wk)
    (sx : sk.1.val = 2) (sy : sk.2 = homeRank σ) (rx : rs.1.val = 3) (ry : rs.2 = homeRank σ)
    (notMate : ¬MatedK q) (win : MateWithin σ 8 q) : wk = ((0 : Fin 8),homeRank σ) := by
  have clear := (KRKEightGeometry.kernel_eight_iff material turn notMate).mp win
  cases σ with
  | white => exact queen_bottom_weak_corner sx (congrArg Fin.val sy) rx (congrArg Fin.val ry) far clear
  | black =>
    have mapped := frame_map (Frame.ofSym symY) material.1 clear
    have corner := queen_bottom_weak_corner (sk := symY.f sk) (rs := symY.f rs) (wk := symY.f wk)
      sx (by dsimp [symY]; have := congrArg Fin.val sy; change sk.2.val = 7 at this; omega)
      rx (by dsimp [symY]; have := congrArg Fin.val ry; change rs.2.val = 7 at this; omega)
      (by rwa [symY.dInf_eq]) mapped
    have file := congrArg (fun t : Square => t.1.val) corner
    have rank := congrArg (fun t : Square => t.2.val) corner
    apply Prod.ext <;> apply Fin.ext
    · simpa only [symY] using file
    · dsimp [symY] at rank
      change wk.2.val = 7
      omega

/-- Both actual castling directions and colours are excluded as nonmating
entries into an eight-ply weak win. Native rights remain in the hypotheses. -/
theorem castle_not_eight {q : Position} {σ : Colour} {sk rs wk ns nr : Square}
    {m : Move} (material : IsKRK q σ sk rs wk) (turn : q.turn = σ)
    (legal : isLegal q m = true) (notMate : ¬MatedK (play q m))
    (src : m.src = sk) (castle : canCastle q m = true)
    (next : IsKRK (play q m) σ ns nr wk) : ¬MateWithin σ 8 (play q m) := by
  have source : q.board m.src = some ⟨σ, .king⟩ := by
    rw [src,material.2.2.2]; exact krkBoard_sk
  intro win
  have actual := castle
  simp only [canCastle,turn,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq,Option.isNone_iff_eq_none] at actual
  rcases actual with ⟨⟨⟨start,row⟩,promo⟩,king | queen⟩
  · have dest : m.dst = ((6 : Fin 8),homeRank σ) := Prod.ext king.1.1.1.1.1.1.1 row
    have move : m = ⟨((4 : Fin 8),homeRank σ),((6 : Fin 8),homeRank σ),none⟩ := by
      cases m; simp only [Move.mk.injEq]; exact ⟨start,dest,promo⟩
    rw [start] at source
    have nsEq := KRKCastleFour.king_square next (t := ((6 : Fin 8),homeRank σ))
      (by rw [move]; simp [play,turn,source])
    have nrEq := KRKCastleFour.rook_square next (t := ((5 : Fin 8),homeRank σ))
      (by rw [move]; simp [play,turn,source])
    have actualNext : IsKRK (play q m) σ ((6 : Fin 8),homeRank σ) ((5 : Fin 8),homeRank σ) wk := by
      simpa only [←nsEq,←nrEq] using next
    exact home_king_no_eight actualNext (by rw [play_turn,turn])
      (KRKEdgeDepth.arrival_far ⟨m,legal,rfl⟩ actualNext) rfl rfl rfl rfl notMate win
  · have dest : m.dst = ((2 : Fin 8),homeRank σ) := Prod.ext queen.1.1.1.1.1.1.1.1 row
    have move : m = ⟨((4 : Fin 8),homeRank σ),((2 : Fin 8),homeRank σ),none⟩ := by
      cases m; simp only [Move.mk.injEq]; exact ⟨start,dest,promo⟩
    rw [start] at source
    have nsEq := KRKCastleFour.king_square next (t := ((2 : Fin 8),homeRank σ))
      (by rw [move]; simp [play,turn,source])
    have nrEq := KRKCastleFour.rook_square next (t := ((3 : Fin 8),homeRank σ))
      (by rw [move]; simp [play,turn,source])
    have actualNext : IsKRK (play q m) σ ((2 : Fin 8),homeRank σ) ((3 : Fin 8),homeRank σ) wk := by
      simpa only [←nsEq,←nrEq] using next
    have weakAt := home_queen_weak_corner actualNext (by rw [play_turn,turn])
      (KRKEdgeDepth.arrival_far ⟨m,legal,rfl⟩ actualNext) rfl rfl rfl rfl notMate win
    have rookAt : q.board ((0 : Fin 8),homeRank σ) = some ⟨σ,.rook⟩ := queen.1.1.1.1.1.1.2
    have weak : q.board wk = some ⟨σ.opp,.king⟩ := by
      rw [material.2.2.2]; exact krkBoard_wk material.2.1 material.2.2.1
    rw [weakAt,rookAt] at weak
    have impossible := congrArg (fun p : Option Piece => p.map Piece.kind) weak
    cases impossible

theorem winning_entry_not_castle {s t : RawHistoryLayer.State} {σ : Colour} {sk rs wk : Square} {m : Move}
    (material : IsKRK (RawHistoryLayer.erase s) σ sk rs wk)
    (turn : (RawHistoryLayer.erase s).turn = σ) (high : 90 ≤ RawClock.clock s.val.trace)
    (legal : isLegal (RawHistoryLayer.erase s) m = true)
    (endpoint : t.val = RawTrace.append s.val m legal) (src : m.src = sk)
    (notMate : ¬MatedK (RawHistoryLayer.erase t)) (win : KRKHolding.F σ t) :
    canCastle (RawHistoryLayer.erase s) m ≠ true := by
  obtain ⟨_,clock⟩ := KRKHighClock.winning_child_quiet material ⟨m,legal,endpoint⟩ win
  have boardEq : RawHistoryLayer.erase t = play (RawHistoryLayer.erase s) m := congrArg RawTrace.erase endpoint
  obtain ⟨ns,nr,next⟩ := krk_strong_material material turn legal
  have nextT : IsKRK (RawHistoryLayer.erase t) σ ns nr wk := by rwa [boardEq]
  have nextTurn : (RawHistoryLayer.erase t).turn = σ.opp := by rw [boardEq,play_turn,turn]
  have notStrong : (RawHistoryLayer.erase t).turn ≠ σ := fun h => opp_ne σ (h.symm.trans nextTurn)
  have deadline := (KRKDeadline.winning_deadline nextT win).2
  have budget : KRKDeadline.budget σ t ≤ 9 := by
    simp only [KRKDeadline.budget,notStrong,↓reduceIte]
    omega
  have eight := KRKEightGeometry.weak_nine_eight nextT nextTurn (mateWithin_mono deadline budget)
  rw [boardEq] at eight notMate
  intro castle
  exact castle_not_eight material turn legal notMate src castle next eight

end EndgameChess.Rules.KRKCastleEight

