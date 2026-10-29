import EndgameChess.Rules.KRKTwelveGlobal
import EndgameChess.Rules.KRKCastleTen

namespace EndgameChess.Rules.KRKCastleTwelve
open EndgameChess.KK KRKNativeFrame KRKFourPlyEscape
set_option maxHeartbeats 600000
set_option linter.unusedSimpArgs false

private def Pair (x r : Nat) : Prop :=
  (x = 2 ∧ r = 3) ∨ (x = 6 ∧ r = 5) ∨ (x = 5 ∧ r = 4) ∨ (x = 1 ∧ r = 2)

private def BorderPair (sk rs : Square) : Prop :=
  (((sk.1.val = 0 ∧ rs.1.val = 0) ∨ (sk.1.val = 7 ∧ rs.1.val = 7)) ∧ Pair sk.2.val rs.2.val) ∨
  (((sk.2.val = 0 ∧ rs.2.val = 0) ∨ (sk.2.val = 7 ∧ rs.2.val = 7)) ∧ Pair sk.1.val rs.1.val)

private theorem inner_pair_impossible {sk rs : Square} (boundary : BorderPair sk rs)
    (inner : KRKElevenInner.Eleven sk rs) : False := by
  dsimp [BorderPair,Pair] at boundary
  rcases inner with (⟨i,distance,apart,region⟩ | ⟨i,distance,apart,region⟩) |
    (⟨i,equal,condition⟩ | ⟨i,equal,condition⟩)
  all_goals
    cases i <;>
      dsimp [KRKElevenInner.king,KRKElevenInner.RookRegion,KRKElevenInner.RookCondition,
        KRKTenInner.Region,KRKTenInner.Horizontal,KRKTenInner.SideExtra,KRKTenInner.HighExtra,
        KRKEightInner.Horizontal,KRKNineNearStrip.RookCondition,symSwap,dInf,absDiff] at * <;>
      simp only [square_eq_iff,Fin.ext_iff] at * <;> omega

private theorem near_pair_impossible {sk rs : Square} (boundary : BorderPair sk rs)
    (near : KRKElevenNearStrip.Eleven sk rs) : False := by
  dsimp [BorderPair,Pair] at boundary
  rcases near with ⟨i,distance,apart,shape⟩ | ⟨i,equal,condition⟩
  all_goals
    cases i <;>
      dsimp [KRKElevenNearStrip.king,KRKElevenNearStrip.RookRegion,KRKElevenNearStrip.RookCondition,
        KRKElevenNearStrip.SideRow,KRKElevenNearStrip.SideFile,KRKNineNearStrip.RookCondition,dInf,absDiff] at * <;>
      simp only [square_eq_iff,Fin.ext_iff] at * <;> omega

private theorem mapped_border {sk rs wk : Square} (sy : sk.2.val = 0) (ry : rs.2.val = 0)
    (files : (sk.1.val = 2 ∧ rs.1.val = 3) ∨ (sk.1.val = 6 ∧ rs.1.val = 5)) :
    BorderPair ((KRKEightInteriorExact.stripFrame wk).f sk) ((KRKEightInteriorExact.stripFrame wk).f rs) := by
  rcases files with ⟨sx,rx⟩ | ⟨sx,rx⟩
  · have kingEq : sk = ((2 : Fin 8),0) := Prod.ext (Fin.ext sx) (Fin.ext sy)
    have rookEq : rs = ((3 : Fin 8),0) := Prod.ext (Fin.ext rx) (Fin.ext ry)
    rw [kingEq,rookEq]
    dsimp [KRKEightInteriorExact.stripFrame]
    split <;> (try split) <;> (try split) <;> (try split) <;>
      dsimp [BorderPair,Pair,Frame.ofSym,Frame.comp,symId,symX,symY,symXY,symSwap] <;> decide
  · have kingEq : sk = ((6 : Fin 8),0) := Prod.ext (Fin.ext sx) (Fin.ext sy)
    have rookEq : rs = ((5 : Fin 8),0) := Prod.ext (Fin.ext rx) (Fin.ext ry)
    rw [kingEq,rookEq]
    dsimp [KRKEightInteriorExact.stripFrame]
    split <;> (try split) <;> (try split) <;> (try split) <;>
      dsimp [BorderPair,Pair,Frame.ofSym,Frame.comp,symId,symX,symY,symXY,symSwap] <;> decide

theorem eleven_interior_impossible {sk rs wk : Square} (sy : sk.2.val = 0) (ry : rs.2.val = 0)
    (files : (sk.1.val = 2 ∧ rs.1.val = 3) ∨ (sk.1.val = 6 ∧ rs.1.val = 5))
    (distinct : sk ≠ rs) (notKing : sk ≠ wk) (notRook : rs ≠ wk)
    (far : 2 ≤ dInf sk wk) (notCheck : ¬RookSees rs wk sk wk)
    (inside : 0 < KRKEdgeDepth.depth wk) (clear : KRKElevenGeometry.Clear sk rs wk) : False := by
  have shallow := KRKTwelveGeometry.eleven_weak_depth clear
  have depth : KRKEdgeDepth.depth wk = 1 := by omega
  let g := KRKEightInteriorExact.stripFrame wk
  have spec := KRKEightInteriorExact.strip_spec depth
  change (g.f wk).1.val = 1 ∧ 1 ≤ (g.f wk).2.val ∧ (g.f wk).2.val ≤ 3 at spec
  have mapped := KRKElevenGeometry.frame_map g distinct notKing notRook far notCheck clear
  have mappedFar : 2 ≤ dInf (g.f sk) (g.f wk) := by rw [g.distance]; exact far
  have mappedCheck : ¬RookSees (g.f rs) (g.f wk) (g.f sk) (g.f wk) :=
    fun h => notCheck ((g.sees _ _ _ _).mp h)
  have ys : (g.f wk).2.val = 1 ∨ (g.f wk).2.val = 2 ∨ (g.f wk).2.val = 3 := by omega
  rcases ys with one | two | three
  · have target : g.f wk = ((1 : Fin 8),1) := Prod.ext (Fin.ext spec.1) (Fin.ext one)
    rw [target] at mapped mappedFar mappedCheck
    have inner := (KRKElevenInner.clear_iff (g.ne_iff.mpr distinct)
      (target ▸ g.ne_iff.mpr notKing) (target ▸ g.ne_iff.mpr notRook) mappedFar mappedCheck).mp mapped
    exact inner_pair_impossible (mapped_border sy ry files) inner
  · have target : g.f wk = ((1 : Fin 8),2) := Prod.ext (Fin.ext spec.1) (Fin.ext two)
    rw [target] at mapped mappedFar mappedCheck
    have near := (KRKElevenNearStrip.clear_iff (g.ne_iff.mpr distinct)
      (target ▸ g.ne_iff.mpr notRook)).mp mapped
    exact near_pair_impossible (mapped_border sy ry files) near
  · have target : g.f wk = ((1 : Fin 8),3) := Prod.ext (Fin.ext spec.1) (Fin.ext three)
    let q := krkPos .white (g.f sk) (g.f rs) (g.f wk) .white
    have material : IsKRK q .white (g.f sk) (g.f rs) (g.f wk) :=
      ⟨g.ne_iff.mpr distinct,g.ne_iff.mpr notKing,g.ne_iff.mpr notRook,rfl⟩
    have eleven := KRKElevenGeometry.sufficient material rfl mappedFar mappedCheck mapped
    exact KRKTenCentralStripHolding.strong_no_twelve material rfl
      (Or.inl ⟨Or.inl spec.1,by omega,by omega⟩) (mateWithin_mono eleven (by decide))

theorem interior_covered {sk rs wk t : Square} (sy : sk.2.val = 0) (ry : rs.2.val = 0)
    (files : (sk.1.val = 2 ∧ rs.1.val = 3) ∨ (sk.1.val = 6 ∧ rs.1.val = 5))
    (distinct : sk ≠ rs) (safe : SafeRook sk rs wk) (distance : dInf wk t = 1)
    (inside : 0 < KRKEdgeDepth.depth t)
    (every : ∀ u, StepM ⟨sk,rs,wk,false⟩ ⟨sk,rs,u,true⟩ → KRKElevenGeometry.Clear sk rs u) : Covered sk rs t := by
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
  exact False.elim (eleven_interior_impossible sy ry files distinct
    (ne_of_dInf_pos (by omega)) apart.symm (by omega) (fun sees => line sees.1) inside (every t step))

theorem king_bottom_no_twelve {sk rs wk : Square}
    (sx : sk.1.val = 6) (sy : sk.2.val = 0) (rx : rs.1.val = 5) (ry : rs.2.val = 0)
    (distinct : sk ≠ rs) (far : 2 ≤ dInf sk wk) (clear : KRKTwelveGeometry.Clear sk rs wk) : False := by
  have every : ∀ t, StepM ⟨sk,rs,wk,false⟩ ⟨sk,rs,t,true⟩ → KRKElevenGeometry.Clear sk rs t :=
    fun t step => clear.2.2 t (KRKCornerWeakBand.step_guard step)
  have rank := KRKCastleEight.rank_prison sy ry (by omega) (by omega) (fun t distance inside height =>
    interior_covered sy ry (by omega) distinct clear.1 distance inside every)
  have low : wk.1.val ≤ 4 := by simp only [dInf,absDiff,sx,sy,rank] at far; omega
  let x : Nat := if wk.1.val = 0 then 1 else if wk.1.val = 1 then 2 else wk.1.val
  have xb : 1 ≤ x ∧ x ≤ 4 ∧ x ≤ wk.1.val + 1 ∧ wk.1.val ≤ x + 1 := by
    dsimp [x]; split <;> (try split) <;> omega
  let t : Square := (⟨x,by omega⟩,1)
  have step : StepM ⟨sk,rs,wk,false⟩ ⟨sk,rs,t,true⟩ := by
    refine StepM.lone ?_ ?_ ?_ ?_ <;>
      simp only [t,dInf,absDiff,ne_iff_coords,RookSees,RookLine,OnSeg,sx,sy,rx,ry,rank] <;> omega
  have guard := KRKCornerWeakBand.step_guard step
  exact eleven_interior_impossible sy ry (by omega) distinct
    (ne_of_dInf_pos (by have := guard.2.2.1; omega)) guard.2.1.symm guard.2.2.1 guard.2.2.2
    (by dsimp [t,KRKEdgeDepth.depth]; omega) (every t step)

theorem queen_bottom_weak_corner {sk rs wk : Square}
    (sx : sk.1.val = 2) (sy : sk.2.val = 0) (rx : rs.1.val = 3) (ry : rs.2.val = 0)
    (distinct : sk ≠ rs) (far : 2 ≤ dInf sk wk) (clear : KRKTwelveGeometry.Clear sk rs wk) : wk = ((0 : Fin 8),0) := by
  have every : ∀ t, StepM ⟨sk,rs,wk,false⟩ ⟨sk,rs,t,true⟩ → KRKElevenGeometry.Clear sk rs t :=
    fun t step => clear.2.2 t (KRKCornerWeakBand.step_guard step)
  have rank := KRKCastleEight.rank_prison sy ry (by omega) (by omega) (fun t distance inside height =>
    interior_covered sy ry (by omega) distinct clear.1 distance inside every)
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
  have guard := KRKCornerWeakBand.step_guard step
  exact False.elim (eleven_interior_impossible sy ry (by omega) distinct
    (ne_of_dInf_pos (by have := guard.2.2.1; omega)) guard.2.1.symm guard.2.2.1 guard.2.2.2
    (by dsimp [t,KRKEdgeDepth.depth]; omega) (every t step))

theorem home_king_no_twelve {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp) (far : 2 ≤ dInf sk wk)
    (sx : sk.1.val = 6) (sy : sk.2 = homeRank σ) (rx : rs.1.val = 5) (ry : rs.2 = homeRank σ)
    (notMate : ¬MatedK q) (win : MateWithin σ 12 q) : False := by
  have clear := (KRKTwelveGeometry.kernel_twelve_iff material turn notMate).mp win
  cases σ with
  | white => exact king_bottom_no_twelve sx (congrArg Fin.val sy) rx (congrArg Fin.val ry) material.1 far clear
  | black =>
    have mapped := KRKTwelveGeometry.frame_map (Frame.ofSym symY) material.1 clear
    apply king_bottom_no_twelve (sk := symY.f sk) (rs := symY.f rs) (wk := symY.f wk)
      sx (by dsimp [symY]; have := congrArg Fin.val sy; change sk.2.val = 7 at this; omega)
      rx (by dsimp [symY]; have := congrArg Fin.val ry; change rs.2.val = 7 at this; omega)
      ((Frame.ofSym symY).ne_iff.mpr material.1) (by rwa [symY.dInf_eq]) mapped

theorem home_queen_weak_corner {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp) (far : 2 ≤ dInf sk wk)
    (sx : sk.1.val = 2) (sy : sk.2 = homeRank σ) (rx : rs.1.val = 3) (ry : rs.2 = homeRank σ)
    (notMate : ¬MatedK q) (win : MateWithin σ 12 q) : wk = ((0 : Fin 8),homeRank σ) := by
  have clear := (KRKTwelveGeometry.kernel_twelve_iff material turn notMate).mp win
  cases σ with
  | white => exact queen_bottom_weak_corner sx (congrArg Fin.val sy) rx (congrArg Fin.val ry) material.1 far clear
  | black =>
    have mapped := KRKTwelveGeometry.frame_map (Frame.ofSym symY) material.1 clear
    have corner := queen_bottom_weak_corner (sk := symY.f sk) (rs := symY.f rs) (wk := symY.f wk)
      sx (by dsimp [symY]; have := congrArg Fin.val sy; change sk.2.val = 7 at this; omega)
      rx (by dsimp [symY]; have := congrArg Fin.val ry; change rs.2.val = 7 at this; omega)
      ((Frame.ofSym symY).ne_iff.mpr material.1) (by rwa [symY.dInf_eq]) mapped
    have file := congrArg (fun t : Square => t.1.val) corner
    have rank := congrArg (fun t : Square => t.2.val) corner
    apply Prod.ext <;> apply Fin.ext
    · simpa only [symY] using file
    · dsimp [symY] at rank
      change wk.2.val = 7
      omega

/-- Both actual castling directions and colours are excluded as nonmating
entries into a twelve-ply weak win. Native rights remain in the hypotheses. -/
theorem castle_not_twelve {q : Position} {σ : Colour} {sk rs wk ns nr : Square}
    {m : Move} (material : IsKRK q σ sk rs wk) (turn : q.turn = σ)
    (legal : isLegal q m = true) (notMate : ¬MatedK (play q m))
    (src : m.src = sk) (castle : canCastle q m = true)
    (next : IsKRK (play q m) σ ns nr wk) : ¬MateWithin σ 12 (play q m) := by
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
    exact home_king_no_twelve actualNext (by rw [play_turn,turn])
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
    (turn : (RawHistoryLayer.erase s).turn = σ) (high : 86 ≤ RawClock.clock s.val.trace)
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
  have budget : KRKDeadline.budget σ t ≤ 13 := by
    simp only [KRKDeadline.budget,notStrong,↓reduceIte]
    omega
  have ten := KRKTwelveGeometry.weak_thirteen_twelve nextT nextTurn (mateWithin_mono deadline budget)
  rw [boardEq] at ten notMate
  intro castle
  exact castle_not_twelve material turn legal notMate src castle next ten

end EndgameChess.Rules.KRKCastleTwelve
