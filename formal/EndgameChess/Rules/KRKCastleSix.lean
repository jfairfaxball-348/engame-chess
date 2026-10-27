import EndgameChess.Rules.KRKSixGeometry

namespace EndgameChess.Rules.KRKCastleSix
open EndgameChess.KK KRKFourPlyEscape KRKFiveGeometry
set_option maxHeartbeats 500000

theorem five_depth_zero {sk rs wk : Square} (clear : Clear sk rs wk) : KRKEdgeDepth.depth wk = 0 := by
  rcases clear with immediate | ⟨depth,_⟩
  · exact three_depth_zero (Or.inl immediate)
  · exact depth

theorem interior_covered {sk rs wk t : Square} (safe : SafeRook sk rs wk)
    (distance : dInf wk t = 1) (inside : 0 < KRKEdgeDepth.depth t)
    (every : ∀ u, StepM ⟨sk,rs,wk,false⟩ ⟨sk,rs,u,true⟩ → Clear sk rs u) : Covered sk rs t := by
  by_cases king : dInf sk t ≤ 1
  · exact Or.inl king
  by_cases line : RookLine rs t
  · exact Or.inr line
  have apart : t ≠ rs := by
    intro equal
    rcases safe with distant | guarded
    · rw [equal,dInf_comm] at distance; omega
    · rw [equal] at king; omega
  have step : StepM ⟨sk,rs,wk,false⟩ ⟨sk,rs,t,true⟩ := StepM.lone distance apart (by omega) (fun sees => line sees.1)
  have zero := five_depth_zero (every t step)
  omega

/-- A king and rook on rank zero, with the rook on an interior file,
cannot cover every interior neighbour of a weak king on another rank. -/
theorem rank_prison {sk rs wk : Square} (sy : sk.2.val = 0) (ry : rs.2.val = 0)
    (low : 2 ≤ rs.1.val) (high : rs.1.val ≤ 5)
    (cover : ∀ t, dInf wk t = 1 → 0 < KRKEdgeDepth.depth t → Covered sk rs t) : wk.2.val = 0 := by
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
  have covered := covered_box (cover t distance inside)
  dsimp [t] at covered
  omega


/-- With an interior-file rook on the king's home edge, covering all inward
replies forces a corner weak king and the opposing king two files away. -/
theorem corner_prison {sk rs wk : Square} (sy : sk.2.val = 0) (ry : rs.2.val = 0)
    (low : 2 ≤ rs.1.val) (high : rs.1.val ≤ 5) (far : 2 ≤ dInf sk wk)
    (cover : ∀ t, dInf wk t = 1 → 0 < KRKEdgeDepth.depth t → Covered sk rs t) :
    (wk.1.val = 0 ∧ sk.1.val = 2) ∨ (wk.1.val = 7 ∧ sk.1.val = 5) := by
  have rank := rank_prison sy ry low high cover
  have boundary : wk.1.val = 0 ∨ wk.1.val = 7 := by
    by_cases left : wk.1.val = 0
    · exact Or.inl left
    by_cases right : wk.1.val = 7
    · exact Or.inr right
    have xl : 1 ≤ wk.1.val := by omega
    have xh : wk.1.val ≤ 6 := by omega
    by_cases same : wk.1.val = rs.1.val
    · let x : Nat := if sk.1.val ≤ wk.1.val then wk.1.val + 1 else wk.1.val - 1
      have xb : 1 ≤ x ∧ x ≤ 6 ∧ x ≠ rs.1.val ∧
          (sk.1.val + 2 ≤ x ∨ x + 2 ≤ sk.1.val) := by
        dsimp [x]; split <;> simp only [dInf,absDiff,sy,rank] at far <;> omega
      let t : Square := (⟨x,by omega⟩,1)
      have distance : dInf wk t = 1 := by dsimp [t,x,dInf,absDiff]; split <;> omega
      have inside : 0 < KRKEdgeDepth.depth t := by dsimp [t,KRKEdgeDepth.depth]; omega
      have covered := covered_box (cover t distance inside)
      dsimp [t] at covered
      omega
    · have distance : dInf wk (wk.1,1) = 1 := by simp [dInf,absDiff,rank]
      have inside : 0 < KRKEdgeDepth.depth (wk.1,1) := by dsimp [KRKEdgeDepth.depth]; omega
      have covered := covered_box (cover (wk.1,1) distance inside)
      dsimp only at covered
      simp only [dInf,absDiff,sy,rank] at far
      omega
  rcases boundary with left | right
  · have covered := covered_box (cover ((1 : Fin 8),1)
      (by simp [dInf,absDiff,left,rank]) (by decide))
    simp only [dInf,absDiff,sy,rank,left] at far
    exact Or.inl ⟨left,by dsimp only at covered; omega⟩
  · have covered := covered_box (cover ((6 : Fin 8),1)
      (by simp [dInf,absDiff,right,rank] <;> omega) (by decide))
    simp only [dInf,absDiff,sy,rank,right] at far
    exact Or.inr ⟨right,by dsimp only at covered; omega⟩


theorem cover_flip {sk rs wk : Square}
    (cover : ∀ t, dInf wk t = 1 → 0 < KRKEdgeDepth.depth t → Covered sk rs t) :
    ∀ t, dInf (symY.f wk) t = 1 → 0 < KRKEdgeDepth.depth t → Covered (symY.f sk) (symY.f rs) t := by
  intro t distance inside
  have backDistance : dInf wk (symY.f t) = 1 := by
    simpa only [symY.invol] using (symY.dInf_eq (symY.f wk) t).trans distance
  have backInside : 0 < KRKEdgeDepth.depth (symY.f t) := by
    simp only [KRKEdgeDepth.depth,symY] at inside ⊢
    (try dsimp only)
    omega
  have covered := cover (symY.f t) backDistance backInside
  simp only [Covered,dInf,absDiff,RookLine,symY] at covered ⊢
  (try dsimp only at covered ⊢)
  omega

theorem home_prison {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp) (far : 2 ≤ dInf sk wk)
    (sy : sk.2 = homeRank σ) (ry : rs.2 = homeRank σ)
    (low : 2 ≤ rs.1.val) (high : rs.1.val ≤ 5)
    (notMate : ¬MatedK q) (win : MateWithin σ 6 q) :
    (wk = ((0 : Fin 8),homeRank σ) ∧ sk.1.val = 2) ∨
      (wk = ((7 : Fin 8),homeRank σ) ∧ sk.1.val = 5) := by
  have safe := krk_force_weak_safe material turn ⟨6,win⟩
  have all : ∀ r, Legal q r → MateWithin σ 5 r := by
    rcases win with goal | ⟨_,chosen | defended⟩
    · exact False.elim (notMate goal.2)
    · exact False.elim (opp_ne σ (chosen.1.symm.trans turn))
    · exact defended.2.2
  have every : ∀ u, StepM ⟨sk,rs,wk,false⟩ ⟨sk,rs,u,true⟩ → Clear sk rs u := by
    intro u step
    obtain ⟨r,edge,next⟩ := step_sound (show Matches q σ ⟨sk,rs,wk,false⟩ from ⟨material,turn⟩) step
    obtain ⟨nextFar,notCheck⟩ := krk_strong_arrival_geometry edge next.1 next.2
    exact (kernel_five_iff next.1 next.2 nextFar notCheck).mp (all r edge)
  have cover : ∀ t, dInf wk t = 1 → 0 < KRKEdgeDepth.depth t → Covered sk rs t :=
    fun t distance inside => interior_covered safe distance inside every
  cases σ with
  | white =>
    have sy0 : sk.2.val = 0 := congrArg Fin.val sy
    have ry0 : rs.2.val = 0 := congrArg Fin.val ry
    have rank := rank_prison sy0 ry0 low high cover
    rcases corner_prison sy0 ry0 low high far cover with ⟨x,k⟩ | ⟨x,k⟩
    · exact Or.inl ⟨Prod.ext (Fin.ext x) (Fin.ext rank),k⟩
    · exact Or.inr ⟨Prod.ext (Fin.ext x) (Fin.ext rank),k⟩
  | black =>
    have sy7 : sk.2.val = 7 := congrArg Fin.val sy
    have ry7 : rs.2.val = 7 := congrArg Fin.val ry
    have sy0 : (symY.f sk).2.val = 0 := by dsimp [symY]; omega
    have ry0 : (symY.f rs).2.val = 0 := by dsimp [symY]; omega
    have flipped := cover_flip cover
    have rank := rank_prison sy0 ry0 low high flipped
    have weakRank : wk.2.val = 7 := by dsimp [symY] at rank; omega
    rcases corner_prison sy0 ry0 low high (by rwa [symY.dInf_eq]) flipped with ⟨x,k⟩ | ⟨x,k⟩
    · exact Or.inl ⟨Prod.ext (Fin.ext x) (Fin.ext weakRank),k⟩
    · exact Or.inr ⟨Prod.ext (Fin.ext x) (Fin.ext weakRank),k⟩

/-- Actual castling cannot be a nonmating entry into a six-ply weak win.
All castling flags and both colours remain in the hypotheses. -/
theorem castle_not_six {q : Position} {σ : Colour} {sk rs wk ns nr : Square}
    {m : Move} (hk : IsKRK q σ sk rs wk) (turn : q.turn = σ)
    (legal : isLegal q m = true) (notMate : ¬MatedK (play q m))
    (src : m.src = sk) (castle : canCastle q m = true)
    (next : IsKRK (play q m) σ ns nr wk) : ¬MateWithin σ 6 (play q m) := by
  have source : q.board m.src = some ⟨σ, .king⟩ := by
    rw [src, hk.2.2.2]; exact krkBoard_sk
  intro win
  have actual := castle
  simp only [canCastle, turn, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    Option.isNone_iff_eq_none] at actual
  rcases actual with ⟨⟨⟨start, row⟩, promo⟩, king | queen⟩
  · have dest : m.dst = ((6 : Fin 8), homeRank σ) := Prod.ext king.1.1.1.1.1.1.1 row
    have move : m = ⟨((4 : Fin 8), homeRank σ), ((6 : Fin 8), homeRank σ), none⟩ := by
      cases m; simp only [Move.mk.injEq]; exact ⟨start, dest, promo⟩
    rw [start] at source
    have nsEq := KRKCastleFour.king_square next (t := ((6 : Fin 8), homeRank σ))
      (by rw [move]; simp [play, turn, source])
    have nrEq := KRKCastleFour.rook_square next (t := ((5 : Fin 8), homeRank σ))
      (by rw [move]; simp [play, turn, source])
    have actualNext : IsKRK (play q m) σ ((6 : Fin 8),homeRank σ) ((5 : Fin 8),homeRank σ) wk := by
      simpa only [←nsEq,←nrEq] using next
    have prison := home_prison actualNext (by rw [play_turn,turn])
      (KRKEdgeDepth.arrival_far ⟨m,legal,rfl⟩ actualNext) rfl rfl (by dsimp only; decide) (by dsimp only; decide) notMate win
    rcases prison with ⟨_,bad⟩ | ⟨_,bad⟩ <;> dsimp only at bad <;> omega
  · have dest : m.dst = ((2 : Fin 8), homeRank σ) := Prod.ext queen.1.1.1.1.1.1.1.1 row
    have move : m = ⟨((4 : Fin 8), homeRank σ), ((2 : Fin 8), homeRank σ), none⟩ := by
      cases m; simp only [Move.mk.injEq]; exact ⟨start, dest, promo⟩
    rw [start] at source
    have nsEq := KRKCastleFour.king_square next (t := ((2 : Fin 8), homeRank σ))
      (by rw [move]; simp [play, turn, source])
    have nrEq := KRKCastleFour.rook_square next (t := ((3 : Fin 8), homeRank σ))
      (by rw [move]; simp [play, turn, source])
    have actualNext : IsKRK (play q m) σ ((2 : Fin 8),homeRank σ) ((3 : Fin 8),homeRank σ) wk := by
      simpa only [←nsEq,←nrEq] using next
    have prison := home_prison actualNext (by rw [play_turn,turn])
      (KRKEdgeDepth.arrival_far ⟨m,legal,rfl⟩ actualNext) rfl rfl (by dsimp only; decide) (by dsimp only; decide) notMate win
    have weakAt : wk = ((0 : Fin 8),homeRank σ) := by
      rcases prison with ⟨weak,_⟩ | ⟨_,bad⟩
      · exact weak
      · dsimp only at bad; omega
    have rookAt : q.board ((0 : Fin 8), homeRank σ) = some ⟨σ, .rook⟩ := queen.1.1.1.1.1.1.2
    have weak : q.board wk = some ⟨σ.opp, .king⟩ := by
      rw [hk.2.2.2]; exact krkBoard_wk hk.2.1 hk.2.2.1
    rw [weakAt, rookAt] at weak
    have impossible := congrArg (fun p : Option Piece => p.map Piece.kind) weak
    cases impossible


/-- In the next strong clock band, every nonmating winning first move is
noncastling. This checks the real appended history and deadline. -/
theorem winning_entry_not_castle {s t : RawHistoryLayer.State} {σ : Colour} {sk rs wk : Square} {m : Move}
    (material : IsKRK (RawHistoryLayer.erase s) σ sk rs wk)
    (turn : (RawHistoryLayer.erase s).turn = σ) (high : 92 ≤ RawClock.clock s.val.trace)
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
  have budget : KRKDeadline.budget σ t ≤ 7 := by
    simp only [KRKDeadline.budget,notStrong,↓reduceIte]
    omega
  have six := KRKSixGeometry.weak_seven_six nextT nextTurn (mateWithin_mono deadline budget)
  rw [boardEq] at six notMate
  intro castle
  exact castle_not_six material turn legal notMate src castle next six

end EndgameChess.Rules.KRKCastleSix




