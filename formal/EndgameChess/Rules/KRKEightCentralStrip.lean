import EndgameChess.Rules.KRKEightInterior

namespace EndgameChess.Rules.KRKEightCentralStrip
open EndgameChess.KK KRKNativeFrame KRKFourPlyEscape
set_option maxHeartbeats 400000

/-- In the middle of a first strip, no inward-corner exception is available. -/
theorem prison {sk rs wk : Square} (file : wk.1.val = 1)
    (low : 3 ≤ wk.2.val) (high : wk.2.val ≤ 4)
    (far : 2 ≤ dInf sk wk) (clear : KRKEightGeometry.Clear sk rs wk) :
    sk.1.val = 3 ∧ sk.2.val = wk.2.val ∧ rs.1.val = 1 := by
  apply strip_prison file (by omega) (by omega) far clear.1
  intro t distance inside
  have notInner : ¬KRKSixInterior.InnerCorner t := by
    simp only [dInf,absDiff,file] at distance
    dsimp [KRKSixInterior.InnerCorner]
    omega
  exact (KRKEightInterior.covered_or_inner clear.1 distance inside
    (fun u step => clear.2.2 u (KRKCornerWeakBand.step_guard step))).resolve_right notInner

theorem not_clear {sk rs wk : Square} (file : wk.1.val = 1)
    (low : 3 ≤ wk.2.val) (high : wk.2.val ≤ 4)
    (distinct : sk ≠ rs) (notRook : rs ≠ wk) (far : 2 ≤ dInf sk wk) :
    ¬KRKEightGeometry.Clear sk rs wk := by
  intro clear
  obtain ⟨sx,sy,rx⟩ := prison file low high far clear
  let t : Square := (0,wk.2)
  have guard : KRKCornerWeakBand.Guard sk rs wk t := by
    have differentRank : rs.2.val ≠ wk.2.val := by
      intro same
      exact notRook (Prod.ext (Fin.ext (rx.trans file.symm)) (Fin.ext same))
    simp only [KRKCornerWeakBand.Guard,t,dInf,absDiff,RookSees,RookLine,OnSeg,
      ne_iff_coords,sx,sy,rx,file]
    omega
  have child := clear.2.2 t guard
  let g := Frame.ofSym symSwap
  have farChild : 2 ≤ dInf sk t := guard.2.2.1
  have notKing : sk ≠ t := by intro h; rw [h] at farChild; simp [dInf,absDiff] at farChild
  have notRookChild : rs ≠ t := guard.2.1.symm
  have mapped := KRKSevenReach.frame_map g distinct notKing notRookChild farChild guard.2.2.2 child
  have formula := (KRKSevenMiddle.low_rook_clear_iff
    (sk := g.f sk) (rs := g.f rs) (wk := g.f t)
    (by rfl) (by simpa [g,Frame.ofSym,symSwap,t] using low)
    (by simpa [g,Frame.ofSym,symSwap,t] using high)
    (by simp [g,Frame.ofSym,symSwap,rx])
    (g.ne_iff.mpr distinct) (g.ne_iff.mpr notKing) (g.ne_iff.mpr notRookChild)
    (by rwa [g.distance])
    (fun h => guard.2.2.2 ((g.sees _ _ _ _).mp h))).mp mapped
  simp only [KRKFiveMiddle.LowRookFive,g,Frame.ofSym,symSwap] at formula
  omega

theorem kernel_no_eight {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp)
    (file : wk.1.val = 1) (low : 3 ≤ wk.2.val) (high : wk.2.val ≤ 4)
    (far : 2 ≤ dInf sk wk) : ¬MateWithin σ 8 q := by
  have notMate : ¬MatedK q := by
    intro mate
    have zero := KRKEdgeDepth.terminal_depth_zero ((KRKMateGeometry.kernel_mate_iff material turn far).mp mate)
    dsimp [KRKEdgeDepth.depth] at zero
    omega
  intro win
  exact not_clear file low high material.1 material.2.2.1 far
    ((KRKEightGeometry.kernel_eight_iff material turn notMate).mp win)

def MiddleStrip (wk : Square) : Prop :=
  ((wk.1.val = 1 ∨ wk.1.val = 6) ∧ 3 ≤ wk.2.val ∧ wk.2.val ≤ 4) ∨
  ((wk.2.val = 1 ∨ wk.2.val = 6) ∧ 3 ≤ wk.1.val ∧ wk.1.val ≤ 4)

private theorem mapped_not_clear (g : Frame) {sk rs wk : Square}
    (file : (g.f wk).1.val = 1) (low : 3 ≤ (g.f wk).2.val) (high : (g.f wk).2.val ≤ 4)
    (distinct : sk ≠ rs) (notRook : rs ≠ wk) (far : 2 ≤ dInf sk wk)
    (clear : KRKEightGeometry.Clear sk rs wk) : False :=
  not_clear file low high (g.ne_iff.mpr distinct) (g.ne_iff.mpr notRook)
    (by rwa [g.distance]) (KRKCastleEight.frame_map g distinct clear)

theorem middle_not_clear {sk rs wk : Square} (middle : MiddleStrip wk)
    (distinct : sk ≠ rs) (notRook : rs ≠ wk) (far : 2 ≤ dInf sk wk) :
    ¬KRKEightGeometry.Clear sk rs wk := by
  intro clear
  rcases middle with ⟨file,low,high⟩ | ⟨rank,low,high⟩
  · rcases file with left | right
    · exact not_clear left low high distinct notRook far clear
    · apply mapped_not_clear (Frame.ofSym symX) (sk := sk) (rs := rs) (wk := wk)
        (by dsimp [Frame.ofSym,symX]; omega) low high distinct notRook far clear
  · rcases rank with bottom | top
    · exact mapped_not_clear (Frame.ofSym symSwap) bottom low high distinct notRook far clear
    · apply mapped_not_clear ((Frame.ofSym symSwap).comp (Frame.ofSym symX))
        (sk := sk) (rs := rs) (wk := wk)
        (by dsimp [Frame.comp,Frame.ofSym,symSwap,symX]; omega) low high distinct notRook far clear

theorem middle_kernel_no_eight {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp)
    (middle : MiddleStrip wk) (far : 2 ≤ dInf sk wk) : ¬MateWithin σ 8 q := by
  have inside : 0 < KRKEdgeDepth.depth wk := by
    dsimp [MiddleStrip,KRKEdgeDepth.depth] at middle ⊢
    omega
  have notMate : ¬MatedK q := by
    intro mate
    have zero := KRKEdgeDepth.terminal_depth_zero ((KRKMateGeometry.kernel_mate_iff material turn far).mp mate)
    omega
  intro win
  exact middle_not_clear middle material.1 material.2.2.1 far
    ((KRKEightGeometry.kernel_eight_iff material turn notMate).mp win)

end EndgameChess.Rules.KRKEightCentralStrip
