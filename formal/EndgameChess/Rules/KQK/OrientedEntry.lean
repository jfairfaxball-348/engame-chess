import EndgameChess.Rules.KQK.EntryFrames

namespace EndgameChess.Rules.KQK
open EndgameChess.KK

theorem framed_clear_low_wall_entry (g : QueenSym) {q : Position} {σ : Colour}
    {sk qs wk : Square} (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (gap : (g.f sk).2.val+2 ≤ (g.f wk).2.val) (low : (g.f sk).2.val ≤ 4)
    (clear : (g.f qs).1.val ≠ (g.f sk).1.val ∨ (g.f sk).2.val < (g.f qs).2.val)
    (files : 2 ≤ absDiff (g.f qs).1.val (g.f wk).1.val) (hc : inCheck q σ.opp = false) :
    MateWithin σ 93 q := by
  apply unframe_bound g hq
  exact clear_low_wall_entry (framed_material g hq) ht gap low clear files
    (framed_weak_not_check g hq hc)

theorem framed_clear_wall_entry (g : QueenSym) {q : Position} {σ : Colour}
    {sk qs wk : Square} (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (gap : (g.f sk).2.val+2 ≤ (g.f wk).2.val)
    (clear : (g.f qs).1.val ≠ (g.f sk).1.val ∨ (g.f sk).2.val < (g.f qs).2.val)
    (files : 3 ≤ absDiff (g.f qs).1.val (g.f wk).1.val) (hc : inCheck q σ.opp = false) :
    MateWithin σ 93 q := by
  apply unframe_bound g hq
  exact clear_wall_entry (framed_material g hq) ht gap clear files (framed_weak_not_check g hq hc)

/-- The far-file setup also admits a two-file margin on the final rank,
because its queen file remains at most four. -/
theorem small_file_wall_entry {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (gap : sk.2.val+2 ≤ wk.2.val)
    (clear : qs.1.val ≠ sk.1.val ∨ sk.2.val < qs.2.val)
    (cap : qs.1.val ≤ 4) (files : qs.1.val+2 ≤ wk.1.val)
    (hc : inCheck q σ.opp = false) : MateWithin σ 93 q := by
  by_cases low : sk.2.val ≤ 4
  · exact clear_low_wall_entry hq ht gap low clear
      (by simp only [absDiff]; omega) hc
  have ky : sk.2.val = 5 := by have bound := wk.2.isLt; omega
  have wy : wk.2.val = 7 := by have bound := wk.2.isLt; omega
  by_cases already : qs.2.val = 6
  · exact mateWithin_mono (wall_ninety_one hq ht ⟨by omega,by omega,by omega⟩ hc) (by decide)
  let nq : Square := (qs.1,6)
  have see : QueenSees qs nq sk wk := by
    apply rook_sees_queen
    refine ⟨⟨by dsimp [nq]; omega,Or.inl rfl⟩,?_,?_⟩
    · rcases clear with off | higher <;> simp only [OnSeg,nq] <;> omega
    · simp only [OnSeg,nq]; omega
  obtain ⟨c,hl,hm,hct⟩ := queen_move (t := nq) hq ht see
    (by simp only [ne_iff_coords,nq]; omega)
    (by simp only [ne_iff_coords,nq]; omega)
    (by simp only [dInf,absDiff]; omega)
  exact mateWithin_mono (mateWithin_choose ht hl (edge_wall_weak_bound hm hct
    ⟨by omega,rfl,wy,cap,files⟩)) (by decide)

private theorem high_file_corner_entry {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (kx : sk.1.val = 5) (ky : sk.2.val = 6) (qy : qs.2.val = 5)
    (wx : wk.1.val = 7) (wy : wk.2.val = 7) (hc : inCheck q σ.opp = false) :
    MateWithin σ 1 q := by
  have notFile : qs.1.val ≠ 7 := by
    intro equal
    have see : QueenSees qs wk sk wk := by
      apply rook_sees_queen
      refine ⟨⟨ne_iff_coords.mp hq.2.2.1,Or.inl (by omega)⟩,?_,not_onSeg_end _ _⟩
      simp only [OnSeg]; omega
    have check := (weak_check hq).mpr (Or.inr see)
    rw [hc] at check
    cases check
  let nq : Square := (7,5)
  have see : QueenSees qs nq sk wk := by
    apply rook_sees_queen
    refine ⟨⟨by dsimp [nq]; omega,Or.inr (by dsimp [nq]; omega)⟩,?_,?_⟩
    · simp only [OnSeg,nq]; omega
    · simp only [OnSeg,nq]; omega
  obtain ⟨c,hl,hm,hct⟩ := queen_move (t := nq) hq ht see
    (by simp only [ne_iff_coords,nq]; omega)
    (by simp only [ne_iff_coords,nq]; omega)
    (by simp only [dInf,absDiff]; omega)
  exact mateWithin_choose ht hl ⟨hct,corner_distant_mated hm hct kx ky rfl rfl wx wy⟩

/-- Horizontal entry after far-file preparation, with a rank margin of two.
The only narrow-corner failure of the intended wall is a direct mate. -/
theorem horizontal_far_wall_entry {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (upper : sk.2.val+1 ≤ wk.2.val) (right : 3 ≤ wk.1.val)
    (gap : 2 ≤ absDiff sk.1.val wk.1.val) (off : qs.2.val ≠ sk.2.val)
    (files : 2 ≤ absDiff qs.2.val wk.2.val) (hc : inCheck q σ.opp = false) :
    MateWithin σ 93 q := by
  by_cases forward : sk.1.val+2 ≤ wk.1.val
  · by_cases low : sk.1.val ≤ 4
    · apply framed_clear_low_wall_entry swap hq ht
      · exact forward
      · exact low
      · exact Or.inl off
      · exact files
      · exact hc
    have kx : sk.1.val = 5 := by have bound := wk.1.isLt; omega
    have wx : wk.1.val = 7 := by have bound := wk.1.isLt; omega
    by_cases wider : 3 ≤ absDiff qs.2.val wk.2.val
    · exact framed_clear_wall_entry swap hq ht forward (Or.inl off) wider hc
    have exactGap : absDiff qs.2.val wk.2.val = 2 := by omega
    by_cases wall : sk.2.val < qs.2.val ∧ qs.2.val < wk.2.val
    · exact mateWithin_mono (separating_rank_bound hq ht wall.1 wall.2 hc) (by decide)
    have outside : qs.2.val < sk.2.val ∨ wk.2.val < qs.2.val := by simp only [absDiff] at exactGap; omega
    by_cases corner : qs.2.val = 5 ∧ wk.2.val = 7
    · have ky : sk.2.val = 6 := by rcases outside with lower | higher <;> omega
      exact mateWithin_mono (high_file_corner_entry hq ht kx ky corner.1 wx corner.2 hc) (by decide)
    by_cases already : qs.1.val = 6
    · exact mateWithin_mono (framed_separating_rank_bound swap hq ht (by dsimp [swap,symSwap]; omega)
        (by dsimp [swap,symSwap]; omega) hc) (by decide)
    let nq : Square := (6,qs.2)
    have see : QueenSees qs nq sk wk := by
      apply rook_sees_queen
      refine ⟨⟨by dsimp [nq]; omega,Or.inr rfl⟩,?_,?_⟩
      · simp only [OnSeg,nq]; omega
      · simp only [OnSeg,nq]; simp only [absDiff] at exactGap; omega
    obtain ⟨c,hl,hm,hct⟩ := queen_move (t := nq) hq ht see
      (by simp only [ne_iff_coords,nq]; omega)
      (by simp only [ne_iff_coords,nq]; omega)
      (by simp only [dInf,absDiff]; omega)
    have win : MateWithin σ 26 c := by
      rcases outside with below | above
      · have wall : EdgeWall (swap.f sk) (swap.f nq) (swap.f wk) := by
          dsimp [EdgeWall,swap,symSwap,nq]
          simp only [absDiff] at exactGap
          omega
        exact framed_edge_wall_weak_bound swap hm hct wall
      · apply unframe_bound swap hm
        apply framed_edge_wall_weak_bound reflectX (framed_material swap hm) hct
        dsimp [EdgeWall,reflectX,swap,symX,symSwap,nq]
        simp only [absDiff] at exactGap
        omega
    exact mateWithin_mono (mateWithin_choose ht hl win) (by decide)
  · apply framed_clear_low_wall_entry anti hq ht
    · dsimp [anti,symAnti]; simp only [absDiff] at gap; omega
    · dsimp [anti,symAnti]; simp only [absDiff] at gap; omega
    · left; dsimp [anti,symAnti]; omega
    · dsimp [anti,symAnti]; simp only [absDiff] at files ⊢; omega
    · exact hc

end EndgameChess.Rules.KQK
