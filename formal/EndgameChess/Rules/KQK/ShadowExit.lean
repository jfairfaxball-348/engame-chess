import EndgameChess.Rules.KQK.ShadowGeometry

namespace EndgameChess.Rules.KQK
open EndgameChess.KK
set_option maxHeartbeats 2000000

def ShadowExit (sk qs wk : Square) : Prop :=
  sk.1.val+sk.2.val ≤ 4 ∧ qs.1.val = 5 ∧ wk.1.val = 7 ∧
    (qs.2.val+1 = wk.2.val ∨ qs.2.val+3 = wk.2.val)

theorem shadow_exit_bound {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (he : ShadowExit sk qs wk) : MateWithin σ 27 q := by
  obtain ⟨low,qx,wx,offset⟩ := he
  have skx : sk.1.val ≤ 4 := by omega
  have sky : sk.2.val ≤ 4 := by omega
  have wy : 1 ≤ wk.2.val := by rcases offset with one | three <;> omega
  have far : 2 ≤ dInf sk wk := by simp only [dInf,absDiff]; omega
  by_cases bottom : wk.2.val = 1
  · have qy : qs.2.val = 0 := by rcases offset with one | three <;> omega
    let nq : Square := (5,2)
    have see : QueenSees qs nq sk wk := by
      apply rook_sees_queen
      refine ⟨⟨by dsimp [nq]; omega,Or.inl qx⟩,?_,?_⟩
      · simp only [OnSeg,nq]; omega
      · simp only [OnSeg,nq]; omega
    obtain ⟨c,hl,hm,hc⟩ := queen_move (t := nq) hq ht see
      (by simp only [ne_iff_coords,nq]; omega)
      (by simp only [ne_iff_coords,nq]; omega) far
    have safe : SafeQueen sk nq wk := Or.inl (by simp only [dInf,absDiff,nq]; omega)
    let first : Square := (6,0)
    have firstStep : dInf wk first = 1 := by simp only [dInf,absDiff,first]; omega
    have firstNe : first ≠ nq := by decide
    have firstFar : 2 ≤ dInf sk first := by simp only [dInf,absDiff,first]; omega
    have firstNot : ¬ QueenSees nq first sk first := by
      apply not_sees_of_not_line <;> decide
    obtain ⟨r,hr,_,_⟩ := weak_move hm hc firstStep firstNe firstFar firstNot
    have all : ∀ r, Legal c r → MateWithin σ 23 r := by
      intro r hr
      obtain ⟨t,hmt,hrt,hd,hfar,hn⟩ := safe_reply hm hc safe hr
      have point : t.1.val = 6 ∧ t.2.val = 0 := by
        have bx := t.1.isLt
        have by' := t.2.isLt
        have bounds : 6 ≤ t.1.val ∧ t.2.val ≤ 2 := by
          simp only [dInf,absDiff] at hd; omega
        have notTwo : t.2.val ≠ 2 := by
          intro two
          apply hn
          apply rook_sees_queen
          refine ⟨⟨by dsimp [nq]; omega,Or.inr (by dsimp [nq]; omega)⟩,?_,not_onSeg_end _ _⟩
          simp only [OnSeg,nq]; omega
        have notNear : ¬ dInf nq t = 1 := fun h => hn (near_sees h)
        have notSevenZero : ¬ (t.1.val = 7 ∧ t.2.val = 0) := by
          rintro ⟨seven,zero⟩
          apply hn
          apply sees_split.mpr
          right
          refine ⟨?_,?_,?_⟩
          · simp only [KBK.onDiag,ne_iff_coords,absDiff,nq]; omega
          · simp only [KBK.between,KBK.onDiag,dInf,absDiff,ne_iff_coords,nq]; omega
          · simp [KBK.between,KBK.onDiag]
        simp only [dInf,absDiff,nq] at hd notNear
        omega
      let nextQ : Square := (4,1)
      have nextSee : QueenSees nq nextQ sk t := near_sees (by decide)
      have nextNe : nextQ ≠ sk := by simp only [ne_iff_coords,nextQ]; omega
      have nextWeak : nextQ ≠ t := by simp only [ne_iff_coords,nextQ]; omega
      obtain ⟨u,hu,hum,hut⟩ := queen_move (t := nextQ) hmt hrt nextSee nextNe nextWeak hfar
      have prison : Prison (reflectY.f nextQ) (reflectY.f t) := by
        dsimp [Prison,reflectY,symY,nextQ]; omega
      have outside : OutsidePrison (reflectY.f sk) := Or.inr (by
        dsimp [reflectY,symY]; omega)
      have win := framed_prison_weak_bound reflectY hum hut prison outside
      exact mateWithin_choose hrt hu win
    have win := mateWithin_choose ht hl (mateWithin_defend hc ⟨r,hr⟩ all)
    exact mateWithin_mono win (by decide)
  by_cases top : wk.2.val = 7
  · rcases offset with one | three
    · have qy : qs.2.val = 6 := by omega
      let nq : Square := (4,6)
      have see : QueenSees qs nq sk wk := near_sees (by simp only [dInf,absDiff,nq]; omega)
      obtain ⟨c,hl,hm,hc⟩ := queen_move (t := nq) hq ht see
        (by simp only [ne_iff_coords,nq]; omega)
        (by simp only [ne_iff_coords,nq]; omega) far
      have prison : Prison nq wk := ⟨rfl,rfl,top,by omega⟩
      have outside : OutsidePrison sk := Or.inl (by omega)
      exact mateWithin_mono (mateWithin_choose ht hl (prison_weak_bound hm hc prison outside))
        (by decide)
    · have qy : qs.2.val = 4 := by omega
      let nq : Square := (6,4)
      have see : QueenSees qs nq sk wk := near_sees (by simp only [dInf,absDiff,nq]; omega)
      obtain ⟨c,hl,hm,hc⟩ := queen_move (t := nq) hq ht see
        (by simp only [ne_iff_coords,nq]; omega)
        (by simp only [ne_iff_coords,nq]; omega) far
      have wall : EdgeWall (swap.f sk) (swap.f nq) (swap.f wk) := by
        dsimp [EdgeWall,swap,symSwap,nq]; omega
      exact mateWithin_choose ht hl (framed_edge_wall_weak_bound swap hm hc wall)
  · let nq : Square := (6,⟨wk.2.val-2,by omega⟩)
    have y : 2 ≤ wk.2.val ∧ wk.2.val ≤ 6 := by have bound := wk.2.isLt; omega
    have see : QueenSees qs nq sk wk := by
      apply near_sees
      rcases offset with one | three <;> simp only [dInf,absDiff,nq] <;> omega
    obtain ⟨c,hl,hm,hc⟩ := queen_move (t := nq) hq ht see
      (by simp only [ne_iff_coords,nq]; omega)
      (by simp only [ne_iff_coords,nq]; omega) far
    have wall : EdgeWall (swap.f sk) (swap.f nq) (swap.f wk) := by
      dsimp [EdgeWall,swap,symSwap,nq]; omega
    exact mateWithin_choose ht hl (framed_edge_wall_weak_bound swap hm hc wall)

end EndgameChess.Rules.KQK
