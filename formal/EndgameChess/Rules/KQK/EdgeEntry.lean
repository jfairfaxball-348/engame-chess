import EndgameChess.Rules.KQK.FramedFinish

/-! Edge entry with unrestricted strong-king placement. The queen controls
the penultimate rank; evacuation of its own king is part of the strategy. -/
namespace EndgameChess.Rules.KQK
open EndgameChess.KK

def Corridor (qs wk : Square) : Prop :=
  qs.2.val = 6 ∧ wk.2.val = 7 ∧ qs.1.val ≤ 4 ∧ qs.1.val+2 ≤ wk.1.val

def OutsideCorridor (sk qs : Square) : Prop := sk.2.val ≤ 5 ∨ sk.1.val < qs.1.val

private theorem horizontal_reply {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ.opp)
    (qy : qs.2.val = 6) (wy : wk.2.val = 7) (x : Fin 8)
    (step : absDiff wk.1.val x.val = 1) (gap : qs.1.val+2 ≤ x.val)
    (far : 2 ≤ dInf sk (x,7)) : ∃ r, Legal q r := by
  have hd : dInf wk (x,7) = 1 := by simp only [dInf,absDiff] at step ⊢; omega
  have ne : (x,(7 : Fin 8)) ≠ qs := by simp only [ne_iff_coords]; omega
  have unseen : ¬ QueenSees qs (x,7) sk (x,7) := by
    apply not_sees_of_not_line <;> simp only [absDiff] <;> omega
  obtain ⟨r,hr,_,_⟩ := weak_move hq ht hd ne far unseen
  exact ⟨r,hr⟩

/-- A king off the queen rank, left of its ray, or beyond every candidate
weak destination cannot block the confining rank. -/
private theorem corridor_reply {q r : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ.opp)
    (qy : qs.2.val = 6) (wy : wk.2.val = 7) (qx : qs.1.val ≤ 4)
    (gap : qs.1.val+1 ≤ wk.1.val) (safe : SafeQueen sk qs wk)
    (clear : sk.2.val ≠ 6 ∨ sk.1.val < qs.1.val ∨ wk.1.val+2 ≤ sk.1.val)
    (hl : Legal q r) :
    ∃ t, IsKQK r σ sk qs t ∧ r.turn = σ ∧ Corridor qs t ∧
      dInf wk t = 1 ∧ 2 ≤ dInf sk t := by
  obtain ⟨t,hm,hrt,hd,hfar,hn⟩ := safe_reply hq ht safe hl
  have tx : qs.1.val ≤ t.1.val := by simp only [dInf,absDiff] at hd; omega
  have upperX : t.1.val ≤ wk.1.val+1 := by simp only [dInf,absDiff] at hd; omega
  have ty : t.2.val = 7 := by
    have bound := t.2.isLt
    have lower : 6 ≤ t.2.val := by simp only [dInf,absDiff] at hd; omega
    by_cases edge : t.2.val = 7
    · exact edge
    · have six : t.2.val = 6 := by omega
      have ne := ne_iff_coords.mp hm.2.2.1
      apply False.elim
      apply hn
      apply rook_sees_queen
      refine ⟨⟨ne,Or.inr (by omega)⟩,?_,not_onSeg_end _ _⟩
      rcases clear with off | left | right <;> simp only [OnSeg] <;> omega
  have newGap : qs.1.val+2 ≤ t.1.val := by
    by_cases enough : qs.1.val+2 ≤ t.1.val
    · exact enough
    · exact False.elim (hn (near_sees (by simp only [dInf,absDiff]; omega)))
  exact ⟨t,hm,hrt,⟨qy,ty,qx,newGap⟩,hd,hfar⟩

private theorem outside_reply_exists {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ.opp)
    (he : Corridor qs wk) (outside : OutsideCorridor sk qs) : ∃ r, Legal q r := by
  obtain ⟨qy,wy,qx,gap⟩ := he
  let x : Fin 8 := ⟨if wk.1.val = 7 then 6 else wk.1.val+1,by
    have bound := wk.1.isLt; split <;> omega⟩
  have hx : absDiff wk.1.val x.val = 1 ∧ qs.1.val+2 ≤ x.val := by
    have bound := wk.1.isLt
    dsimp [x]; split <;> simp only [absDiff] <;> omega
  apply horizontal_reply hq ht qy wy x hx.1 hx.2
  rcases outside with low | left <;> simp only [dInf,absDiff] <;> omega

private theorem rank_six_corridor_bound {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (he : Corridor qs wk) (ky : sk.2.val = 6) : MateWithin σ 27 q := by
  let su : Square := (sk.1,5)
  obtain ⟨c,hl,hm,hc⟩ := king_move (t := su) hq ht
    (by simp only [dInf,absDiff,su]; omega)
    (by simp only [ne_iff_coords,su]; have := he.1; omega)
    (by simp only [dInf,absDiff,su]; have := he.2.1; omega)
  have wall : EdgeWall su qs wk := ⟨by dsimp [su]; omega,he⟩
  apply mateWithin_pair ht hl hc (edge_reply_exists hm hc wall)
  intro r hr
  obtain ⟨t,hmt,hrt,het,_⟩ := edge_reply hm hc wall hr
  exact edge_wall_twenty_five hmt hrt het

theorem outside_corridor_bound {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (he : Corridor qs wk) (outside : OutsideCorridor sk qs) : MateWithin σ 29 q := by
  by_cases low : sk.2.val ≤ 5
  · exact mateWithin_mono (edge_wall_twenty_five hq ht ⟨low,he⟩) (by decide)
  by_cases six : sk.2.val = 6
  · exact mateWithin_mono (rank_six_corridor_bound hq ht he six) (by decide)
  have top : sk.2.val = 7 := by have bound := sk.2.isLt; omega
  have left : sk.1.val < qs.1.val := outside.resolve_left low
  let su : Square := (sk.1,6)
  obtain ⟨c,hl,hm,hc⟩ := king_move (t := su) hq ht
    (by simp only [dInf,absDiff,su]; omega)
    (by simp only [ne_iff_coords,su]; omega)
    (by simp only [dInf,absDiff,su]; have := he.2.2.2; omega)
  have newOutside : OutsideCorridor su qs := Or.inr left
  apply mateWithin_pair ht hl hc (outside_reply_exists hm hc he newOutside)
  intro r hr
  have safe : SafeQueen su qs wk := Or.inl (by
    have qy := he.1; have wy := he.2.1; have gx := he.2.2.2
    simp only [dInf,absDiff]; omega)
  obtain ⟨t,hmt,hrt,het,_,_⟩ := corridor_reply hm hc he.1 he.2.1 he.2.2.1
    (by have := he.2.2.2; omega) safe (Or.inr (Or.inl left)) hr
  exact rank_six_corridor_bound hmt hrt het rfl

theorem outside_corridor_weak_bound {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ.opp)
    (he : Corridor qs wk) (outside : OutsideCorridor sk qs) : MateWithin σ 30 q := by
  have safe : SafeQueen sk qs wk := Or.inl (by
    have qy := he.1; have wy := he.2.1; have gap := he.2.2.2
    simp only [dInf,absDiff]; omega)
  apply mateWithin_defend ht (outside_reply_exists hq ht he outside)
  intro r hr
  have clear : sk.2.val ≠ 6 ∨ sk.1.val < qs.1.val ∨ wk.1.val+2 ≤ sk.1.val := by
    rcases outside with low | left
    · exact Or.inl (by omega)
    · exact Or.inr (Or.inl left)
  obtain ⟨t,hm,hrt,het,_,_⟩ := corridor_reply hq ht he.1 he.2.1 he.2.2.1
    (by have := he.2.2.2; omega) safe clear hr
  exact outside_corridor_bound hm hrt het outside

private theorem top_left_reply_exists {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ.opp)
    (qy : qs.2.val = 6) (wy : wk.2.val = 7) (qx : qs.1.val ≤ 4)
    (gap : qs.1.val+1 ≤ wk.1.val) (left : sk.1.val+2 ≤ wk.1.val)
    (kx : sk.1.val ≤ 4) : ∃ r, Legal q r := by
  let x : Fin 8 := ⟨if wk.1.val = 7 then 6 else wk.1.val+1,by
    have bound := wk.1.isLt; split <;> omega⟩
  have props : absDiff wk.1.val x.val = 1 ∧ qs.1.val+2 ≤ x.val ∧ sk.1.val+2 ≤ x.val := by
    have bound := wk.1.isLt
    dsimp [x]; split <;> simp only [absDiff] <;> omega
  apply horizontal_reply hq ht qy wy x props.1 props.2.1
  simp only [dInf,absDiff]; omega

/-- On the last rank, walking away from the lone king evacuates a blocking
king. Its file strictly decreases; a queen shift frees the corner case. -/
theorem top_left_corridor_bound {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (he : Corridor qs wk) (ky : sk.2.val = 7) (left : sk.1.val+2 ≤ wk.1.val) :
    MateWithin σ (2*sk.1.val+31) q := by
  generalize hkx : sk.1.val = k
  induction k using Nat.strongRecOn generalizing q sk wk with
  | ind k ih =>
    by_cases out : sk.1.val < qs.1.val
    · exact mateWithin_mono (outside_corridor_bound hq ht he (Or.inr out)) (by omega)
    by_cases zero : sk.1.val = 0
    · have qx : qs.1.val = 0 := by omega
      let nq : Square := (1,6)
      have see : QueenSees qs nq sk wk := near_sees (by
        have qy := he.1; simp only [dInf,absDiff,nq]; omega)
      obtain ⟨c,hl,hm,hc⟩ := queen_move (t := nq) hq ht see
        (by simp only [ne_iff_coords,nq]; omega)
        (by simp only [ne_iff_coords,nq]; omega)
        (by simp only [dInf,absDiff]; omega)
      have protect : SafeQueen sk nq wk := Or.inr (by simp only [dInf,absDiff,nq]; omega)
      have replies := top_left_reply_exists hm hc rfl he.2.1 (by dsimp [nq]; omega)
        (by dsimp [nq]; have := he.2.2.2; omega) left (by omega)
      have all : ∀ r, Legal c r → MateWithin σ 29 r := by
        intro r hr
        obtain ⟨t,hmt,hrt,het,_,_⟩ := corridor_reply hm hc rfl he.2.1 (by dsimp [nq]; omega)
          (by dsimp [nq]; have := he.2.2.2; omega) protect (Or.inl (by omega)) hr
        exact outside_corridor_bound hmt hrt het (Or.inr (by dsimp [nq]; omega))
      have result := mateWithin_pair ht hl hc replies all
      have kz : k = 0 := by omega
      simpa only [kz] using result
    · let su : Square := (⟨sk.1.val-1,Nat.lt_of_le_of_lt (Nat.sub_le _ _) sk.1.isLt⟩,7)
      have sx : su.1.val+1 = sk.1.val := by dsimp [su]; omega
      have small : su.1.val ≤ 4 := by have bound := wk.1.isLt; omega
      obtain ⟨c,hl,hm,hc⟩ := king_move (t := su) hq ht
        (by simp only [dInf,absDiff,su]; omega)
        (by simp only [ne_iff_coords,su]; have := he.1; omega)
        (by simp only [dInf,absDiff,su]; omega)
      have replies := top_left_reply_exists hm hc he.1 he.2.1 he.2.2.1
        (by have := he.2.2.2; omega) (by omega) small
      have all : ∀ r, Legal c r → MateWithin σ (2*(k-1)+31) r := by
        intro r hr
        have safe : SafeQueen su qs wk := Or.inl (by
          have gap := he.2.2.2; simp only [dInf,absDiff]; omega)
        obtain ⟨t,hmt,hrt,het,hd,_⟩ := corridor_reply hm hc he.1 he.2.1 he.2.2.1
          (by have := he.2.2.2; omega) safe (Or.inl (by dsimp [su]; omega)) hr
        have newLeft : su.1.val+2 ≤ t.1.val := by simp only [dInf,absDiff] at hd; omega
        have decrease : su.1.val < k := by omega
        have result := ih su.1.val decrease hmt hrt het rfl newLeft rfl
        have eq : su.1.val = k-1 := by omega
        rwa [eq] at result
      have result := mateWithin_pair ht hl hc replies all
      have eq : 2*(k-1)+31+2 = 2*k+31 := by omega
      rwa [eq] at result

private theorem right_down_bound {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (he : Corridor qs wk) (ky : sk.2.val = 7) (right : wk.1.val+2 ≤ sk.1.val)
    (x : Fin 8) (step : sk.1.val ≤ x.val ∧ x.val ≤ sk.1.val+1)
    (room : wk.1.val+3 ≤ x.val ∨ qs.1.val+3 ≤ wk.1.val) : MateWithin σ 29 q := by
  let su : Square := (x,6)
  have sx : wk.1.val+2 ≤ su.1.val := by dsimp [su]; omega
  obtain ⟨c,hl,hm,hc⟩ := king_move (t := su) hq ht
    (by simp only [dInf,absDiff,su]; omega)
    (by simp only [ne_iff_coords,su]; have := he.2.2.2; omega)
    (by simp only [dInf,absDiff,su]; omega)
  let tx : Fin 8 := ⟨if qs.1.val+3 ≤ wk.1.val then wk.1.val-1 else wk.1.val+1,by
    have bound := wk.1.isLt
    have xb := x.isLt
    split <;> omega⟩
  have props : absDiff wk.1.val tx.val = 1 ∧ qs.1.val+2 ≤ tx.val ∧ tx.val+2 ≤ x.val := by
    have gap := he.2.2.2
    dsimp [tx]; split <;> simp only [absDiff] <;> omega
  have replies := horizontal_reply hm hc he.1 he.2.1 tx props.1 props.2.1 (by
    simp only [dInf,absDiff,su]; omega)
  apply mateWithin_pair ht hl hc replies
  intro r hr
  have safe : SafeQueen su qs wk := Or.inl (by
    have gap := he.2.2.2; simp only [dInf,absDiff]; omega)
  obtain ⟨t,hmt,hrt,het,_,_⟩ := corridor_reply hm hc he.1 he.2.1 he.2.2.1
    (by have := he.2.2.2; omega) safe (Or.inr (Or.inr sx)) hr
  exact rank_six_corridor_bound hmt hrt het rfl

theorem top_right_corridor_bound {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (he : Corridor qs wk) (ky : sk.2.val = 7) (right : wk.1.val+2 ≤ sk.1.val) :
    MateWithin σ 31 q := by
  by_cases space : sk.1.val < 7
  · let x : Fin 8 := ⟨sk.1.val+1,by omega⟩
    have result := right_down_bound hq ht he ky right x
      (by dsimp [x]; omega) (Or.inl (by dsimp [x]; omega))
    exact mateWithin_mono result (by decide)
  have kx : sk.1.val = 7 := by have bound := sk.1.isLt; omega
  by_cases room : wk.1.val+3 ≤ sk.1.val ∨ qs.1.val+3 ≤ wk.1.val
  · exact mateWithin_mono (right_down_bound hq ht he ky right sk.1
      ⟨Nat.le_refl _,by omega⟩ room) (by decide)
  have wx : wk.1.val = 5 := by omega
  have qx : qs.1.val = 3 := by have gap := he.2.2.2; omega
  let nq : Square := (2,6)
  have see : QueenSees qs nq sk wk := near_sees (by
    have qy := he.1; simp only [dInf,absDiff,nq]; omega)
  obtain ⟨c,hl,hm,hc⟩ := queen_move (t := nq) hq ht see
    (by simp only [ne_iff_coords,nq]; omega)
    (by simp only [ne_iff_coords,nq]; omega)
    (by simp only [dInf,absDiff]; omega)
  have replies := horizontal_reply hm hc rfl he.2.1 (4 : Fin 8)
    (by simp only [absDiff]; omega) (by dsimp [nq]; omega)
    (by simp only [dInf,absDiff]; omega)
  apply mateWithin_pair ht hl hc replies
  intro r hr
  have safe : SafeQueen sk nq wk := Or.inl (by simp only [dInf,absDiff,nq]; omega)
  obtain ⟨t,hmt,hrt,het,hd,hfar⟩ := corridor_reply hm hc rfl he.2.1 (by dsimp [nq]; omega)
    (by dsimp [nq]; omega) safe (Or.inl (by omega)) hr
  have tx : t.1.val = 4 := by
    have ty := het.2.1
    have wy := he.2.1
    have txBound := t.1.isLt
    simp only [dInf,absDiff] at hd hfar
    omega
  exact right_down_bound hmt hrt het ky (by omega) sk.1
    ⟨Nat.le_refl _,by omega⟩ (Or.inl (by omega))

/-- General edge-wall entry: the strong king may start anywhere legal,
including on the queen's rank or in the confined side of the board. -/
theorem corridor_bound {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (he : Corridor qs wk) (far : 2 ≤ dInf sk wk) : MateWithin σ 41 q := by
  by_cases low : sk.2.val ≤ 5
  · exact mateWithin_mono (edge_wall_twenty_five hq ht ⟨low,he⟩) (by decide)
  by_cases six : sk.2.val = 6
  · exact mateWithin_mono (rank_six_corridor_bound hq ht he six) (by decide)
  have top : sk.2.val = 7 := by have bound := sk.2.isLt; omega
  have sides : sk.1.val+2 ≤ wk.1.val ∨ wk.1.val+2 ≤ sk.1.val := by
    have wy := he.2.1
    simp only [dInf,absDiff] at far
    omega
  rcases sides with left | right
  · have kx : sk.1.val ≤ 5 := by have bound := wk.1.isLt; omega
    exact mateWithin_mono (top_left_corridor_bound hq ht he top left) (by omega)
  · exact mateWithin_mono (top_right_corridor_bound hq ht he top right) (by decide)

theorem framed_corridor_bound (g : QueenSym) {q : Position} {σ : Colour}
    {sk qs wk : Square} (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (he : Corridor (g.f qs) (g.f wk)) (far : 2 ≤ dInf sk wk) : MateWithin σ 41 q := by
  apply unframe_bound g hq
  apply corridor_bound
  · exact ⟨g.toBoardSym.ne_iff.mpr hq.1,g.toBoardSym.ne_iff.mpr hq.2.1,
      g.toBoardSym.ne_iff.mpr hq.2.2.1,rfl⟩
  · exact ht
  · exact he
  · rwa [g.dInf_eq]

end EndgameChess.Rules.KQK
