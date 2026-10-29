import EndgameChess.Rules.KQK.ShadowForce
import EndgameChess.Rules.KQK.InteriorEscape

/-! Entry into the driving strategy by a clear queen slide. These are
setup theorems, not a claim that arbitrary KQK positions satisfy the premises. -/
namespace EndgameChess.Rules.KQK
open EndgameChess.KK

def identity : QueenSym where
  toBoardSym := symId
  diag_iff _ _ := Iff.rfl

theorem framed_shadow_strong_bound (g : QueenSym) {q : Position} {σ : Colour}
    {sk qs wk : Square} (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (hs : Shadow (g.f sk) (g.f qs) (g.f wk)) (hx : (g.f wk).1.val ≤ 6) :
    MateWithin σ 53 q := by
  apply unframe_bound g hq
  apply shadow_strong_bound
  · exact ⟨g.toBoardSym.ne_iff.mpr hq.1,g.toBoardSym.ne_iff.mpr hq.2.1,
      g.toBoardSym.ne_iff.mpr hq.2.2.1,rfl⟩
  · exact ht
  · exact hs
  · exact hx

theorem framed_shadow_weak_bound (g : QueenSym) {q : Position} {σ : Colour}
    {sk qs wk : Square} (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ.opp)
    (hs : Shadow (g.f sk) (g.f qs) (g.f wk)) (hx : (g.f wk).1.val ≤ 6) :
    MateWithin σ 52 q := by
  apply unframe_bound g hq
  apply shadow_weak_fifty_two
  · exact ⟨g.toBoardSym.ne_iff.mpr hq.1,g.toBoardSym.ne_iff.mpr hq.2.1,
      g.toBoardSym.ne_iff.mpr hq.2.2.1,rfl⟩
  · exact ht
  · exact hs
  · exact hx

private theorem slide_to_shadow (g : QueenSym) {q : Position} {σ : Colour}
    {sk qs wk nq : Square} (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (hs : Shadow (g.f sk) (g.f nq) (g.f wk)) (hx : (g.f wk).1.val ≤ 6)
    (slide : qs = nq ∨ QueenSees qs nq sk wk) : MateWithin σ 53 q := by
  rcases slide with equal | sees
  · subst equal
    exact framed_shadow_strong_bound g hq ht hs hx
  · have low := hs.1
    have high := hs.2.1
    have qx := hs.2.2.1
    have qy := hs.2.2.2
    have neKing : nq ≠ sk := by
      intro equal
      have eq := congrArg g.f equal
      rw [eq] at qx qy
      omega
    have neWeak : nq ≠ wk := by
      intro equal
      have eq := congrArg g.f equal
      rw [eq] at qx
      omega
    have far : 2 ≤ dInf sk wk := by
      have far := sum_far low high
      rwa [g.dInf_eq] at far
    obtain ⟨r,hr,hm,hrt⟩ := queen_move hq ht sees neKing neWeak far
    exact mateWithin_choose ht hr (framed_shadow_weak_bound g hm hrt hs hx)

/-- A queen one or two files left of the lone king can align its rank in
one slide, provided the strong king does not block that file. Both knight
orientations feed the same proved copying strategy. -/
theorem vertical_shadow_entry {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (low : sk.1.val+sk.2.val ≤ 4) (high : 8 ≤ wk.1.val+wk.2.val)
    (wx : wk.1.val ≤ 6) (wy : wk.2.val ≤ 6)
    (gap : qs.1.val+1 = wk.1.val ∨ qs.1.val+2 = wk.1.val)
    (clearFile : sk.1.val ≠ qs.1.val) : MateWithin σ 53 q := by
  have y2 : 2 ≤ wk.2.val := by omega
  rcases gap with one | two
  · let nq : Square := (qs.1,⟨wk.2.val-2,by have := wk.2.isLt; omega⟩)
    have shadow : Shadow sk nq wk := ⟨low,high,one,by dsimp [nq]; omega⟩
    apply slide_to_shadow identity hq ht shadow wx
    by_cases equal : qs = nq
    · exact Or.inl equal
    · right
      apply rook_sees_queen
      refine ⟨⟨(ne_iff_coords.mp equal),Or.inl rfl⟩,?_,?_⟩
      · simp only [OnSeg]; omega
      · simp only [OnSeg]; omega
  · let nq : Square := (qs.1,⟨wk.2.val-1,by have := wk.2.isLt; omega⟩)
    have shadow : Shadow (swap.f sk) (swap.f nq) (swap.f wk) := by
      dsimp [Shadow,swap,symSwap,nq]; omega
    apply slide_to_shadow swap hq ht shadow wy
    by_cases equal : qs = nq
    · exact Or.inl equal
    · right
      apply rook_sees_queen
      refine ⟨⟨(ne_iff_coords.mp equal),Or.inl rfl⟩,?_,?_⟩
      · simp only [OnSeg,nq]; omega
      · simp only [OnSeg,nq]; omega

/-- Two-file knight offsets on either side of a rank have a common finish.
On the last rank, widen a singleton corridor instead of creating stalemate. -/
theorem two_file_entry_bound {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (low : sk.1.val+sk.2.val ≤ 4) (high : 8 ≤ wk.1.val+wk.2.val)
    (gap : qs.1.val+2 = wk.1.val) (nearRank : absDiff qs.2.val wk.2.val = 1) :
    MateWithin σ 53 q := by
  have wxBound := wk.1.isLt
  have wyBound := wk.2.isLt
  have qyBound := qs.2.isLt
  have y1 : 1 ≤ wk.2.val := by omega
  by_cases top : wk.2.val = 7
  · have qy : qs.2.val = 6 := by simp only [absDiff] at nearRank; omega
    by_cases wide : qs.1.val ≤ 4
    · have wall : EdgeWall sk qs wk := ⟨by omega,qy,top,wide,by omega⟩
      exact mateWithin_mono (edge_wall_twenty_five hq ht wall) (by decide)
    · have qx : qs.1.val = 5 := by omega
      let nq : Square := (4,6)
      obtain ⟨r,hr,hm,hrt⟩ := queen_move (t := nq) hq ht
        (near_sees (by simp only [dInf,absDiff,nq]; omega))
        (by simp only [ne_iff_coords,nq]; omega)
        (by simp only [ne_iff_coords,nq]; omega) (sum_far low high)
      have prison : Prison nq wk := ⟨rfl,rfl,top,by omega⟩
      have outside : OutsidePrison sk := Or.inl (by omega)
      exact mateWithin_mono (mateWithin_choose ht hr (prison_weak_bound hm hrt prison outside))
        (by decide)
  · let nq : Square := (qs.1,⟨wk.2.val-1,by omega⟩)
    have shadow : Shadow (swap.f sk) (swap.f nq) (swap.f wk) := by
      dsimp [Shadow,swap,symSwap,nq]; omega
    apply slide_to_shadow swap hq ht shadow (by dsimp [swap,symSwap]; omega)
    by_cases equal : qs = nq
    · exact Or.inl equal
    · have queenHigh : 5 ≤ qs.1.val+qs.2.val := by
        simp only [absDiff] at nearRank; omega
      right
      apply rook_sees_queen
      refine ⟨⟨ne_iff_coords.mp equal,Or.inl rfl⟩,?_,?_⟩
      · simp only [OnSeg,nq]; omega
      · simp only [OnSeg,nq]; omega

private theorem file_reply_shape {q r : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ.opp)
    (safe : SafeQueen sk qs wk) (left : sk.1.val < qs.1.val)
    (gap : qs.1.val+1 = wk.1.val) (hl : Legal q r) :
    ∃ t, IsKQK r σ sk qs t ∧ r.turn = σ ∧ dInf wk t = 1 ∧ wk.1.val ≤ t.1.val := by
  obtain ⟨t,hm,hrt,hd,_,hn⟩ := safe_reply hq ht safe hl
  have tx : wk.1.val ≤ t.1.val := by
    by_cases right : wk.1.val ≤ t.1.val
    · exact right
    · have eqx : t.1.val = qs.1.val := by simp only [dInf,absDiff] at hd; omega
      have ne : qs ≠ t := hm.2.2.1
      apply False.elim
      apply hn
      apply rook_sees_queen
      refine ⟨⟨ne_iff_coords.mp ne,Or.inl eqx.symm⟩,?_,not_onSeg_end _ _⟩
      simp only [OnSeg]; omega
  exact ⟨t,hm,hrt,hd,tx⟩

private theorem central_file_defend_bound {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ.opp)
    (low : sk.1.val+sk.2.val ≤ 4) (high : 9 ≤ wk.1.val+wk.2.val)
    (wx : wk.1.val ≤ 5) (wy : wk.2.val ≤ 5)
    (gap : qs.1.val+1 = wk.1.val) (left : sk.1.val < qs.1.val)
    (farQ : 2 ≤ dInf qs wk) : MateWithin σ 54 q := by
  have yGap : qs.2.val+2 ≤ wk.2.val ∨ wk.2.val+2 ≤ qs.2.val := by
    simp only [dInf,absDiff] at farQ; omega
  let y : Fin 8 := ⟨if qs.2.val < wk.2.val then wk.2.val+1 else wk.2.val-1,
    by split <;> omega⟩
  let t : Square := (wk.1,y)
  have step : dInf wk t = 1 := by
    dsimp [t,y]; split <;> simp only [dInf,absDiff] <;> omega
  have highT : 8 ≤ t.1.val+t.2.val := by dsimp [t,y]; split <;> omega
  have ne : t ≠ qs := by simp only [ne_iff_coords,t]; omega
  have unseen : ¬ QueenSees qs t sk t := by
    dsimp [t,y]; split <;> apply not_sees_of_not_line <;> simp only [absDiff] <;> omega
  obtain ⟨r,hr,_,_⟩ := weak_move hq ht step ne (sum_far low highT) unseen
  have safe : SafeQueen sk qs wk := Or.inl farQ
  apply mateWithin_defend ht ⟨r,hr⟩
  intro r hr
  obtain ⟨t,hmt,hrt,hd,tx⟩ := file_reply_shape hq ht safe left gap hr
  have nextHigh : 8 ≤ t.1.val+t.2.val := by simp only [dInf,absDiff] at hd; omega
  have nextX : t.1.val ≤ 6 := by simp only [dInf,absDiff] at hd; omega
  have nextY : t.2.val ≤ 6 := by simp only [dInf,absDiff] at hd; omega
  have nextGap : qs.1.val+1 = t.1.val ∨ qs.1.val+2 = t.1.val := by
    simp only [dInf,absDiff] at hd; omega
  exact vertical_shadow_entry hmt hrt low nextHigh nextX nextY nextGap (by omega)

/-- Clear the queen's file by moving the blocking king away. Every defence
then enters one of the two knight orientations. No per-position search is used. -/
theorem blocked_file_entry_bound {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (low : sk.1.val+sk.2.val ≤ 4) (high : 9 ≤ wk.1.val+wk.2.val)
    (wx : wk.1.val ≤ 5) (wy : wk.2.val ≤ 5)
    (gap : qs.1.val+1 = wk.1.val) (hc : inCheck q σ.opp = false) :
    MateWithin σ 55 q := by
  by_cases clearFile : sk.1.val ≠ qs.1.val
  · exact mateWithin_mono (vertical_shadow_entry hq ht low (by omega)
      (by omega) (by omega) (Or.inl gap) clearFile) (by decide)
  have blocked : sk.1.val = qs.1.val := by omega
  have farQ := queen_distant_of_not_check hq hc
  let su : Square := (⟨sk.1.val-1,by have := sk.1.isLt; omega⟩,sk.2)
  have lowSu : su.1.val+su.2.val ≤ 4 := by dsimp [su]; omega
  have left : su.1.val < qs.1.val := by dsimp [su]; omega
  obtain ⟨c,hl,hm,hct⟩ := king_move (t := su) hq ht
    (by simp only [dInf,absDiff,su]; omega)
    (by simp only [ne_iff_coords,su]; omega)
    (sum_far lowSu (by omega))
  exact mateWithin_choose ht hl (central_file_defend_bound hm hct lowSu high wx wy gap left farQ)

/-- Align from an arbitrary queen file along a clear horizontal ray. Its
rank is kept distant, so all weak replies survive safely and align vertically. -/
theorem horizontal_alignment_entry {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (low : sk.1.val+sk.2.val ≤ 4) (high : 9 ≤ wk.1.val+wk.2.val)
    (wx : wk.1.val ≤ 5) (wy : wk.2.val ≤ 5)
    (left : sk.1.val+2 ≤ wk.1.val) (rankGap : 2 ≤ absDiff qs.2.val wk.2.val)
    (clear : ¬ OnSeg qs sk
      (⟨wk.1.val-1,Nat.lt_of_le_of_lt (Nat.sub_le _ _) wk.1.isLt⟩,qs.2)) :
    MateWithin σ 55 q := by
  let nq : Square := (⟨wk.1.val-1,by omega⟩,qs.2)
  have gap : nq.1.val+1 = wk.1.val := by dsimp [nq]; omega
  by_cases equal : qs = nq
  · have qgap : qs.1.val+1 = wk.1.val := by
      have ex := congrArg (fun s : Square => s.1.val) equal
      dsimp [nq] at ex
      omega
    exact mateWithin_mono (vertical_shadow_entry hq ht low (by omega) (by omega)
      (by omega) (Or.inl qgap) (by omega)) (by decide)
  · have see : QueenSees qs nq sk wk := by
      apply rook_sees_queen
      refine ⟨⟨ne_iff_coords.mp equal,Or.inr rfl⟩,clear,?_⟩
      simp only [OnSeg,nq,absDiff] at rankGap ⊢; omega
    have neKing : nq ≠ sk := by simp only [ne_iff_coords,nq]; omega
    have neWeak : nq ≠ wk := by simp only [ne_iff_coords,nq]; omega
    obtain ⟨c,hl,hm,hct⟩ := queen_move hq ht see neKing neWeak (sum_far low (by omega))
    have farQ : 2 ≤ dInf nq wk := by simp only [dInf,nq]; omega
    have leftQ : sk.1.val < nq.1.val := by dsimp [nq]; omega
    exact mateWithin_choose ht hl (central_file_defend_bound hm hct low high wx wy gap leftQ farQ)

theorem framed_vertical_shadow_entry (g : QueenSym) {q : Position} {σ : Colour}
    {sk qs wk : Square} (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (low : (g.f sk).1.val+(g.f sk).2.val ≤ 4)
    (high : 8 ≤ (g.f wk).1.val+(g.f wk).2.val)
    (wx : (g.f wk).1.val ≤ 6) (wy : (g.f wk).2.val ≤ 6)
    (gap : (g.f qs).1.val+1 = (g.f wk).1.val ∨ (g.f qs).1.val+2 = (g.f wk).1.val)
    (clear : (g.f sk).1.val ≠ (g.f qs).1.val) : MateWithin σ 53 q := by
  apply unframe_bound g hq
  apply vertical_shadow_entry
  · exact ⟨g.toBoardSym.ne_iff.mpr hq.1,g.toBoardSym.ne_iff.mpr hq.2.1,
      g.toBoardSym.ne_iff.mpr hq.2.2.1,rfl⟩
  · exact ht
  · exact low
  · exact high
  · exact wx
  · exact wy
  · exact gap
  · exact clear

theorem framed_blocked_file_entry (g : QueenSym) {q : Position} {σ : Colour}
    {sk qs wk : Square} (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (low : (g.f sk).1.val+(g.f sk).2.val ≤ 4)
    (high : 9 ≤ (g.f wk).1.val+(g.f wk).2.val)
    (wx : (g.f wk).1.val ≤ 5) (wy : (g.f wk).2.val ≤ 5)
    (gap : (g.f qs).1.val+1 = (g.f wk).1.val) (hc : inCheck q σ.opp = false) :
    MateWithin σ 55 q := by
  apply unframe_bound g hq
  have material : IsKQK (pos σ (g.f sk) (g.f qs) (g.f wk) q.turn)
      σ (g.f sk) (g.f qs) (g.f wk) :=
    ⟨g.toBoardSym.ne_iff.mpr hq.1,g.toBoardSym.ne_iff.mpr hq.2.1,
      g.toBoardSym.ne_iff.mpr hq.2.2.1,rfl⟩
  apply blocked_file_entry_bound material ht low high wx wy gap
  cases he : inCheck (pos σ (g.f sk) (g.f qs) (g.f wk) q.turn) σ.opp
  · rfl
  · have check := (weak_check material).mp he
    have original : dInf sk wk = 1 ∨ QueenSees qs wk sk wk := by
      simpa only [g.dInf_eq,g.sees_iff] using check
    have wrong := (weak_check hq).mpr original
    rw [hc] at wrong; cases wrong

end EndgameChess.Rules.KQK
