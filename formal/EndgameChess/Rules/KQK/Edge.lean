import EndgameChess.Rules.KQK.Geometry
import EndgameChess.Rules.KRKBound.Pair

namespace EndgameChess.Rules.KQK
open EndgameChess.KK

def EdgeWall (sk qs wk : Square) : Prop :=
  sk.2.val ≤ 5 ∧ qs.2.val = 6 ∧ wk.2.val = 7 ∧
    qs.1.val ≤ 4 ∧ qs.1.val + 2 ≤ wk.1.val

/-- An edge corridor has an explicit legal horizontal reply. The width
condition is essential: a one-square corridor can be stalemate. -/
theorem edge_reply_exists {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ.opp)
    (he : EdgeWall sk qs wk) : ∃ r, Legal q r := by
  obtain ⟨hsk,hqY,hwY,hqX,hwX⟩ := he
  let tx : Nat := if wk.1.val = 7 then 6 else wk.1.val+1
  have htx : tx < 8 ∧ qs.1.val+2 ≤ tx ∧ absDiff wk.1.val tx = 1 := by
    have hbound := wk.1.isLt
    dsimp [tx]; split <;> simp only [absDiff] <;> omega
  let t : Square := (⟨tx,htx.1⟩,7)
  have hd : dInf wk t = 1 := by
    simp only [dInf,absDiff,t] at htx ⊢; omega
  have htn : t ≠ qs := by simp only [ne_iff_coords,t]; omega
  have hfar : 2 ≤ dInf sk t := by simp only [dInf,absDiff,t]; omega
  have hn : ¬ QueenSees qs t sk t := by
    apply not_sees_of_not_line
    · dsimp [t]; omega
    · dsimp [t]; omega
    · simp only [t,absDiff]; omega
  obtain ⟨r,hr,_,_⟩ := weak_move hq ht hd htn hfar hn
  exact ⟨r,hr⟩

theorem edge_reply {q r : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ.opp)
    (he : EdgeWall sk qs wk) (hl : Legal q r) :
    ∃ t, IsKQK r σ sk qs t ∧ r.turn = σ ∧ EdgeWall sk qs t ∧ dInf wk t = 1 := by
  obtain ⟨hsk,hqY,hwY,hqX,hwX⟩ := he
  have hs : SafeQueen sk qs wk := Or.inl (by simp only [dInf,absDiff]; omega)
  obtain ⟨t,hm,hr,hd,_,hn⟩ := safe_reply hq ht hs hl
  have hy : t.2.val = 7 := by
    have above := rook_rank_barrier (sk := sk) (rs := qs) (wk := wk)
      (by omega) (by omega) hd (Ne.symm hm.2.2.1)
      (fun h => hn (rook_sees_queen h))
    have bound := t.2.isLt
    omega
  have hx : qs.1.val+2 ≤ t.1.val := by
    have step : wk.1.val ≤ t.1.val+1 := by simp only [dInf,absDiff] at hd; omega
    by_cases h : qs.1.val+2 ≤ t.1.val
    · exact h
    · have adjacent : dInf qs t = 1 := by simp only [dInf,absDiff]; omega
      exact False.elim (hn (near_sees adjacent))
  exact ⟨t,hm,hr,⟨hsk,hqY,hy,hqX,hx⟩,hd⟩

def toward (a b : Fin 8) : Fin 8 :=
  ⟨if a.val < b.val then a.val+1 else if b.val < a.val then a.val-1 else a.val,
    by have ha := a.isLt; have hb := b.isLt; split <;> (try split) <;> omega⟩

def towardSquare (s t : Square) : Square := (toward s.1 t.1,toward s.2 t.2)

theorem toward_step {s t : Square} (hne : s ≠ t) :
    dInf s (towardSquare s t) = 1 ∧
    dInf (towardSquare s t) t + 1 = dInf s t := by
  have hd : dInf s t ≠ 0 := fun h => hne (dInf_eq_zero_iff.mp h)
  simp only [towardSquare,toward,dInf,absDiff] at hd ⊢
  split <;> (try split) <;> (try split) <;> (try split) <;> omega

def CornerPrison (sk qs wk : Square) : Prop :=
  EdgeWall sk qs wk ∧ qs.1.val = 4

def escort : Square := (6,5)

/-- Walking below the queen's rank preserves both weak escape squares.
The measure is king approach distance, not optimal mate distance. -/
theorem corner_prison_bound {q : Position} {σ : Colour} {sk qs wk : Square}
    (hq : IsKQK q σ sk qs wk) (ht : q.turn = σ)
    (hp : CornerPrison sk qs wk) :
    MateWithin σ (2*dInf sk escort+1) q := by
  generalize hd : dInf sk escort = d
  induction d using Nat.strongRecOn generalizing q sk wk with
  | ind d ih =>
    by_cases hz : d = 0
    · have hs : sk = escort := dInf_eq_zero_iff.mp (by omega)
      obtain ⟨⟨hsk,hqY,hwY,hqX,hwX⟩,hqx⟩ := hp
      let t : Square := (wk.1,6)
      have hsee : QueenSees qs t sk wk := by
        apply rook_sees_queen
        refine ⟨⟨?_,Or.inr (by dsimp [t]; omega)⟩,?_,?_⟩
        · simp only [t]; omega
        · simp only [OnSeg,t]; omega
        · simp only [OnSeg,t]; omega
      have hts : t ≠ sk := by simp only [ne_iff_coords,t,hs,escort]; omega
      have htw : t ≠ wk := by simp only [ne_iff_coords,t]; omega
      have hfar : 2 ≤ dInf sk wk := by simp only [dInf,absDiff,hs,escort]; omega
      obtain ⟨r,hl,hm,hr⟩ := queen_move hq ht hsee hts htw hfar
      have protect : dInf sk t = 1 := by
        have hbound := wk.1.isLt
        simp only [dInf,absDiff,t,hs,escort]; omega
      have goal : MateWithin σ 0 r :=
        ⟨hr,edge_mated hm hr hwY rfl rfl protect⟩
      have result := mateWithin_choose ht hl goal
      simpa [hz] using result
    · have hne : sk ≠ escort := fun h => by
        subst h; have hz0 := dInf_eq_zero_iff.mpr (Eq.refl escort); omega
      let su := towardSquare sk escort
      obtain ⟨hstep,hdec⟩ := toward_step hne
      have hy : su.2.val ≤ 5 := by
        have hsk := hp.1.1
        dsimp [su,towardSquare,toward,escort]
        split <;> (try split) <;> omega
      have htq : su ≠ qs := by
        have hqY := hp.1.2.1
        simp only [ne_iff_coords]; omega
      have hfar : 2 ≤ dInf su wk := by
        have hwY := hp.1.2.2.1
        simp only [dInf,absDiff]; omega
      obtain ⟨c,hl,hm,hc⟩ := king_move hq ht hstep htq hfar
      have newWall : EdgeWall su qs wk := ⟨hy,hp.1.2⟩
      have hneReply := edge_reply_exists hm hc newWall
      have hall : ∀ r, Legal c r → MateWithin σ (2*dInf su escort+1) r := by
        intro r hr
        obtain ⟨t,hmt,hrt,he,_⟩ := edge_reply hm hc newWall hr
        exact ih (dInf su escort) (by dsimp [su] at *; omega) hmt hrt ⟨he,hp.2⟩ rfl
      have result := mateWithin_pair ht hl hc hneReply hall
      have cost : 2*dInf su escort+1+2 = 2*d+1 := by dsimp [su] at *; omega
      rwa [cost] at result

end EndgameChess.Rules.KQK
