import EndgameChess.Rules.KQK.Complete
import EndgameChess.Rules.KRKForcing.AxisWalls
import EndgameChess.Rules.KRKBound.Pair

namespace EndgameChess.Rules.KQK
open EndgameChess.KK

def BishopSees (qs t a b : Square) : Prop :=
  KBK.onDiag qs t ∧ ¬ KBK.between qs a t ∧ ¬ KBK.between qs b t

theorem sees_split {qs t a b : Square} :
    QueenSees qs t a b ↔ RookSees qs t a b ∨ BishopSees qs t a b := by
  simp only [QueenSees,Bool.eq_false_iff]
  constructor
  · rintro ⟨hd | hl,ha,hb⟩
    · right
      have hd := diagGeom_iff_onDiag.mp hd
      exact ⟨hd,fun h => ha ((isBetween_iff_between hd).mpr h),
        fun h => hb ((isBetween_iff_between hd).mpr h)⟩
    · left
      exact ⟨hl,fun h => ha ((isBetween_iff_onSeg hl).mpr h),
        fun h => hb ((isBetween_iff_onSeg hl).mpr h)⟩
  · rintro (⟨hl,ha,hb⟩ | ⟨hd,ha,hb⟩)
    · exact ⟨Or.inr hl,fun h => ha ((isBetween_iff_onSeg hl).mp h),
        fun h => hb ((isBetween_iff_onSeg hl).mp h)⟩
    · exact ⟨Or.inl (diagGeom_iff_onDiag.mpr hd),
        fun h => ha ((isBetween_iff_between hd).mp h),
        fun h => hb ((isBetween_iff_between hd).mp h)⟩

/-- A rook/king isometry with the additional diagonal guarantee queens need. -/
structure QueenSym extends BoardSym where
  diag_iff : ∀ s t, KBK.onDiag (f s) (f t) ↔ KBK.onDiag s t

theorem QueenSym.sees_iff (g : QueenSym) (s t a b : Square) :
    QueenSees (g.f s) (g.f t) (g.f a) (g.f b) ↔ QueenSees s t a b := by
  simp only [sees_split,g.toBoardSym.sees_iff,BishopSees,KBK.between,
    g.diag_iff,g.dInf_eq]

def reflectX : QueenSym where
  toBoardSym := symX
  diag_iff s t := by
    simp only [KBK.onDiag,symX,ne_iff_coords,absDiff]; omega

def reflectY : QueenSym where
  toBoardSym := symY
  diag_iff s t := by
    simp only [KBK.onDiag,symY,ne_iff_coords,absDiff]; omega

def swap : QueenSym where
  toBoardSym := symSwap
  diag_iff s t := by
    simp only [KBK.onDiag,symSwap,ne_iff_coords,absDiff]; omega

private theorem safe_map (g : QueenSym) {sk qs wk : Square}
    (h : SafeQueen sk qs wk) : SafeQueen (g.f sk) (g.f qs) (g.f wk) := by
  simpa only [SafeQueen,LoneKing.Safe,g.dInf_eq] using h

private theorem back_reply (g : QueenSym) {q t u : Position} {σ : Colour}
    {sk qs wk : Square} (hq : IsKQK q σ sk qs wk)
    (ht : IsKQK t σ (g.f sk) (g.f qs) (g.f wk))
    (qt : q.turn = σ.opp) (tt : t.turn = σ.opp)
    (hs : SafeQueen sk qs wk) (hu : Legal t u) :
    ∃ r w, Legal q r ∧ IsKQK r σ sk qs w ∧ r.turn = σ ∧
      IsKQK u σ (g.f sk) (g.f qs) (g.f w) ∧ u.turn = σ := by
  obtain ⟨x,hm,hr,hd,hfar,hn⟩ := safe_reply ht tt (safe_map g hs) hu
  have step : dInf wk (g.f x) = 1 := by
    have eq := g.dInf_eq (g.f wk) x
    rw [g.invol] at eq
    omega
  have far : 2 ≤ dInf sk (g.f x) := by
    have eq := g.dInf_eq (g.f sk) x
    rw [g.invol] at eq
    omega
  have nq : g.f x ≠ qs := by
    intro e
    have ee : x = g.f qs := by rw [←e,g.invol]
    exact hm.2.2.1 ee.symm
  have notSeen : ¬ QueenSees qs (g.f x) sk (g.f x) := by
    intro h
    have mapped := (g.sees_iff qs (g.f x) sk (g.f x)).mpr h
    simp only [g.invol] at mapped
    exact hn mapped
  obtain ⟨r,hl,hmr,hrr⟩ := weak_move hq qt step nq far notSeen
  refine ⟨r,g.f x,hl,hmr,hrr,?_,hr⟩
  simpa only [g.invol] using hm

private theorem goal_map (g : QueenSym) {q t : Position} {σ : Colour}
    {sk qs wk : Square} (hq : IsKQK q σ sk qs wk)
    (ht : IsKQK t σ (g.f sk) (g.f qs) (g.f wk))
    (turn : t.turn = q.turn) (goal : MateGoal σ q) : MateGoal σ t := by
  have tt : t.turn = σ.opp := turn.trans goal.1
  have hs := force_weak_safe hq goal.1 (forceMate_of_goal goal)
  refine ⟨tt,?_,?_⟩
  · rw [tt,weak_check ht]
    have hc := (weak_check hq).mp (by simpa [goal.1] using goal.2.1)
    simpa only [g.dInf_eq,g.sees_iff] using hc
  · rintro ⟨u,hu⟩
    obtain ⟨r,_,hl,_,_,_,_⟩ := back_reply g hq ht goal.1 tt hs hu
    exact goal.2.2 ⟨r,hl⟩

/-- Exact preservation of a supplied upper budget under queen/king symmetry.
This transports a proved strategy; it does not compute optimal distances. -/
theorem bound_transport (g : QueenSym) {q t : Position} {σ : Colour}
    {sk qs wk : Square} {n : Nat} (hq : IsKQK q σ sk qs wk)
    (rights : q.castling = noRights)
    (ht : IsKQK t σ (g.f sk) (g.f qs) (g.f wk))
    (turn : t.turn = q.turn) (win : MateWithin σ n q) : MateWithin σ n t := by
  induction n generalizing q t sk qs wk with
  | zero => exact goal_map g hq ht turn win
  | succ n ih =>
    rcases win with goal | ⟨_,choose | defend⟩
    · exact Or.inl (goal_map g hq ht turn goal)
    · obtain ⟨qt,r,hl,hw⟩ := choose
      have tt : t.turn = σ := turn.trans qt
      rcases strong_reply hq qt rights hl with ⟨s,hm,hr,hd,hneq,hfar⟩ |
          ⟨s,hm,hr,hsee,hnes,hnew,hfar⟩
      · obtain ⟨u,hu,hum,hut⟩ := king_move ht tt
          (by rwa [g.dInf_eq]) (g.toBoardSym.ne_iff.mpr hneq) (by rwa [g.dInf_eq])
        exact mateWithin_choose tt hu
          (ih hm (noRights_after_legal rights hl) hum (hut.trans hr.symm) hw)
      · obtain ⟨u,hu,hum,hut⟩ := queen_move ht tt
          ((g.sees_iff qs s sk wk).mpr hsee)
          (g.toBoardSym.ne_iff.mpr hnes) (g.toBoardSym.ne_iff.mpr hnew)
          (by rwa [g.dInf_eq])
        exact mateWithin_choose tt hu
          (ih hm (noRights_after_legal rights hl) hum (hut.trans hr.symm) hw)
    · obtain ⟨qt,hne,hall⟩ := defend
      have tt : t.turn = σ.opp := turn.trans qt
      have source : ForceMate σ q :=
        forceMate_defend qt hne (fun r hr => ⟨n,hall r hr⟩)
      have hs := force_weak_safe hq qt source
      obtain ⟨r,hr⟩ := hne
      obtain ⟨w,hm,hrt,hd,hfar,hn⟩ := safe_reply hq qt hs hr
      have far : 2 ≤ dInf (g.f sk) (g.f w) := by rwa [g.dInf_eq]
      have ne : g.f w ≠ g.f qs := g.toBoardSym.ne_iff.mpr (Ne.symm hm.2.2.1)
      obtain ⟨u,hu,_,_⟩ := weak_move ht tt (by rwa [g.dInf_eq]) ne far
        (fun h => hn ((g.sees_iff qs w sk w).mp h))
      apply mateWithin_defend tt ⟨u,hu⟩
      intro u hu
      obtain ⟨r,w,hr,hm,hrt,hum,hut⟩ := back_reply g hq ht qt tt hs hu
      exact ih hm (noRights_after_legal rights hr) hum (hut.trans hrt.symm) (hall r hr)

end EndgameChess.Rules.KQK
