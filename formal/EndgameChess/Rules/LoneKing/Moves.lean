import EndgameChess.Rules.LoneKing.Material
import EndgameChess.Rules.ForceMate

namespace EndgameChess.Rules.LoneKing
open EndgameChess.KK

/-- All moves of the lone king are ordinary steps, independent of the enemy piece. -/
theorem weak_motion {k : PieceType} {q r : Position} {σ : Colour} {sk xs wk : Square}
    (hk : Material k q σ sk xs wk) (ht : q.turn = σ.opp) (hl : Legal q r) :
    ∃ m : Move, r = play q m ∧ m.src = wk ∧ m.promo = none ∧
      dInf wk m.dst = 1 ∧ m.dst ≠ sk ∧
      r.board = fun s => if s = m.dst then some ⟨σ.opp,.king⟩
        else if s = wk then none else board k σ sk xs wk s := by
  obtain ⟨h12,h13,h23,hb⟩ := hk
  obtain ⟨m,hm,rfl⟩ := hl
  have hp : isPseudo q m = true := by
    unfold isLegal at hm; simp only [Bool.and_eq_true] at hm; exact hm.1
  obtain ⟨pc,hpc,hcol⟩ := own_of_isPseudo hp
  rw [hb] at hpc
  rcases board_some hpc with ⟨_,rfl⟩ | ⟨_,rfl⟩ | ⟨esrc,rfl⟩
  · rw [ht] at hcol; exact False.elim (opp_ne _ hcol)
  · rw [ht] at hcol; exact False.elim (opp_ne _ hcol)
  · have hsrc : q.board m.src = some ⟨q.turn,.king⟩ := by
      rw [hb,ht,esrc]; exact board_wk h13 h23
    have hnc : canCastle q m = false := by
      apply canCastle_false_of_noRook
      intro s hs
      rw [hb,ht] at hs
      rcases board_some hs with ⟨_,h⟩ | ⟨_,h⟩ | ⟨_,h⟩
      · simp at h
      · have hh := congrArg Piece.colour h
        exact opp_ne σ hh.symm
      · simp at h
    rw [isPseudo_of_king hsrc,hnc] at hp
    simp only [Bool.or_false,Bool.and_eq_true,Option.isNone_iff_eq_none] at hp
    obtain ⟨htg,hpro,hg⟩ := hp
    have hd : dInf wk m.dst = 1 := by rw [← esrc]; exact kingGeom_iff.1 hg
    have hdk : m.dst ≠ sk := by
      intro e
      have hh := (targetOK_some htg (by rw [hb,e]; exact board_sk)).2
      exact hh rfl
    refine ⟨m,rfl,esrc,hpro,hd,hdk,?_⟩
    rw [play_board_simple hsrc (by decide) hpro (fun _ => by rw [esrc]; exact hd)]
    rw [ht,esrc,hb]

/-- A weak reply preserves material or captures the extra piece into KK. -/
theorem weak_cases {k : PieceType} {q r : Position} {σ : Colour} {sk xs wk : Square}
    (hk : Material k q σ sk xs wk) (ht : q.turn = σ.opp) (hl : Legal q r) :
    (∃ t, Material k r σ sk xs t ∧ r.turn = σ) ∨ (∃ w b, IsKK r w b) := by
  obtain ⟨h12,h13,h23,hb⟩ := hk
  obtain ⟨m,hr,_,_,_,hdk,hbp⟩ := weak_motion ⟨h12,h13,h23,hb⟩ ht hl
  have hturn : r.turn = σ := by rw [hr,play_turn,ht,opp_opp]
  by_cases hcap : m.dst = xs
  · right
    cases σ with
    | white =>
      refine ⟨sk,m.dst,Ne.symm hdk,?_⟩
      rw [hbp]; funext x; rw [hcap]; unfold board kkBoard
      by_cases e1 : x = xs
      · subst e1; simp [Ne.symm h12,Colour.opp]
      · by_cases e2 : x = wk
        · subst e2; simp [e1,Ne.symm h13]
        · simp [e1,e2]
    | black =>
      refine ⟨m.dst,sk,hdk,?_⟩
      rw [hbp]; funext x; rw [hcap]; unfold board kkBoard
      by_cases e1 : x = xs
      · subst e1; simp [Colour.opp]
      · by_cases e2 : x = wk
        · subst e2; simp [e1,Ne.symm h13]
        · by_cases e3 : x = sk <;> simp [e1,e2,e3,h12,h13]
  · left
    refine ⟨m.dst,⟨h12,Ne.symm hdk,Ne.symm hcap,?_⟩,hturn⟩
    rw [hbp]; funext x; unfold board
    by_cases e1 : x = m.dst
    · subst e1; simp [hdk,hcap]
    · by_cases e2 : x = wk
      · subst e2; simp [e1,Ne.symm h13,Ne.symm h23]
      · simp [e1,e2]

def Safe (sk xs wk : Square) : Prop := 2 ≤ dInf xs wk ∨ dInf sk xs = 1

/-- Distance or king protection excludes capture, for every extra-piece kind. -/
theorem safe_reply {k : PieceType} {q r : Position} {σ : Colour} {sk xs wk : Square}
    (hk : Material k q σ sk xs wk) (ht : q.turn = σ.opp)
    (hs : Safe sk xs wk) (hl : Legal q r) :
    ∃ t, Material k r σ sk xs t ∧ r.turn = σ ∧ dInf wk t = 1 := by
  obtain ⟨h12,h13,h23,hb⟩ := hk
  obtain ⟨m,hr,_,_,hd,hdk,hbp⟩ := weak_motion ⟨h12,h13,h23,hb⟩ ht hl
  have hcap : m.dst ≠ xs := by
    intro e
    rcases hs with far | protect
    · rw [e,dInf_comm] at hd; omega
    · have hcheck : inCheck r σ.opp = true := by
        rw [inCheck_iff]
        refine ⟨m.dst,?_,?_⟩
        · rw [hbp]; simp
        · rw [EndgameChess.Rules.attacked_iff,opp_opp]
          refine ⟨sk,⟨σ,.king⟩,?_,rfl,?_⟩
          · rw [hbp]; simp [Ne.symm hdk,h13,board_sk]
          · simpa [attacksFrom,kingGeom_iff,e] using protect
      have hn := legal_mover_safe hl
      rw [ht,hcheck] at hn
      cases hn
  refine ⟨m.dst,⟨h12,Ne.symm hdk,Ne.symm hcap,?_⟩,?_,hd⟩
  · rw [hbp]; funext x; unfold board
    by_cases e1 : x = m.dst
    · subst e1; simp [hdk,hcap]
    · by_cases e2 : x = wk
      · subst e2; simp [e1,Ne.symm h13,Ne.symm h23]
      · simp [e1,e2]
  · rw [hr,play_turn,ht,opp_opp]

/-- Every adjacent unprotected non-king piece is legally capturable into KK. -/
theorem unprotected_capture {k : PieceType} (nk : k ≠ .king)
    {q : Position} {σ : Colour} {sk xs wk : Square}
    (hk : Material k q σ sk xs wk) (ht : q.turn = σ.opp)
    (ha : dInf wk xs = 1) (hf : 2 ≤ dInf sk xs) :
    ∃ r, Legal q r ∧ ∃ w b, IsKK r w b := by
  obtain ⟨h12,h13,h23,hb⟩ := hk
  let m : Move := ⟨wk,xs,none⟩
  have hsrc : q.board m.src = some ⟨q.turn,.king⟩ := by
    rw [hb,ht]; exact board_wk h13 h23
  have hp : isPseudo q m = true := by
    rw [isPseudo_of_king hsrc]
    have hd : q.board m.dst = some ⟨σ,k⟩ := by rw [hb]; exact board_xs h12
    simp [targetOK,hd,ht,m,kingGeom_iff,ha,nk,fun h => opp_ne σ h]
  have hbp := play_board_simple hsrc (by decide) rfl (fun _ => ha)
  have hkk : ∃ w b, IsKK (play q m) w b ∧ 2 ≤ dInf w b := by
    cases σ with
    | white =>
      refine ⟨sk,xs,⟨h12,?_⟩,hf⟩
      rw [hbp]; funext x; rw [hb,ht]; unfold board kkBoard
      by_cases e1 : x = xs
      · subst e1; simp [m,Ne.symm h12,Colour.opp]
      · by_cases e2 : x = wk
        · subst e2; simp [m,e1,Ne.symm h13]
        · simp [m,e1,e2]
    | black =>
      refine ⟨xs,sk,⟨Ne.symm h12,?_⟩,by rwa [dInf_comm]⟩
      rw [hbp]; funext x; rw [hb,ht]; unfold board kkBoard
      by_cases e1 : x = xs
      · subst e1; simp [m,Colour.opp]
      · by_cases e2 : x = wk
        · subst e2; simp [m,e1,Ne.symm h13]
        · by_cases e3 : x = sk <;> simp [m,e1,e2,e3,h12,h13]
  obtain ⟨w,b,hkk,hdist⟩ := hkk
  have hc : inCheck (play q m) q.turn = false := by
    cases he : inCheck (play q m) q.turn
    · rfl
    · have hh : inCheck (ofKK ⟨w,b,(play q m).turn⟩) q.turn = true := by
        rw [inCheck_of_board (p := ofKK ⟨w,b,(play q m).turn⟩) (q := play q m)
          (by exact hkk.2.symm)]
        exact he
      have hh := (inCheck_ofKK (a := ⟨w,b,(play q m).turn⟩) hkk.1 q.turn).1 hh
      dsimp only at hh
      omega
  exact ⟨play q m,legal_of_pseudo hp hc,w,b,hkk⟩

theorem force_weak_safe {k : PieceType} (nk : k ≠ .king)
    {q : Position} {σ : Colour} {sk xs wk : Square}
    (hk : Material k q σ sk xs wk) (ht : q.turn = σ.opp)
    (hw : ForceMate σ q) : Safe sk xs wk := by
  classical
  by_cases hs : Safe sk xs wk
  · exact hs
  have h0 : dInf xs wk ≠ 0 := fun h => hk.2.2.1 (dInf_eq_zero_iff.1 h)
  have h1 : dInf sk xs ≠ 0 := fun h => hk.1 (dInf_eq_zero_iff.1 h)
  have ha : dInf wk xs = 1 := by
    simp only [Safe,not_or] at hs
    rw [dInf_comm]; omega
  have hf : 2 ≤ dInf sk xs := by simp only [Safe,not_or] at hs; omega
  obtain ⟨r,hl,w,b,hkk⟩ := unprotected_capture nk hk ht ha hf
  exact False.elim (dead_reply_not_forceMate ht hl (dead_of_legal_into_KK hl hkk) hw)

end EndgameChess.Rules.LoneKing
