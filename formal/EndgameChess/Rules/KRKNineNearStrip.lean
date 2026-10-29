import EndgameChess.Rules.KRKNineEntry
import EndgameChess.Rules.KRKEightNearStrip
import EndgameChess.Rules.KRKNineGeometry

namespace EndgameChess.Rules.KRKNineNearStrip
open EndgameChess.KK
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

def RookCondition (rs : Square) : Prop :=
  rs.2.val = 3 ∨ 4 ≤ rs.1.val ∨ (rs.1.val = 3 ∧ 2 ≤ rs.2.val)

def Nine (sk rs : Square) : Prop :=
  (rs.2.val = 3 ∧ 3 ≤ rs.1.val ∧ dInf sk (3,1) = 1) ∨
  (sk = ((3 : Fin 8),1) ∧ RookCondition rs)

theorem rook_line_necessary {rs nr : Square} (apart : ((3 : Fin 8),1) ≠ rs)
    (sees : RookSees rs nr (3,1) (1,2)) (row : nr.2.val = 3) (width : 3 ≤ nr.1.val) :
    RookCondition rs := by
  simp only [RookSees,RookLine,OnSeg,ne_iff_coords] at sees apart
  dsimp [RookCondition] at *
  omega

theorem rook_destination {rs : Square} (condition : RookCondition rs) :
    ∃ nr, RookSees rs nr (3,1) (1,2) ∧ nr.2.val = 3 ∧ 3 ≤ nr.1.val := by
  by_cases row : rs.2.val = 3
  · let x : Fin 8 := if rs.1.val = 3 then 4 else 3
    have width : 3 ≤ x.val ∧ x.val ≠ rs.1.val := by dsimp [x]; split <;> (try simp_all) <;> omega
    refine ⟨(x,3),?_,rfl,width.1⟩
    simp only [RookSees,RookLine,OnSeg,ne_iff_coords,row]
    simp <;> omega
  · refine ⟨(rs.1,3),?_,rfl,?_⟩
    · dsimp [RookCondition] at condition
      simp only [RookSees,RookLine,OnSeg,ne_iff_coords]
      simp <;> omega
    · dsimp [RookCondition] at condition
      change 3 ≤ rs.1.val
      omega

theorem necessary {q : Position} {σ : Colour} {sk rs : Square}
    (material : IsKRK q σ sk rs (1,2)) (turn : q.turn = σ) (win : MateWithin σ 9 q) : Nine sk rs := by
  rcases win with goal | ⟨_,chosen | defended⟩
  · exact False.elim (opp_ne σ (turn.symm.trans goal.1))
  · obtain ⟨_,r,⟨m,legal,rfl⟩,child⟩ := chosen
    obtain ⟨ns,nr,next⟩ := krk_strong_material material turn legal
    have nextTurn : (play q m).turn = σ.opp := by rw [play_turn,turn]
    have far := KRKEdgeDepth.arrival_far ⟨m,legal,rfl⟩ next
    have notMate : ¬MatedK (play q m) := by
      intro mate
      have zero := KRKEdgeDepth.terminal_depth_zero ((KRKMateGeometry.kernel_mate_iff next nextTurn far).mp mate)
      change 1 = 0 at zero
      contradiction
    rcases KRKNineEntry.eight_entry_move material turn legal next notMate child with
      ⟨_,_,distance,moved,clear⟩ | ⟨_,_,sees,moved,clear⟩
    · have region := KRKEightNearStrip.necessary moved.1 (KRKEdgeDepth.arrival_far ⟨m,legal,rfl⟩ moved) clear
      obtain ⟨_,_,sx,sy,ry,rx⟩ := region
      have target : m.dst = ((3 : Fin 8),1) := Prod.ext (Fin.ext sx) (Fin.ext sy)
      rw [target] at distance
      exact Or.inl ⟨ry,rx,distance⟩
    · have region := KRKEightNearStrip.necessary moved.1 (KRKEdgeDepth.arrival_far ⟨m,legal,rfl⟩ moved) clear
      obtain ⟨_,_,sx,sy,ry,rx⟩ := region
      have king : sk = ((3 : Fin 8),1) := Prod.ext (Fin.ext sx) (Fin.ext sy)
      rw [king] at sees
      exact Or.inr ⟨king,rook_line_necessary (king ▸ material.1) sees ry rx⟩
  · exact False.elim (opp_ne σ (turn.symm.trans defended.1))

theorem sufficient {q : Position} {σ : Colour} {sk rs : Square}
    (material : IsKRK q σ sk rs (1,2)) (turn : q.turn = σ) (far : 2 ≤ dInf sk (1,2))
    (condition : Nine sk rs) : MateWithin σ 9 q := by
  rcases condition with ⟨row,width,distance⟩ | ⟨king,condition⟩
  · have notRook : ((3 : Fin 8),1) ≠ rs := by simp only [ne_iff_coords,row]; dsimp; omega
    have nextFar : 2 ≤ dInf ((3 : Fin 8),1) (1,2) := by decide
    have legal := KRKOrdinaryEntry.king_legal material turn distance notRook nextFar
    have next := KRKThreePly.canonical_king_material material turn distance notRook nextFar
    have nextTurn : (play q ⟨sk,((3 : Fin 8),1),none⟩).turn = σ.opp := by rw [play_turn,turn]
    apply mateWithin_choose turn ⟨_,legal,rfl⟩
    exact (KRKEightNearStrip.kernel_eight_iff next nextTurn nextFar).mpr ⟨rfl,rfl,rfl,rfl,row,width⟩
  · obtain ⟨nr,sees,row,width⟩ := rook_destination condition
    have notKing : nr ≠ sk := by rw [king]; simp only [ne_iff_coords,row]; dsimp; omega
    have notWeak : nr ≠ ((1 : Fin 8),2) := by simp only [ne_iff_coords,row]; dsimp; omega
    have actualSees : RookSees rs nr sk (1,2) := by rwa [king]
    have legal := KRKOrdinaryEntry.rook_legal material turn actualSees notKing notWeak far
    have next := (KRKMatingMove.rook_move_model material turn legal rfl).1
    have nextTurn : (play q ⟨rs,nr,none⟩).turn = σ.opp := by rw [play_turn,turn]
    apply mateWithin_choose turn ⟨_,legal,rfl⟩
    apply (KRKEightNearStrip.kernel_eight_iff next nextTurn far).mpr
    rw [king]
    exact ⟨rfl,rfl,rfl,rfl,row,width⟩

theorem kernel_nine_iff {q : Position} {σ : Colour} {sk rs : Square}
    (material : IsKRK q σ sk rs (1,2)) (turn : q.turn = σ) (far : 2 ≤ dInf sk (1,2)) :
    MateWithin σ 9 q ↔ Nine sk rs := ⟨necessary material turn,sufficient material turn far⟩

theorem clear_iff {sk rs : Square} (distinct : sk ≠ rs) (notKing : sk ≠ ((1 : Fin 8),2))
    (notRook : rs ≠ ((1 : Fin 8),2)) (far : 2 ≤ dInf sk (1,2))
    (notCheck : ¬RookSees rs (1,2) sk (1,2)) :
    KRKNineGeometry.Clear sk rs (1,2) ↔ Nine sk rs := by
  let q := krkPos .white sk rs (1,2) .white
  have material : IsKRK q .white sk rs (1,2) := ⟨distinct,notKing,notRook,rfl⟩
  exact (KRKNineGeometry.kernel_nine_iff material rfl far notCheck).symm.trans (kernel_nine_iff material rfl far)

theorem kernel_exact_nine {q : Position} {σ : Colour} {sk rs : Square}
    (material : IsKRK q σ sk rs (1,2)) (turn : q.turn = σ) (far : 2 ≤ dInf sk (1,2))
    (notCheck : ¬RookSees rs (1,2) sk (1,2)) (condition : Nine sk rs) :
    MateWithin σ 9 q ∧ ¬MateWithin σ 8 q := by
  refine ⟨sufficient material turn far condition,?_⟩
  intro eight
  have seven := KRKEightGeometry.strong_eight_seven material turn eight
  have domain := KRKSevenReach.weak_domain ((KRKSevenGeometry.kernel_seven_iff material turn far notCheck).mp seven)
  rcases domain with edge | inner
  · change 1 = 0 at edge; contradiction
  · dsimp [KRKSixInterior.InnerCorner] at inner; omega

end EndgameChess.Rules.KRKNineNearStrip
