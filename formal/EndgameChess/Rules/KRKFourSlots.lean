import EndgameChess.Rules.KRKCastleFour

namespace EndgameChess.Rules.KRKFourSlots
open EndgameChess.KK KRKNativeFrame KRKFourGeometry
set_option maxHeartbeats 500000

inductive Kind where
  | c02 | c20 | c12 | c21 | c22
  | cTop (a : Fin 3) | cRight (a : Fin 3)
  | nearWest | nearMiddle | nearEast
  | middleWest | middleMiddle | middleEast

def small (a : Fin 3) : Fin 8 := ⟨a.val, by omega⟩

def Valid (wk : Square) : Kind → Prop
  | .c02 | .c20 | .c12 | .c21 | .c22 | .cTop _ | .cRight _ => wk.1.val = 0
  | .nearWest | .nearMiddle | .nearEast => wk.1.val = 1
  | _ => 2 ≤ wk.1.val ∧ wk.1.val ≤ 3

def king (wk : Square) : Kind → Square
  | .c02 => (0,2)
  | .c20 => (2,0)
  | .c12 => (1,2)
  | .c21 => (2,1)
  | .c22 => (2,2)
  | .cTop a => (small a,3)
  | .cRight a => (3,small a)
  | .nearWest => (0,2)
  | .nearMiddle => (1,2)
  | .nearEast => (2,2)
  | .middleWest => (KRKCanonicalSlots.left wk,2)
  | .middleMiddle => (wk.1,2)
  | .middleEast => (KRKCanonicalSlots.right wk,2)

def Region (wk rs : Square) : Kind → Prop
  | .c02 => 2 ≤ rs.2.val ∨ rs.1.val = 2
  | .c20 => 2 ≤ rs.1.val ∨ rs.2.val = 2
  | .c12 => 1 ≤ rs.2.val
  | .c21 => 1 ≤ rs.1.val
  | .c22 => (3 ≤ rs.1.val ∧ 3 ≤ rs.2.val) ∨ (rs.1.val = 0 ∧ 2 ≤ rs.2.val) ∨
      (rs.2.val = 0 ∧ 2 ≤ rs.1.val) ∨ (rs.1.val = 1 ∧ rs.2.val = 2) ∨
      (rs.1.val = 2 ∧ rs.2.val = 1)
  | .cTop _ => rs.1.val = 2 ∧ rs.2.val = 1
  | .cRight _ => rs.1.val = 1 ∧ rs.2.val = 2
  | .nearWest => rs.1.val = 2 ∧ 2 ≤ rs.2.val
  | .nearMiddle => 3 ≤ rs.2.val ∨ (rs.2.val = 2 ∧ 2 ≤ rs.1.val) ∨
      (rs.2.val = 1 ∧ (rs.1.val = 2 ∨ rs.1.val = 3))
  | .nearEast => (rs.1.val = 0 ∧ 2 ≤ rs.2.val) ∨
      (3 ≤ rs.1.val ∧ ¬(rs.1.val = 3 ∧ rs.2.val = 1))
  | .middleWest => rs.1.val = (KRKCanonicalSlots.right wk).val ∧ 2 ≤ rs.2.val
  | .middleMiddle => 3 ≤ rs.2.val
  | .middleEast => rs.1.val = (KRKCanonicalSlots.left wk).val ∧ 2 ≤ rs.2.val

private theorem point_eq {sk : Square} {x y : Fin 8} (hx : sk.1.val = x.val) (hy : sk.2.val = y.val) :
    sk = (x,y) := Prod.ext (Fin.ext hx) (Fin.ext hy)

/-- An exhaustive finite catalogue of every nonterminal canonical four-ply
king point and its rook region. The corner parameters each have three values. -/
theorem shape_iff {sk rs wk : Square} (rank : wk.2.val = 0) (high : wk.1.val ≤ 3) :
    Shape sk rs wk ↔ ∃ i : Kind, Valid wk i ∧ sk = king wk i ∧ Region wk rs i := by
  constructor
  · rintro (⟨corner, shape⟩ | ⟨near, shape⟩ | ⟨low, high, shape⟩)
    · rcases shape with ⟨sx, sy, region⟩ | ⟨sx, sy, region⟩ | ⟨sx, sy, region⟩ |
        ⟨sx, sy, region⟩ | ⟨sx, sy, region⟩ | ⟨sx, sy, rx, ry⟩ | ⟨sx, sy, rx, ry⟩
      · exact ⟨.c02, corner, point_eq sx sy, region⟩
      · exact ⟨.c20, corner, point_eq sx sy, region⟩
      · exact ⟨.c12, corner, point_eq sx sy, region⟩
      · exact ⟨.c21, corner, point_eq sx sy, region⟩
      · exact ⟨.c22, corner, point_eq sx sy, region⟩
      · exact ⟨.cTop ⟨sk.1.val, by omega⟩, corner, point_eq rfl sy, rx, ry⟩
      · exact ⟨.cRight ⟨sk.2.val, by omega⟩, corner, point_eq sx rfl, rx, ry⟩
    · obtain ⟨sy, west | middle | east⟩ := shape
      · exact ⟨.nearWest, near, point_eq west.1 sy, west.2⟩
      · exact ⟨.nearMiddle, near, point_eq middle.1 sy, middle.2⟩
      · exact ⟨.nearEast, near, point_eq east.1 sy, east.2⟩
    · rcases shape with last | ⟨sx, sy, ry⟩
      · obtain ⟨sy, ry, east | west⟩ := (KRKThreePly.last_middle_iff rank low (by omega)).mp last
        · refine ⟨.middleEast, ⟨low, high⟩, ?_, ?_⟩
          · apply point_eq <;> dsimp [king, KRKCanonicalSlots.right] <;> omega
          · dsimp [Region, KRKCanonicalSlots.left]; exact ⟨by omega, ry⟩
        · refine ⟨.middleWest, ⟨low, high⟩, ?_, ?_⟩
          · apply point_eq <;> dsimp [king, KRKCanonicalSlots.left] <;> omega
          · dsimp [Region, KRKCanonicalSlots.right]; exact ⟨by omega, ry⟩
      · exact ⟨.middleMiddle, ⟨low, high⟩, point_eq sx sy, ry⟩
  · rintro ⟨i, valid, equal, region⟩
    subst sk
    cases i with
    | c02 => exact Or.inl ⟨valid, Or.inl ⟨rfl,rfl,region⟩⟩
    | c20 => exact Or.inl ⟨valid, Or.inr (Or.inl ⟨rfl,rfl,region⟩)⟩
    | c12 => exact Or.inl ⟨valid, Or.inr (Or.inr (Or.inl ⟨rfl,rfl,region⟩))⟩
    | c21 => exact Or.inl ⟨valid, Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,rfl,region⟩)))⟩
    | c22 => exact Or.inl ⟨valid, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl,rfl,region⟩))))⟩
    | cTop a => exact Or.inl ⟨valid, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by dsimp [king,small]; omega,rfl,region⟩)))))⟩
    | cRight a => exact Or.inl ⟨valid, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl,by dsimp [king,small]; omega,region⟩)))))⟩
    | nearWest => exact Or.inr (Or.inl ⟨valid,rfl,Or.inl ⟨rfl,region⟩⟩)
    | nearMiddle => exact Or.inr (Or.inl ⟨valid,rfl,Or.inr (Or.inl ⟨rfl,region⟩)⟩)
    | nearEast => exact Or.inr (Or.inl ⟨valid,rfl,Or.inr (Or.inr ⟨rfl,region⟩)⟩)
    | middleMiddle => exact Or.inr (Or.inr ⟨valid.1,valid.2,Or.inr ⟨rfl,rfl,region⟩⟩)
    | middleWest =>
      have low : 2 ≤ wk.1.val := valid.1
      have top : wk.1.val ≤ 3 := valid.2
      refine Or.inr (Or.inr ⟨low,top,Or.inl ?_⟩)
      apply (KRKThreePly.last_middle_iff rank low (by omega)).mpr
      dsimp [king, Region, KRKCanonicalSlots.right, KRKCanonicalSlots.left] at region ⊢
      exact ⟨rfl,region.2,Or.inr ⟨by omega,by omega⟩⟩
    | middleEast =>
      have low : 2 ≤ wk.1.val := valid.1
      have top : wk.1.val ≤ 3 := valid.2
      refine Or.inr (Or.inr ⟨low,top,Or.inl ?_⟩)
      apply (KRKThreePly.last_middle_iff rank low (by omega)).mpr
      dsimp [king, Region, KRKCanonicalSlots.right, KRKCanonicalSlots.left] at region ⊢
      exact ⟨rfl,region.2,Or.inl ⟨by omega,by omega⟩⟩


/-- All nonmating five-ply entries are confined to these finite king points
or rook-line intersections with their explicit four-ply regions. This is a
necessary geometric restriction, not a full clock/history outcome formula. -/
def EntryCandidates (sk rs wk : Square) : Prop :=
  let g := normalize wk
  KRKEdgeDepth.depth wk = 0 ∧
    ((∃ i : Kind, Valid (g.f wk) i ∧ Region (g.f wk) (g.f rs) i ∧ dInf (g.f sk) (king (g.f wk) i) = 1) ∨
     (∃ i : Kind, Valid (g.f wk) i ∧ g.f sk = king (g.f wk) i ∧
       ∃ a : KRKCornerSlotBarriers.Axis, ∃ v : Fin 8,
         RookSees (g.f rs) (a.target (g.f rs) v) (g.f sk) (g.f wk) ∧
           Region (g.f wk) (a.target (g.f rs) v) i))

theorem entry_candidates {q : Position} {σ : Colour} {sk rs wk ns nr : Square} {m : Move}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ)
    (legal : isLegal q m = true) (next : IsKRK (play q m) σ ns nr wk)
    (notMate : ¬MatedK (play q m)) (win : MateWithin σ 4 (play q m)) :
    EntryCandidates sk rs wk := by
  have geometry := global_shape_necessary next (by rw [play_turn, turn])
    (KRKEdgeDepth.arrival_far ⟨m, legal, rfl⟩ next) notMate win
  have normal := normalize_spec geometry.1
  refine ⟨geometry.1, ?_⟩
  rcases KRKCastleFour.four_entry_move material turn legal next notMate win with
    ⟨src,promo,distance,moved,shape⟩ | ⟨src,promo,sees,moved,shape⟩
  · obtain ⟨i, valid, equal, region⟩ := (shape_iff normal.1 normal.2).mp shape
    have mappedDistance := (normalize wk).distance sk m.dst
    rw [equal, distance] at mappedDistance
    exact Or.inl ⟨i,valid,region,mappedDistance⟩
  · obtain ⟨i, valid, equal, region⟩ := (shape_iff normal.1 normal.2).mp shape
    have mappedSees := ((normalize wk).sees rs m.dst sk wk).mpr sees
    obtain ⟨a,v,target⟩ := KRKCornerSlotBarriers.line_target mappedSees.1
    rw [target] at mappedSees region
    exact Or.inr ⟨i,valid,equal,a,v,mappedSees,region⟩

theorem high_clock_necessary {s : RawHistoryLayer.State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (RawHistoryLayer.erase s) σ sk rs wk) (ongoing : RawHistoryLayer.Ongoing s)
    (turn : (RawHistoryLayer.erase s).turn = σ) (high : 94 ≤ RawClock.clock s.val.trace)
    (win : KRKHolding.F σ s) : KRKImmediate.MateNow sk rs wk ∨ EntryCandidates sk rs wk := by
  obtain ⟨n,cert⟩ := win
  cases n with
  | zero => exact False.elim (opp_ne σ (turn.symm.trans cert.1))
  | succ n =>
    rcases cert with goal | ⟨_, chosen | defended⟩
    · exact False.elim (opp_ne σ (turn.symm.trans goal.1))
    · obtain ⟨_,v,edge,child⟩ := chosen
      have childWin : KRKHolding.F σ v := ⟨n,child⟩
      obtain ⟨_,clock⟩ := KRKHighClock.winning_child_quiet material edge childWin
      obtain ⟨m,legal,rawEq⟩ := edge
      have endpoint : RawHistoryLayer.erase v = play (RawHistoryLayer.erase s) m := congrArg RawTrace.erase rawEq
      obtain ⟨ns,nr,next⟩ := krk_strong_material material turn legal
      have nextV : IsKRK (RawHistoryLayer.erase v) σ ns nr wk := by rwa [endpoint]
      have nextTurn : (RawHistoryLayer.erase v).turn = σ.opp := by rw [endpoint,play_turn,turn]
      by_cases childOngoing : RawHistoryLayer.Ongoing v
      · have deadline := (KRKDeadline.winning_deadline nextV childWin).2
        have budget : KRKDeadline.budget σ v ≤ 5 := by
          have notStrong : (RawHistoryLayer.erase v).turn ≠ σ := fun h => opp_ne σ (h.symm.trans nextTurn)
          simp only [KRKDeadline.budget,notStrong,↓reduceIte]
          omega
        have four := KRKFourPlyEscape.weak_five_to_four nextV nextTurn (mateWithin_mono deadline budget)
        have noMate : ¬MatedK (RawHistoryLayer.erase v) := by
          intro mate
          exact mate.2 (((RawAdjudication.ongoing_iff v.val).mp childOngoing).2.1)
        rw [endpoint] at four noMate
        exact Or.inr (entry_candidates material turn legal next noMate four)
      · have goal := (KRKHighClock.terminal_force_iff_goal childOngoing).mp childWin
        exact Or.inl ((KRKImmediate.admitted_immediate_iff material ongoing turn).mp ⟨v,⟨m,legal,rawEq⟩,goal⟩)
    · exact False.elim (opp_ne σ (turn.symm.trans defended.1))

end EndgameChess.Rules.KRKFourSlots
