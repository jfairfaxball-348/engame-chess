import EndgameChess.Rules.KRKSevenPrefix

namespace EndgameChess.Rules.KRKSevenSlots
open EndgameChess.KK KRKNativeFrame
set_option maxHeartbeats 300000

/-- At most twenty fixed king points; rook inequalities remain symbolic.
This rectangle contains all winning canonical six-ply destination points. -/
abbrev Kind := Fin 5 × Fin 4

def point (i : Kind) : Square :=
  (⟨i.1.val,by have := i.1.isLt; omega⟩,⟨i.2.val,by have := i.2.isLt; omega⟩)

def frame (wk : Square) : Frame :=
  if KRKEdgeDepth.depth wk = 0 then normalize wk
  else Frame.ofSym (KRKSixInwardCorner.innerSym wk)

theorem region_bounds {sk rs wk : Square} (region : KRKSixGlobal.Region sk rs wk) :
    ((frame wk).f sk).1.val < 5 ∧ ((frame wk).f sk).2.val < 4 := by
  by_cases edge : KRKEdgeDepth.depth wk = 0
  · simp only [frame,edge,↓reduceIte]
    simp only [KRKSixGlobal.Region,edge,↓reduceIte] at region
    rcases region with ⟨file,h⟩ | ⟨file,h⟩ | ⟨file,h⟩ | ⟨file,h⟩
    · dsimp [KRKSixCorner.Region] at h; omega
    · dsimp [KRKSixNear.Region,KRKSixNear.Extra,KRKFourPlyNearCorner.NearFour] at h; omega
    · dsimp [KRKSixSecond.Region] at h; omega
    · dsimp [KRKSixMiddle.Region] at h; omega
  · simp only [frame,edge,↓reduceIte,Frame.ofSym]
    simp only [KRKSixGlobal.Region,edge,↓reduceIte,KRKSixInwardCorner.GlobalRegion] at region
    dsimp [KRKSixInwardCorner.Region] at region
    omega

theorem region_point {sk rs wk : Square} (region : KRKSixGlobal.Region sk rs wk) :
    ∃ i : Kind, (frame wk).f sk = point i := by
  have bounds := region_bounds region
  let i : Kind := (⟨((frame wk).f sk).1.val,bounds.1⟩,⟨((frame wk).f sk).2.val,bounds.2⟩)
  exact ⟨i,Prod.ext (Fin.ext rfl) (Fin.ext rfl)⟩

end EndgameChess.Rules.KRKSevenSlots
