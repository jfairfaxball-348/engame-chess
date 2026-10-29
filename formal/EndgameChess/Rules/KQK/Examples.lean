import EndgameChess.Rules.KQK.FramedFinish
import EndgameChess.Rules.KQK.ShadowForce
import EndgameChess.Rules.KQK.Staircase
import EndgameChess.Rules.KQK.EdgeEntry

/-! A few kernel-checked non-vacuity/control examples, not a position table. -/
namespace EndgameChess.Rules.KQK
open EndgameChess.KK

def cornerExample : Position := pos .white (0,0) (4,6) (6,7) .white

theorem corner_example_bound : MateWithin .white 15 cornerExample := by
  apply corner_prison_fifteen
  · exact ⟨by decide,by decide,by decide,rfl⟩
  · rfl
  · unfold CornerPrison EdgeWall; decide

def stalemateExample : Position := pos .white (2,5) (1,5) (0,7) .black

theorem stalemate_example_no_force : ¬ ForceMate .white stalemateExample := by
  apply stalemate_not_forceMate (by decide)
  rintro ⟨r,hr⟩
  obtain ⟨m,hm,_⟩ := hr
  have empty : legalMoves stalemateExample = [] := by decide
  have mem := mem_legalMoves.mpr hm
  rw [empty] at mem
  exact List.not_mem_nil mem

def shadowExample : Position := pos .white (0,0) (3,2) (4,4) .white

theorem shadow_example_bound : MateWithin .white 53 shadowExample := by
  apply shadow_strong_bound
  · exact ⟨by decide,by decide,by decide,rfl⟩
  · rfl
  · unfold Shadow; decide
  · decide

def blockedEntryExample : Position := pos .white (3,1) (3,0) (4,5) .white

theorem blocked_entry_example_bound : MateWithin .white 55 blockedEntryExample := by
  apply blocked_file_entry_bound
  · exact ⟨by decide,by decide,by decide,rfl⟩
  · rfl
  · decide
  · decide
  · decide
  · decide
  · rfl
  · decide

def staircaseExample : Position := pos .white (0,0) (1,6) (4,5) .white

theorem staircase_example_bound : MateWithin .white 81 staircaseExample := by
  apply staircase_eighty_one
  · exact ⟨by decide,by decide,by decide,rfl⟩
  · rfl
  · unfold Staircase; decide

def horizontalEntryExample : Position := pos .white (0,0) (7,1) (4,5) .white

theorem horizontal_entry_example_bound : MateWithin .white 55 horizontalEntryExample := by
  apply horizontal_alignment_entry
  · exact ⟨by decide,by decide,by decide,rfl⟩
  · rfl
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · unfold OnSeg; decide

def topLeftEntryExample : Position := pos .white (5,7) (0,6) (7,7) .white

theorem top_left_entry_example_bound : MateWithin .white 41 topLeftEntryExample := by
  apply corridor_bound
  · exact ⟨by decide,by decide,by decide,rfl⟩
  · rfl
  · unfold Corridor; decide
  · decide

def cornerEvacuationExample : Position := pos .white (7,7) (3,6) (5,7) .white

theorem corner_evacuation_example_bound : MateWithin .white 41 cornerEvacuationExample := by
  apply corridor_bound
  · exact ⟨by decide,by decide,by decide,rfl⟩
  · rfl
  · unfold Corridor; decide
  · decide

set_option maxRecDepth 4096 in
/-- A legal direct king evacuation can stalemate. The general strategy
widens the queen corridor first in exactly this boundary configuration. -/
theorem direct_evacuation_stalemate :
    isLegal cornerEvacuationExample ⟨(7,7),(7,6),none⟩ = true ∧
    ¬ ForceMate .white (play cornerEvacuationExample ⟨(7,7),(7,6),none⟩) := by
  constructor
  · decide
  · apply stalemate_not_forceMate (by decide)
    rintro ⟨r,hr⟩
    obtain ⟨m,hm,_⟩ := hr
    have empty : legalMoves (play cornerEvacuationExample ⟨(7,7),(7,6),none⟩) = [] := by decide
    have mem := mem_legalMoves.mpr hm
    rw [empty] at mem
    exact List.not_mem_nil mem

end EndgameChess.Rules.KQK
