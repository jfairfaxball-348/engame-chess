import EndgameChess.Rules.KQK.FramedFinish

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

end EndgameChess.Rules.KQK
