import EndgameChess.Rules.KRKThirteenEntry

namespace EndgameChess.Rules.KRKThirteenSlots
open EndgameChess.KK KRKNativeFrame

/-- The fixed board-square catalogue. No position values are stored. -/
abbrev Kind := Fin 8 × Fin 8

def point (i : Kind) : Square := i

def frame (_wk : Square) : Frame := Frame.ofSym symId

theorem region_point {sk rs wk : Square} (_region : KRKTwelveGlobal.Region sk rs wk) :
    ∃ i : Kind, (frame wk).f sk = point i := ⟨sk,rfl⟩

end EndgameChess.Rules.KRKThirteenSlots
