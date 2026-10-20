import EndgameChess.Rules.KRKBound.Definitions
namespace EndgameChess.Rules
/-- Only terminal rank-edge aligned exits earn the one-ply rather than four-ply budget. -/
def wallEdgeCredit (n : Nat) : Nat := if n = 1 then 3 else 0
end EndgameChess.Rules
