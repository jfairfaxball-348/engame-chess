import EndgameChess.Rules.KRKCentral.FullCut

namespace EndgameChess.Rules.KRKCentral

def fullCost (n : Nat) : Nat := if n≤3 then 18*(n-1)+11 else 12*n+13
def readyCost (n : Nat) : Nat := if n≤3 then 18*(n-1)+11 else 12*n+11
def prepCost (t : Nat) : Nat := 2*(t+t/2+1)

end EndgameChess.Rules.KRKCentral
