import EndgameChess.Rules.KRKCentral.Ready

namespace EndgameChess.Rules.KRKCentral
open EndgameChess.KK

def centreDistance (x : Nat) : Nat := if x<3 then 3-x else if 4<x then x-4 else 0
def prepDistance (r : Nat) (sk : Square) : Nat := max (r-(sk.2.val+1)) (centreDistance sk.1.val)

end EndgameChess.Rules.KRKCentral
