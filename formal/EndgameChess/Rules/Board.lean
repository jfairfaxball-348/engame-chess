import EndgameChess.KK

/-!
# Rules kernel K1 — board, colours, pieces (FIDE 2023 Articles 2.1–2.4)

Reuses `EndgameChess.KK.Square` (`Fin 8 × Fin 8`, `(file, rank)`, `(0,0)` = a1) and
`EndgameChess.KK.Colour` so that the K2 agreement proofs need no change of carrier.
The frozen module `EndgameChess.KK` is imported, never edited.
-/

namespace EndgameChess.Rules

open EndgameChess.KK

/-- Art. 2.2: king, queen, rook, bishop, knight, pawn. -/
inductive PieceType
  | king
  | queen
  | rook
  | bishop
  | knight
  | pawn
  deriving DecidableEq, Repr

/-- A piece: its colour and type. -/
structure Piece where
  colour : Colour
  kind : PieceType
  deriving DecidableEq, Repr

/-- Art. 3.7.3.3: a pawn may be exchanged for a queen, rook, bishop or knight. -/
inductive PromoPiece
  | queen
  | rook
  | bishop
  | knight
  deriving DecidableEq, Repr

def PromoPiece.toKind : PromoPiece → PieceType
  | .queen => .queen
  | .rook => .rook
  | .bishop => .bishop
  | .knight => .knight

/-- All 64 squares. -/
def allSquares : List Square :=
  (List.finRange 8).flatMap fun x => (List.finRange 8).map fun y => (x, y)

theorem mem_allSquares (s : Square) : s ∈ allSquares := by
  obtain ⟨x, y⟩ := s
  simp only [allSquares, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and]
  exact ⟨x, y, rfl⟩

/-- Art. 2.1: a1 is dark; the light ('white') squares are those with odd file+rank. -/
def isLightSquare (s : Square) : Bool := (s.1.val + s.2.val) % 2 == 1

/-- The direction a pawn of colour `c` advances along the ranks (White up, Black down). -/
def forward : Colour → Int
  | .white => 1
  | .black => -1

/-- Each player's first rank (Art. 3.8.2: castling is along the player's first rank). -/
def homeRank : Colour → Fin 8
  | .white => 0
  | .black => 7

/-- Rank on which a colour's pawns start (Art. 2.3). -/
def pawnRank : Colour → Nat
  | .white => 1
  | .black => 6

/-- Art. 3.7.3.3: "the rank furthest from its starting position". -/
def lastRank : Colour → Nat
  | .white => 7
  | .black => 0

/-- Signed file and rank displacement from `s` to `t`. -/
def dx (s t : Square) : Int := (t.1.val : Int) - (s.1.val : Int)
def dy (s t : Square) : Int := (t.2.val : Int) - (s.2.val : Int)

end EndgameChess.Rules
