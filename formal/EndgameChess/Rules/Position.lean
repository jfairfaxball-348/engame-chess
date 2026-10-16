import EndgameChess.Rules.Board

/-!
# Rules kernel K1 — positions and the initial position (FIDE 2023 Articles 1.2, 2.3, 3.7.3.2, 3.8.2.1)

A position records what Article 3 needs in order to decide which moves are legal:
- the placement of pieces (at most one per square, Art. 3.1);
- the side having the move (Art. 1.2, 1.3);
- the four castling rights (Art. 3.8.2.1 depends on history: has the king or the rook moved?);
- the en-passant target, i.e. the square a pawn has just passed over in a two-square
  advance (Art. 3.7.3.1–3.7.3.2: "only legal on the move following this advance").

Clocks and repetition counters (Art. 9) are not part of Article 3 legality and are omitted.
-/

namespace EndgameChess.Rules

open EndgameChess.KK

abbrev Board := Square → Option Piece

/-- Art. 3.8.2.1 castling rights: White/Black, king side (h-rook) / queen side (a-rook). -/
structure CastlingRights where
  whiteKing : Bool
  whiteQueen : Bool
  blackKing : Bool
  blackQueen : Bool
  deriving DecidableEq, Repr

structure Position where
  board : Board
  turn : Colour
  castling : CastlingRights
  /-- The square passed over by a pawn that has just advanced two squares, if any. -/
  ep : Option Square

/-- Art. 2.3 (diagram): back-rank order a–h is R N B Q K B N R. -/
def backRank (file : Nat) : PieceType :=
  match file with
  | 0 => .rook
  | 1 => .knight
  | 2 => .bishop
  | 3 => .queen
  | 4 => .king
  | 5 => .bishop
  | 6 => .knight
  | _ => .rook

/-- Art. 2.3: the initial placement. White on ranks 1–2, Black on ranks 7–8. -/
def initialBoard : Board := fun s =>
  if s.2.val = 0 then some ⟨.white, backRank s.1.val⟩
  else if s.2.val = 1 then some ⟨.white, .pawn⟩
  else if s.2.val = 6 then some ⟨.black, .pawn⟩
  else if s.2.val = 7 then some ⟨.black, backRank s.1.val⟩
  else none

/-- Art. 1.2: White moves first. All castling rights are present; there is no en-passant target. -/
def initial : Position :=
  { board := initialBoard, turn := .white,
    castling := ⟨true, true, true, true⟩, ep := none }

/-- A board given by a list of placements (for examples). -/
def boardOf (l : List (Square × Piece)) : Board := fun s =>
  (l.find? (fun e => e.1 == s)).map (·.2)

/-- Number of occupied squares. -/
def pieceCount (b : Board) : Nat := (allSquares.filter fun s => (b s).isSome).length

/-- Number of squares holding exactly the piece `pc`. -/
def countOf (b : Board) (pc : Piece) : Nat := (allSquares.filter fun s => b s == some pc).length

/-- The initial position is well formed: 32 pieces, one king of each colour, 8 pawns each. -/
theorem initial_wellFormed :
    pieceCount initial.board = 32 ∧
    countOf initial.board ⟨.white, .king⟩ = 1 ∧ countOf initial.board ⟨.black, .king⟩ = 1 ∧
    countOf initial.board ⟨.white, .pawn⟩ = 8 ∧ countOf initial.board ⟨.black, .pawn⟩ = 8 ∧
    countOf initial.board ⟨.white, .queen⟩ = 1 ∧ countOf initial.board ⟨.black, .queen⟩ = 1 ∧
    initial.turn = .white ∧ initial.castling = ⟨true, true, true, true⟩ ∧ initial.ep = none := by
  decide

end EndgameChess.Rules
