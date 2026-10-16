import EndgameChess.Rules.Moves

/-!
Evaluation-only cross-check (NOT a proof; nothing here is a theorem).

Runs perft on the Lean kernel's move generator, for the initial position and for
published test positions (Chess Programming Wiki, "Perft Results"), which exercise
castling, en passant (including en-passant pins), promotion and checks. The same
positions are counted by the independent `scripts/perft.py`.

Run with `lake env lean Checks/Perft.lean`.
-/

open EndgameChess.KK EndgameChess.Rules

def fin8 (n : Nat) : Fin 8 := ⟨n % 8, Nat.mod_lt _ (by decide)⟩

def pieceOfChar (ch : Char) : Option Piece :=
  let c : Colour := if ch.isUpper then .white else .black
  match ch.toUpper with
  | 'K' => some ⟨c, .king⟩
  | 'Q' => some ⟨c, .queen⟩
  | 'R' => some ⟨c, .rook⟩
  | 'B' => some ⟨c, .bishop⟩
  | 'N' => some ⟨c, .knight⟩
  | 'P' => some ⟨c, .pawn⟩
  | _ => none

/-- One FEN rank (`rank` = 0..7), from the a-file. -/
def parseRow (rank : Nat) : Nat → List Char → List (Square × Piece)
  | _, [] => []
  | f, ch :: rest =>
    if ch.isDigit then parseRow rank (f + (ch.toNat - '0'.toNat)) rest
    else match pieceOfChar ch with
      | some pc => ((fin8 f, fin8 rank), pc) :: parseRow rank (f + 1) rest
      | none => parseRow rank f rest

def parseFen (fen : String) : Position :=
  match fen.splitOn " " with
  | place :: side :: castle :: ep :: _ =>
    let rows := place.splitOn "/"
    let placements := (rows.zipIdx).flatMap fun (row, i) => parseRow (7 - i) 0 row.toList
    let epSq : Option Square :=
      match ep.toList with
      | [fc, rc] => some (fin8 (fc.toNat - 'a'.toNat), fin8 (rc.toNat - '1'.toNat))
      | _ => none
    { board := boardOf placements,
      turn := if side == "w" then .white else .black,
      castling := ⟨castle.contains 'K', castle.contains 'Q', castle.contains 'k', castle.contains 'q'⟩,
      ep := epSq }
  | _ => initial

def report (name : String) (p : Position) (refs : List Nat) : IO Unit := do
  for (ref, i) in refs.zipIdx do
    let n := perft p (i + 1)
    IO.println s!"{name} perft({i + 1}) = {n} {if n == ref then "OK" else s!"MISMATCH (expected {ref})"}"

#eval report "initial" initial [20, 400, 8902]
#eval report "kiwipete" (parseFen "r3k2r/p1ppqpb1/bn2pnp1/3PN3/1p2P3/2N2Q1p/PPPBBPPP/R3K2R w KQkq -") [48, 2039]
#eval report "position3" (parseFen "8/2p5/3p4/KP5r/1R3p1k/8/4P1P1/8 w - -") [14, 191, 2812]
#eval report "position4" (parseFen "r3k2r/Pppp1ppp/1b3nbN/nP6/BBP1P3/q4N2/Pp1P2PP/R2Q1RK1 w kq -") [6, 264]
#eval report "position5" (parseFen "rnbq1k1r/pp1Pbppp/2p5/8/2B5/8/PPP1NnPP/RNBQK2R w KQ -") [44, 1486]
