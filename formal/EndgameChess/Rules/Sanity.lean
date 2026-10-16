import EndgameChess.Rules.Moves

/-!
# Rules kernel K1 — sanity theorems (kernel-checked by `decide`)

These are concrete facts about the encoding, not chess theorems. They check that each
special rule of Article 3 behaves as written. They live in their own module, so the
(~20 s) kernel evaluation reruns only when the move model changes.
-/

namespace EndgameChess.Rules

open EndgameChess.KK

/-- Square constructor for examples: `sq f r` with file `f` (a = 0) and rank `r` (1 = 0). -/
def sq (f r : Fin 8) : Square := (f, r)

def wK : Piece := ⟨.white, .king⟩
def bK : Piece := ⟨.black, .king⟩
def wP : Piece := ⟨.white, .pawn⟩
def bP : Piece := ⟨.black, .pawn⟩
def wR : Piece := ⟨.white, .rook⟩
def bR : Piece := ⟨.black, .rook⟩
def wB : Piece := ⟨.white, .bishop⟩

def noCastle : CastlingRights := ⟨false, false, false, false⟩

set_option maxRecDepth 100000 in
/-- The initial position has exactly 20 legal moves (16 pawn moves, 4 knight moves). -/
theorem initial_legal_count : (legalMoves initial).length = 20 := by decide

/-! ### En passant (3.7.3.1–3.7.3.2) -/

/-- White Ke1, Pe5; Black Ke8, Pd5, just played d7–d5 (target d6); White to move. -/
def epPos (target : Option Square) : Position :=
  { board := boardOf [(sq 4 0, wK), (sq 4 7, bK), (sq 4 4, wP), (sq 3 4, bP)],
    turn := .white, castling := noCastle, ep := target }

/-- exd6 e.p. is legal immediately after the advance, and it removes the d5 pawn. -/
theorem enPassant_legal :
    isLegal (epPos (some (sq 3 5))) ⟨sq 4 4, sq 3 5, none⟩ = true ∧
    (play (epPos (some (sq 3 5))) ⟨sq 4 4, sq 3 5, none⟩).board (sq 3 4) = none ∧
    (play (epPos (some (sq 3 5))) ⟨sq 4 4, sq 3 5, none⟩).board (sq 3 5) = some wP := by
  decide

/-- 3.7.3.2: "only legal on the move following this advance". With no target, it is illegal. -/
theorem enPassant_expired : isLegal (epPos none) ⟨sq 4 4, sq 3 5, none⟩ = false := by decide

/-- En passant that would expose the king along the rank is illegal (3.9.2):
White Ka5, Pb5; Black Pc5 (just advanced, target c6), Rh5, Kh8. -/
def epPinPos : Position :=
  { board := boardOf [(sq 0 4, wK), (sq 1 4, wP), (sq 2 4, bP), (sq 7 4, bR), (sq 7 7, bK)],
    turn := .white, castling := noCastle, ep := some (sq 2 5) }

theorem enPassant_exposing_king_illegal : isLegal epPinPos ⟨sq 1 4, sq 2 5, none⟩ = false := by
  decide

/-! ### Promotion (3.7.3.3–3.7.3.5) -/

/-- White Ke1, Pa7; Black Kh8; White to move. -/
def promoPos : Position :=
  { board := boardOf [(sq 4 0, wK), (sq 0 6, wP), (sq 7 7, bK)],
    turn := .white, castling := noCastle, ep := none }

theorem promotion_rules :
    isLegal promoPos ⟨sq 0 6, sq 0 7, some .queen⟩ = true ∧
    isLegal promoPos ⟨sq 0 6, sq 0 7, some .knight⟩ = true ∧
    isLegal promoPos ⟨sq 0 6, sq 0 7, none⟩ = false ∧
    (play promoPos ⟨sq 0 6, sq 0 7, some .knight⟩).board (sq 0 7) = some ⟨.white, .knight⟩ := by
  decide

/-! ### Castling (3.8.2, 3.8.2.1, 3.8.2.2) -/

/-- White Ke1, Rh1; Black Ke8, optionally Rf8; White may castle king side. -/
def castlePos (blackRookF8 : Bool) (rights : CastlingRights) : Position :=
  { board := boardOf ([(sq 4 0, wK), (sq 7 0, wR), (sq 4 7, bK)] ++
      (if blackRookF8 then [(sq 5 7, bR)] else [])),
    turn := .white, castling := rights, ep := none }

def wKOnly : CastlingRights := ⟨true, false, false, false⟩

/-- O-O is legal; the king lands on g1, the rook on f1, and White's rights are lost. -/
theorem castling_legal :
    isLegal (castlePos false wKOnly) ⟨sq 4 0, sq 6 0, none⟩ = true ∧
    (play (castlePos false wKOnly) ⟨sq 4 0, sq 6 0, none⟩).board (sq 6 0) = some wK ∧
    (play (castlePos false wKOnly) ⟨sq 4 0, sq 6 0, none⟩).board (sq 5 0) = some wR ∧
    (play (castlePos false wKOnly) ⟨sq 4 0, sq 6 0, none⟩).board (sq 7 0) = none ∧
    (play (castlePos false wKOnly) ⟨sq 4 0, sq 6 0, none⟩).castling.whiteKing = false := by
  decide

/-- 3.8.2.2 (3): castling through an attacked square (f1, attacked by Rf8) is illegal. -/
theorem castling_through_check_illegal :
    isLegal (castlePos true wKOnly) ⟨sq 4 0, sq 6 0, none⟩ = false := by decide

/-- 3.8.2.1: without the right (king or rook has moved), castling is illegal. -/
theorem castling_without_right_illegal :
    isLegal (castlePos false noCastle) ⟨sq 4 0, sq 6 0, none⟩ = false := by decide

/-- White Ke1, Ra1; Black rook on `r`, Black Kh8; White may castle queen side. -/
def castleQPos (r : Square) : Position :=
  { board := boardOf [(sq 4 0, wK), (sq 0 0, wR), (r, bR), (sq 7 7, bK)],
    turn := .white, castling := ⟨false, true, false, false⟩, ep := none }

/-- 3.8.2.2 (3) covers only the king's squares: with b1 attacked (Rb8) but empty,
O-O-O is legal. -/
theorem castling_queenside_b1_attacked_legal :
    isLegal (castleQPos (sq 1 7)) ⟨sq 4 0, sq 2 0, none⟩ = true := by decide

/-- 3.8.2.2 (3): the king may not castle out of check (Re7 attacks e1). -/
theorem castling_out_of_check_illegal :
    isLegal (castleQPos (sq 4 6)) ⟨sq 4 0, sq 2 0, none⟩ = false := by decide

/-! ### Pins (3.9.2) -/

/-- White Ke1, Be2; Black Re8, Ka8: the bishop is pinned. -/
def pinPos : Position :=
  { board := boardOf [(sq 4 0, wK), (sq 4 1, wB), (sq 4 7, bR), (sq 0 7, bK)],
    turn := .white, castling := noCastle, ep := none }

theorem pinned_piece_cannot_move : isLegal pinPos ⟨sq 4 1, sq 3 2, none⟩ = false := by decide

/-- The king can never be captured (1.4.1): a move onto the enemy king's square is not
even pseudo-legal. White Ke1, Rh1; Black Kh2 (in check, an illegal position, used only to
exercise the rule). -/
theorem king_never_captured :
    isPseudo { board := boardOf [(sq 4 0, wK), (sq 7 0, wR), (sq 7 1, bK)],
               turn := .white, castling := noCastle, ep := none } ⟨sq 7 0, sq 7 1, none⟩ = false := by
  decide

end EndgameChess.Rules
