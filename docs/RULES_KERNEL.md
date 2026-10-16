# Rules kernel — FIDE 2023 → Lean bridge (EC-C004, K1)

**This table is the single trusted FIDE→Lean bridge for every theorem stated over the rules kernel** (`formal/EndgameChess/Rules/`). Lean checks the proofs about these definitions. Nothing machine-checks that the definitions say what the Laws say; this table is where a person checks that.

- **Source:** FIDE Laws of Chess taking effect from 1 January 2023, https://handbook.fide.com/chapter/E012023. Retrieved 2026-10-16. HTML SHA-256: `c5b1692a0614d4bd93fe9238287b9ab7d1f47320934d5df3be113523906c476f`. The rule text below is copied verbatim from that retrieval.
- **Lean modules:** `Rules/Board.lean`, `Rules/Position.lean`, `Rules/Moves.lean`, `Rules/Sanity.lean` (namespace `EndgameChess.Rules`). They reuse `EndgameChess.KK.Square` (`Fin 8 × Fin 8`, (file, rank), a1 = (0,0)) and `EndgameChess.KK.Colour`.
- **Numbering note:** on the retrieved page the promotion clauses are numbered **3.7.3.3–3.7.3.5**, but the same page's glossary cites promotion as 3.7.5.x. This table uses the page's own article numbering.

## Independent review

| Reviewer | Date | Scope reviewed | Verdict / notes |
|---|---|---|---|
| *(open: needs an independent human reviewer)* | | | |

## Clause table

| Article | FIDE text (verbatim) | Lean encoding | Interpretation / notes |
|---|---|---|---|
| 1.2 | "The player with the light-coloured pieces (White) makes the first move, then the players move alternately, with the player with the dark-coloured pieces (Black) making the next move." | `Position.turn`; `initial.turn = .white`; `play` sets `turn := c.opp` (`play_turn`) | |
| 1.4.1 | "… Leaving one's own king under attack, exposing one's own king to attack and also 'capturing' the opponent's king is not allowed." | `targetOK` (`q.kind != .king`); the self-check filter in `isLegal` | Sanity: `king_never_captured`. |
| 2.1 | "The chessboard is composed of an 8 x 8 grid of 64 equal squares alternately light (the 'white' squares) and dark (the 'black' squares). The chessboard is placed between the players in such a way that the near corner square to the right of the player is white." | `Square := Fin 8 × Fin 8`; `allSquares` (`mem_allSquares`); `isLightSquare` (h1 = (7,0) is light) | The orientation fixes a1 as dark. |
| 2.2–2.3 | Pieces: king, queen, two rooks, two bishops, two knights and eight pawns per side; "2.3 The initial position of the pieces on the chessboard is as follows:" (diagram) | `PieceType`, `Piece`, `backRank`, `initialBoard`, `initial` | 2.3 is a diagram. Encoded as the standard set-up: RNBQKBNR on ranks 1/8, pawns on 2/7, Q on d-file, K on e-file. Sanity: `initial_wellFormed`. |
| 2.4 | "The eight vertical columns of squares are called 'files'. The eight horizontal rows of squares are called 'ranks'. A straight line of squares of the same colour, running from one edge of the board to an adjacent edge, is called a 'diagonal'." | file = `.1`, rank = `.2`; `diagGeom` (\|Δfile\| = \|Δrank\| ≠ 0) | |
| 3.1 | "It is not permitted to move a piece to a square occupied by a piece of the same colour." | `targetOK` (`q.colour != p.turn`) | |
| 3.1.1 | "If a piece moves to a square occupied by an opponent's piece the latter is captured and removed from the chessboard as part of the same move." | `play`: `dst` is overwritten by the arriving piece | |
| 3.1.2 | "A piece is said to attack an opponent's piece if the piece could make a capture on that square according to Articles 3.2 to 3.8." | `attacksFrom`, `attacked` | Attack is defined for squares, whatever occupies them; this is the reading needed for 3.8.2.2(3) and 3.9.1. Pawns attack only diagonally forward (their capture geometry). Castling never captures, so it attacks nothing. |
| 3.1.3 | "A piece is considered to attack a square even if this piece is constrained from moving to that square because it would then leave or place the king of its own colour under attack." | `attacksFrom` has no self-check filter | |
| 3.2 | "The bishop may move to any square along a diagonal on which it stands." | `diagGeom` + `pathClear` | |
| 3.3 | "The rook may move to any square along the file or the rank on which it stands." | `lineGeom` + `pathClear` | |
| 3.4 | "The queen may move to any square along the file, the rank or a diagonal on which it stands." | `diagGeom ∨ lineGeom`, + `pathClear` | |
| 3.5 | "When making these moves, the bishop, rook or queen may not move over any intervening pieces." | `pathClear` via `isBetween` (collinear, and `dInf` additive) | Perft agreement with an independent ray-walking generator (see below). |
| 3.6 | "The knight may move to one of the squares nearest to that on which it stands but not on the same rank, file or diagonal." | `knightGeom` (\|Δ\| = (1,2) or (2,1)) | The nearest squares off rank, file and diagonal are exactly the (1,2)/(2,1) offsets. |
| 3.7.1 | "The pawn may move forward to the square immediately in front of it on the same file, provided that this square is unoccupied, or" | `pawnMoveOK.single` (`forward`) | White moves up, Black down. |
| 3.7.2 | "on its first move the pawn may move as in 3.7.1 or alternatively it may advance two squares along the same file, provided that both squares are unoccupied, or" | `pawnMoveOK.double` (`pawnRank`, `pathClear`) | "First move" is read as "still on its starting rank". This is equivalent in play from Art. 2.3, because pawns never retreat and promotion removes them. |
| 3.7.3 | "the pawn may move to a square occupied by an opponent's piece diagonally in front of it on an adjacent file, capturing that piece." | `pawnMoveOK.capture` (`pawnCaptureGeom`) | |
| 3.7.3.1 | "A pawn occupying a square on the same rank as and on an adjacent file to an opponent's pawn which has just advanced two squares in one move from its original square may capture this opponent's pawn as though the latter had been moved only one square." | `pawnMoveOK.enPassant`; `play` removes `(dst.file, src.rank)`; `Position.ep` set by `play` after a two-square advance | Sanity: `enPassant_legal`, `enPassant_exposing_king_illegal`. |
| 3.7.3.2 | "This capture is only legal on the move following this advance and is called an 'en passant' capture." | `play` resets `ep := none` after every other move | Sanity: `enPassant_expired`. |
| 3.7.3.3 | "When a player, having the move, plays a pawn to the rank furthest from its starting position, he/she must exchange that pawn as part of the same move for a new queen, rook, bishop or knight of the same colour on the intended square of arrival. …" | `promoOK` (`lastRank`); `Move.promo : Option PromoPiece`; `play` places `⟨c, k.toKind⟩` | Sanity: `promotion_rules` (Q and N legal; no choice is illegal). |
| 3.7.3.4 | "The player's choice is not restricted to pieces that have been captured previously." | No material bound on promotion | |
| 3.7.3.5 | "… the effect of the new piece is immediate." | The self-check test in `isLegal` is evaluated on the position *after* promotion | |
| 3.8.1 | "by moving to an adjoining square" | `kingGeom` (`dInf = 1`) | Assumption A1, the same as EC-T0001. |
| 3.8.2 | "by 'castling'. This is a move of the king and either rook of the same colour along the player's first rank, counting as a single move of the king and executed as follows: the king is transferred from its original square two squares towards the rook on its original square, then that rook is transferred to the square the king has just crossed." | `canCastle` (king e1/e8 → g or c file; rook on h or a); `play` moves the rook to f or d | Castling is encoded as the king's two-square move. |
| 3.8.2.1 | "The right to castle has been lost: 1) If the king has already moved, or 2) With a rook that has already moved." | `CastlingRights`; `updateCastling` clears both rights on a king move, and one right when its rook's corner is vacated or entered | Entering the corner covers a rook captured on its square: no other rook can later castle from there. Sanity: `castling_without_right_illegal`. |
| 3.8.2.2 (3) | "If the square on which the king stands, or the square which it must cross, or the square which it is to occupy, is attacked by one or more of the opponent's pieces, or" | `canCastle`: `!attacked` on e, f, g (king side) or e, d, c (queen side) | b1/b8 need not be safe, only empty. Sanity: `castling_through_check_illegal`, `castling_out_of_check_illegal`, `castling_queenside_b1_attacked_legal`. |
| 3.8.2.2 (4) | "If there is any piece between the king and the rook with which castling is to be effected." | `canCastle`: f, g empty, or b, c, d empty | |
| 3.9.1 | "The king is said to be 'in check' if it is attacked by one or more of the opponent's pieces, even if such pieces are constrained from moving to the square occupied by the king because they would then leave or place their own king in check." | `inCheck` (via `attacked`, no self-check filter) | |
| 3.9.2 | "No piece can be moved that will either expose the king of the same colour to check or leave that king in check." | `isLegal := isPseudo ∧ ¬ inCheck (play p m) p.turn` | Sanity: `pinned_piece_cannot_move`, `not_inCheck_after_legal`. |
| 3.10.1 | "A move is legal when all the relevant requirements of Articles 3.1 – 3.9 have been fulfilled." | `isLegal`, `Legal`; generator `legalMoves` / `legalPositions` (`mem_legalMoves`, `mem_legalPositions`) | |
| 3.10.3 | "A position is illegal when it cannot have been reached by any series of legal moves." | *(S009: `Arisen` as reachability)* | Not yet encoded. |

## Evidence that the encoding behaves as the Laws do
- **Kernel-checked** (`Rules/Sanity.lean`, `decide`): `initial_legal_count` (20 legal first moves), en passant (legal, expired, exposing the king), promotion (Q/N legal, no-choice illegal, the new piece placed), castling (legal, through check, out of check, without the right, queen side with b1 attacked), pin, no king capture.
- **Perft agreement** between two independent implementations: the Lean generator, evaluated in `Checks/Perft.lean` (evaluation, not proof), and `scripts/perft.py` (a different representation, written separately). Both agree with each other and with the published values (Chess Programming Wiki, "Perft Results") on the initial position and four standard test positions that exercise castling, en passant, en-passant pins, promotion and checks. See `audits/EC-C004_K1.md` for the numbers.

## Known modelling choices (to be reviewed)
1. The 2.3 diagram is encoded as the standard set-up.
2. 3.7.2 "first move" is read as "on its starting rank".
3. A position carries castling rights and an en-passant target, the history that Article 3 needs. Clocks and repetition are omitted, because they do not affect legality.
4. A position with no king of the side to move is representable. `inCheck` is then false. Such positions never arise from `initial` (S009 will prove this).
