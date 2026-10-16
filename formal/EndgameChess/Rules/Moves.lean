import EndgameChess.Rules.Position

/-!
# Rules kernel K1 — the legal-move relation (FIDE 2023 Articles 1.4.1, 3.1–3.10)

Every clause is annotated with the Article it encodes. The FIDE text is quoted verbatim
in `docs/RULES_KERNEL.md`, which is the single trusted FIDE→Lean bridge for theorems
stated over this kernel.

The definitions are `Bool`-valued, so they compute: the same code is both the
specification and a move generator. `Legal` (a `Prop`) is defined from them, and
`mem_legalPositions` shows the generator lists exactly the `Legal` successors.
-/

namespace EndgameChess.Rules

open EndgameChess.KK

/-! ## Geometry -/

/-- `r` lies strictly between `s` and `t` on the straight line through them
(same rank, file or diagonal), using collinearity and additivity of `dInf`. -/
def isBetween (s r t : Square) : Bool :=
  r != s && r != t && (dx s r * dy s t == dy s r * dx s t) &&
    (dInf s r + dInf r t == dInf s t)

/-- Art. 3.5: no intervening piece strictly between `s` and `t`. -/
def pathClear (b : Board) (s t : Square) : Bool :=
  allSquares.all fun r => !isBetween s r t || (b r).isNone

/-- Art. 3.2 and 2.4: along a diagonal. -/
def diagGeom (s t : Square) : Bool := s != t && (dx s t).natAbs == (dy s t).natAbs

/-- Art. 3.3: along the file or the rank. -/
def lineGeom (s t : Square) : Bool := s != t && (dx s t == 0 || dy s t == 0)

/-- Art. 3.6: "one of the squares nearest … but not on the same rank, file or diagonal". -/
def knightGeom (s t : Square) : Bool :=
  ((dx s t).natAbs == 1 && (dy s t).natAbs == 2) || ((dx s t).natAbs == 2 && (dy s t).natAbs == 1)

/-- Art. 3.8.1: an adjoining square (assumption A1: Chebyshev distance one). -/
def kingGeom (s t : Square) : Bool := dInf s t == 1

/-- Art. 3.7.3: "diagonally in front of it on an adjacent file". -/
def pawnCaptureGeom (c : Colour) (s t : Square) : Bool :=
  dy s t == forward c && (dx s t).natAbs == 1

/-! ## Attack and check (Art. 3.1.2, 3.1.3, 3.9.1) -/

/-- Art. 3.1.2–3.1.3: the piece `pc` on `s` attacks `t` iff it could capture on `t`
according to Articles 3.2–3.8. Self-check is ignored (3.1.3), and castling never
captures. -/
def attacksFrom (b : Board) (pc : Piece) (s t : Square) : Bool :=
  match pc.kind with
  | .king => kingGeom s t
  | .queen => (diagGeom s t || lineGeom s t) && pathClear b s t
  | .rook => lineGeom s t && pathClear b s t
  | .bishop => diagGeom s t && pathClear b s t
  | .knight => knightGeom s t
  | .pawn => pawnCaptureGeom pc.colour s t

/-- Square `t` is attacked by some piece of colour `c`. -/
def attacked (b : Board) (t : Square) (c : Colour) : Bool :=
  allSquares.any fun s =>
    match b s with
    | some pc => pc.colour == c && attacksFrom b pc s t
    | none => false

/-- Art. 3.9.1: the king of colour `c` is attacked by an opposing piece. -/
def inCheck (p : Position) (c : Colour) : Bool :=
  allSquares.any fun s => p.board s == some ⟨c, .king⟩ && attacked p.board s c.opp

/-! ## Moves -/

/-- A move: from `src` to `dst`, with an optional promotion choice (Art. 3.7.3.3).
Castling is the king's move two squares along its first rank (Art. 3.8.2). -/
structure Move where
  src : Square
  dst : Square
  promo : Option PromoPiece
  deriving DecidableEq, Repr

/-- Art. 3.1 (no square occupied by an own piece) and 1.4.1 (the king is never captured). -/
def targetOK (p : Position) (t : Square) : Bool :=
  match p.board t with
  | none => true
  | some q => q.colour != p.turn && q.kind != .king

/-- Art. 3.7.1–3.7.3.2: the pawn's moves (promotion is handled separately). -/
def pawnMoveOK (p : Position) (m : Move) : Bool :=
  let c := p.turn
  let f := forward c
  -- 3.7.1: one square forward onto an unoccupied square.
  let single := dx m.src m.dst == 0 && dy m.src m.dst == f && (p.board m.dst).isNone
  -- 3.7.2: on its first move, two squares, both unoccupied. A pawn still on its starting
  -- rank has not moved, since pawns never retreat.
  let double := dx m.src m.dst == 0 && dy m.src m.dst == 2 * f && m.src.2.val == pawnRank c &&
    (p.board m.dst).isNone && pathClear p.board m.src m.dst
  -- 3.7.3: capture of an opponent's piece diagonally in front, on an adjacent file.
  let capture := pawnCaptureGeom c m.src m.dst &&
    (match p.board m.dst with | some q => q.colour == c.opp | none => false)
  -- 3.7.3.1–3.7.3.2: en passant, only immediately after the opponent's two-square advance
  -- (recorded in `p.ep`). The captured pawn stands beside, on the same rank as the capturer.
  let enPassant := pawnCaptureGeom c m.src m.dst && p.ep == some m.dst &&
    (p.board m.dst).isNone && p.board (m.dst.1, m.src.2) == some ⟨c.opp, .pawn⟩
  single || double || capture || enPassant

/-- Art. 3.7.3.3: arriving on the last rank requires a promotion choice; elsewhere none
is allowed. -/
def promoOK (c : Colour) (m : Move) : Bool :=
  if m.dst.2.val == lastRank c then m.promo.isSome else m.promo.isNone

/-- Art. 3.8.2, 3.8.2.1, 3.8.2.2: castling. The king goes from its original square two
squares towards a rook on that rook's original square. The rights must remain (neither
piece has moved). The squares between king and rook must be empty. The king's square,
the square it crosses and the square it lands on must not be attacked. -/
def canCastle (p : Position) (m : Move) : Bool :=
  let c := p.turn
  let h := homeRank c
  let o := c.opp
  m.src == ((4 : Fin 8), h) && m.dst.2 == h && m.promo.isNone &&
  ( -- king side: rook on h-file; f and g empty; e, f, g not attacked
    (m.dst.1 == (6 : Fin 8) &&
      (match c with | .white => p.castling.whiteKing | .black => p.castling.blackKing) &&
      p.board ((7 : Fin 8), h) == some ⟨c, .rook⟩ &&
      (p.board ((5 : Fin 8), h)).isNone && (p.board ((6 : Fin 8), h)).isNone &&
      !attacked p.board ((4 : Fin 8), h) o && !attacked p.board ((5 : Fin 8), h) o &&
      !attacked p.board ((6 : Fin 8), h) o) ||
    -- queen side: rook on a-file; b, c, d empty; e, d, c not attacked
    (m.dst.1 == (2 : Fin 8) &&
      (match c with | .white => p.castling.whiteQueen | .black => p.castling.blackQueen) &&
      p.board ((0 : Fin 8), h) == some ⟨c, .rook⟩ &&
      (p.board ((1 : Fin 8), h)).isNone && (p.board ((2 : Fin 8), h)).isNone &&
      (p.board ((3 : Fin 8), h)).isNone &&
      !attacked p.board ((4 : Fin 8), h) o && !attacked p.board ((3 : Fin 8), h) o &&
      !attacked p.board ((2 : Fin 8), h) o) )

/-- A move satisfying Articles 3.1–3.8 and 1.4.1 for the side having the move, before
the self-check condition of 3.9.2. -/
def isPseudo (p : Position) (m : Move) : Bool :=
  match p.board m.src with
  | none => false
  | some pc =>
    pc.colour == p.turn && targetOK p m.dst &&
    match pc.kind with
    | .king => m.promo.isNone && (kingGeom m.src m.dst || canCastle p m)
    | .pawn => pawnMoveOK p m && promoOK pc.colour m
    | _ => m.promo.isNone && attacksFrom p.board pc m.src m.dst

/-- The rook squares whose occupation or vacating removes a castling right
(Art. 3.8.2.1: a rook that has moved; a rook captured on its square cannot castle). -/
def updateCastling (cr : CastlingRights) (c : Colour) (kingMoved : Bool) (s t : Square) :
    CastlingRights :=
  let touched (q : Square) := s == q || t == q
  { whiteKing := cr.whiteKing && !(kingMoved && c == .white) && !touched ((7 : Fin 8), (0 : Fin 8))
    whiteQueen := cr.whiteQueen && !(kingMoved && c == .white) && !touched ((0 : Fin 8), (0 : Fin 8))
    blackKing := cr.blackKing && !(kingMoved && c == .black) && !touched ((7 : Fin 8), (7 : Fin 8))
    blackQueen := cr.blackQueen && !(kingMoved && c == .black) && !touched ((0 : Fin 8), (7 : Fin 8)) }

/-- The position after playing `m` (meaningful when `m` is pseudo-legal):
- the capture removes the opponent's piece (3.1.1), including en passant (3.7.3.1);
- promotion replaces the pawn on arrival (3.7.3.3);
- castling also moves the rook to the square the king crossed (3.8.2);
- the turn passes (1.2);
- castling rights and the en-passant target are updated. -/
def play (p : Position) (m : Move) : Position :=
  let c := p.turn
  let h := homeRank c
  let pc := p.board m.src
  let isPawn := pc == some ⟨c, .pawn⟩
  let isKing := pc == some ⟨c, .king⟩
  let epCapture := isPawn && p.ep == some m.dst && m.src.1 != m.dst.1 && (p.board m.dst).isNone
  let castleK := isKing && m.src == ((4 : Fin 8), h) && m.dst == ((6 : Fin 8), h)
  let castleQ := isKing && m.src == ((4 : Fin 8), h) && m.dst == ((2 : Fin 8), h)
  let arriving : Option Piece :=
    match m.promo with
    | some k => if isPawn then some ⟨c, k.toKind⟩ else pc
    | none => pc
  { board := fun s =>
      if s == m.dst then arriving
      else if s == m.src then none
      else if epCapture && s == (m.dst.1, m.src.2) then none
      else if castleK && s == ((7 : Fin 8), h) then none
      else if castleK && s == ((5 : Fin 8), h) then some ⟨c, .rook⟩
      else if castleQ && s == ((0 : Fin 8), h) then none
      else if castleQ && s == ((3 : Fin 8), h) then some ⟨c, .rook⟩
      else p.board s
    turn := c.opp
    castling := updateCastling p.castling c isKing m.src m.dst
    ep := if isPawn && (dy m.src m.dst).natAbs == 2 then
            some (m.src.1, ⟨(m.src.2.val + m.dst.2.val) / 2, by omega⟩)
          else none }

/-- Art. 3.9.2 and 3.10.1: a legal move satisfies 3.1–3.8, and the mover's king is not
in check afterwards. -/
def isLegal (p : Position) (m : Move) : Bool :=
  isPseudo p m && !inCheck (play p m) p.turn

/-- The legal-move relation on positions (Art. 3.10.1). -/
def Legal (p q : Position) : Prop :=
  ∃ m, isLegal p m = true ∧ q = play p m

/-! ## Generator -/

def allPromos : List (Option PromoPiece) :=
  [none, some .queen, some .rook, some .bishop, some .knight]

theorem mem_allPromos (o : Option PromoPiece) : o ∈ allPromos := by
  cases o with
  | none => simp [allPromos]
  | some k => cases k <;> simp [allPromos]

/-- Candidate moves: every own-piece square × every square × every promotion option. -/
def candidates (p : Position) : List Move :=
  (allSquares.filter fun s => match p.board s with
      | some pc => pc.colour == p.turn
      | none => false).flatMap fun s =>
    allSquares.flatMap fun t => allPromos.map fun o => ⟨s, t, o⟩

def legalMoves (p : Position) : List Move := (candidates p).filter (isLegal p)

def legalPositions (p : Position) : List Position := (legalMoves p).map (play p)

theorem own_of_isPseudo {p : Position} {m : Move} (h : isPseudo p m = true) :
    ∃ pc, p.board m.src = some pc ∧ pc.colour = p.turn := by
  unfold isPseudo at h
  split at h
  · contradiction
  · rename_i pc hpc
    refine ⟨pc, hpc, ?_⟩
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact h.1.1

/-- The generator is complete and sound for `isLegal`. -/
theorem mem_legalMoves {p : Position} {m : Move} : m ∈ legalMoves p ↔ isLegal p m = true := by
  constructor
  · intro h; exact (List.mem_filter.1 h).2
  · intro h
    refine List.mem_filter.2 ⟨?_, h⟩
    have hp : isPseudo p m = true := by
      unfold isLegal at h; simp only [Bool.and_eq_true] at h; exact h.1
    obtain ⟨pc, hpc, hcol⟩ := own_of_isPseudo hp
    simp only [candidates, List.mem_flatMap, List.mem_filter, List.mem_map]
    refine ⟨m.src, ⟨mem_allSquares _, ?_⟩, m.dst, mem_allSquares _, m.promo, mem_allPromos _, rfl⟩
    rw [hpc]; simp [hcol]

/-- The generator lists exactly the `Legal` successors. -/
theorem mem_legalPositions {p q : Position} : q ∈ legalPositions p ↔ Legal p q := by
  simp only [legalPositions, List.mem_map, Legal, mem_legalMoves]
  constructor
  · rintro ⟨m, hm, rfl⟩; exact ⟨m, hm, rfl⟩
  · rintro ⟨m, hm, rfl⟩; exact ⟨m, hm, rfl⟩

/-! ## Basic sanity theorems -/

/-- Art. 3.9.2: after a legal move the mover's king is not in check. -/
theorem not_inCheck_after_legal {p : Position} {m : Move} (h : isLegal p m = true) :
    inCheck (play p m) p.turn = false := by
  unfold isLegal at h; simp only [Bool.and_eq_true, Bool.not_eq_true'] at h; exact h.2

/-- Art. 1.2: every move passes the turn. -/
theorem play_turn (p : Position) (m : Move) : (play p m).turn = p.turn.opp := rfl

/-- `Legal` is not vacuous; every legal successor is legal for the mover (3.9.2). -/
theorem legal_mover_safe {p q : Position} (h : Legal p q) : inCheck q p.turn = false := by
  obtain ⟨m, hm, rfl⟩ := h
  exact not_inCheck_after_legal hm

/-- Perft: the number of legal move sequences of length `n` (evaluation helper only). -/
def perft : Position → Nat → Nat
  | _, 0 => 1
  | p, n + 1 => ((legalMoves p).map fun m => perft (play p m) n).foldl (· + ·) 0

end EndgameChess.Rules
