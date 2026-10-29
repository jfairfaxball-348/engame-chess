import EndgameChess.Rules.KRKFourGeometry

namespace EndgameChess.Rules.KRKCastleFour
open EndgameChess.KK KRKNativeFrame KRKFourGeometry KRKLastReply
set_option maxHeartbeats 1000000

/-- A queenside castling placement can enter the normalized four-ply
region only if the weak king occupies the original rook square. -/
theorem queen_geometry {σ : Colour} {wk : Square}
    (edge : KRKEdgeDepth.depth wk = 0)
    (shape : Shape ((normalize wk).f ((2 : Fin 8), homeRank σ))
      ((normalize wk).f ((3 : Fin 8), homeRank σ)) ((normalize wk).f wk)) :
    wk = ((0 : Fin 8), homeRank σ) := by
  have boundary : wk.2.val = 0 ∨ wk.2.val = 7 ∨ wk.1.val = 0 ∨ wk.1.val = 7 := by
    simp only [KRKEdgeDepth.depth] at edge
    omega
  cases σ <;>
    by_cases bottom : wk.2.val = 0 <;>
    by_cases top : wk.2.val = 7 <;>
    by_cases left : wk.1.val = 0 <;>
    simp [normalize, bottomFrame, bottom, top, left, Frame.ofSym, Frame.comp,
      symId, symX, symY, symSwap, homeRank] at shape <;>
    (try split at shape) <;>
    (try dsimp only at shape) <;>
    simp_all [Shape, KRKFourPlyCorner.CornerFour, KRKFourPlyNearCorner.NearFour,
      LastReply, HorizontalLast, square_eq_iff, homeRank] <;> omega

/-- Kingside castling placements never enter the four-ply regions. -/
theorem king_geometry {σ : Colour} {wk : Square}
    (edge : KRKEdgeDepth.depth wk = 0)
    (shape : Shape ((normalize wk).f ((6 : Fin 8), homeRank σ))
      ((normalize wk).f ((5 : Fin 8), homeRank σ)) ((normalize wk).f wk)) :
    False := by
  have boundary : wk.2.val = 0 ∨ wk.2.val = 7 ∨ wk.1.val = 0 ∨ wk.1.val = 7 := by
    simp only [KRKEdgeDepth.depth] at edge
    omega
  cases σ <;>
    by_cases bottom : wk.2.val = 0 <;>
    by_cases top : wk.2.val = 7 <;>
    by_cases left : wk.1.val = 0 <;>
    simp [normalize, bottomFrame, bottom, top, left, Frame.ofSym, Frame.comp,
      symId, symX, symY, symSwap, homeRank] at shape <;>
    (try split at shape) <;>
    (try dsimp only at shape) <;>
    simp_all [Shape, KRKFourPlyCorner.CornerFour, KRKFourPlyNearCorner.NearFour,
      LastReply, HorizontalLast, square_eq_iff, homeRank] <;> omega

theorem king_square {q : Position} {σ : Colour} {sk rs wk t : Square}
    (hk : IsKRK q σ sk rs wk) (atKing : q.board t = some ⟨σ, .king⟩) : t = sk := by
  rw [hk.2.2.2] at atKing
  rcases krkBoard_some atKing with ⟨e, _⟩ | ⟨_, bad⟩ | ⟨_, bad⟩
  · exact e
  · have badKind := congrArg Piece.kind bad; cases badKind
  · exact False.elim (opp_ne σ (congrArg Piece.colour bad))

theorem rook_square {q : Position} {σ : Colour} {sk rs wk t : Square}
    (hk : IsKRK q σ sk rs wk) (atRook : q.board t = some ⟨σ, .rook⟩) : t = rs := by
  rw [hk.2.2.2] at atRook
  rcases krkBoard_some atRook with ⟨_, bad⟩ | ⟨e, _⟩ | ⟨_, bad⟩
  · have badKind := congrArg Piece.kind bad; cases badKind
  · exact e
  · have badKind := congrArg Piece.kind bad; cases badKind

theorem castle_not_four {q : Position} {σ : Colour} {sk rs wk ns nr : Square}
    {m : Move} (hk : IsKRK q σ sk rs wk) (turn : q.turn = σ)
    (legal : isLegal q m = true) (notMate : ¬MatedK (play q m))
    (src : m.src = sk) (castle : canCastle q m = true)
    (next : IsKRK (play q m) σ ns nr wk) : ¬MateWithin σ 4 (play q m) := by
  have source : q.board m.src = some ⟨σ, .king⟩ := by
    rw [src, hk.2.2.2]; exact krkBoard_sk
  intro win
  have geometry := global_shape_necessary next (by rw [play_turn, turn])
    (KRKEdgeDepth.arrival_far ⟨m, legal, rfl⟩ next) notMate win
  have actual := castle
  simp only [canCastle, turn, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    Option.isNone_iff_eq_none] at actual
  rcases actual with ⟨⟨⟨start, row⟩, promo⟩, king | queen⟩
  · have dest : m.dst = ((6 : Fin 8), homeRank σ) := Prod.ext king.1.1.1.1.1.1.1 row
    have move : m = ⟨((4 : Fin 8), homeRank σ), ((6 : Fin 8), homeRank σ), none⟩ := by
      cases m; simp only [Move.mk.injEq]; exact ⟨start, dest, promo⟩
    rw [start] at source
    have nsEq := king_square next (t := ((6 : Fin 8), homeRank σ))
      (by rw [move]; simp [play, turn, source])
    have nrEq := rook_square next (t := ((5 : Fin 8), homeRank σ))
      (by rw [move]; simp [play, turn, source])
    rw [←nsEq, ←nrEq] at geometry
    exact king_geometry geometry.1 geometry.2
  · have dest : m.dst = ((2 : Fin 8), homeRank σ) := Prod.ext queen.1.1.1.1.1.1.1.1 row
    have move : m = ⟨((4 : Fin 8), homeRank σ), ((2 : Fin 8), homeRank σ), none⟩ := by
      cases m; simp only [Move.mk.injEq]; exact ⟨start, dest, promo⟩
    rw [start] at source
    have nsEq := king_square next (t := ((2 : Fin 8), homeRank σ))
      (by rw [move]; simp [play, turn, source])
    have nrEq := rook_square next (t := ((3 : Fin 8), homeRank σ))
      (by rw [move]; simp [play, turn, source])
    rw [←nsEq, ←nrEq] at geometry
    have weakAt : wk = ((0 : Fin 8), homeRank σ) := queen_geometry geometry.1 geometry.2
    have rookAt : q.board ((0 : Fin 8), homeRank σ) = some ⟨σ, .rook⟩ := queen.1.1.1.1.1.1.2
    have weak : q.board wk = some ⟨σ.opp, .king⟩ := by
      rw [hk.2.2.2]; exact krkBoard_wk hk.2.1 hk.2.2.1
    rw [weakAt, rookAt] at weak
    have impossible := congrArg (fun p : Option Piece => p.map Piece.kind) weak
    cases impossible

/-- Every nonmating strong entry into the four-ply region is an ordinary
king step or rook relocation, including when castling rights are present. -/
theorem four_entry_move {q : Position} {σ : Colour} {sk rs wk ns nr : Square}
    {m : Move} (material : IsKRK q σ sk rs wk) (turn : q.turn = σ)
    (legal : isLegal q m = true) (next : IsKRK (play q m) σ ns nr wk)
    (notMate : ¬MatedK (play q m)) (win : MateWithin σ 4 (play q m)) :
    (m.src = sk ∧ m.promo = none ∧ dInf sk m.dst = 1 ∧
      IsKRK (play q m) σ m.dst rs wk ∧
      Shape ((normalize wk).f m.dst) ((normalize wk).f rs) ((normalize wk).f wk)) ∨
    (m.src = rs ∧ m.promo = none ∧ RookSees rs m.dst sk wk ∧
      IsKRK (play q m) σ sk m.dst wk ∧
      Shape ((normalize wk).f sk) ((normalize wk).f m.dst) ((normalize wk).f wk)) := by
  have geometry := global_shape_necessary next (by rw [play_turn, turn])
    (KRKEdgeDepth.arrival_far ⟨m, legal, rfl⟩ next) notMate win
  have pseudo : isPseudo q m = true := by
    simp only [isLegal, Bool.and_eq_true] at legal; exact legal.1
  obtain ⟨piece, source, colour⟩ := own_of_isPseudo pseudo
  rw [material.2.2.2] at source
  rcases krkBoard_some source with ⟨src, rfl⟩ | ⟨src, rfl⟩ | ⟨_, rfl⟩
  · by_cases castle : canCastle q m = true
    · exact False.elim (castle_not_four material turn legal notMate src castle next win)
    · obtain ⟨moved, distance⟩ := KRKThreePly.king_move_model material turn src legal castle
      have nsEq := king_square next (t := m.dst) (by rw [moved.2.2.2]; exact krkBoard_sk)
      have nrEq := rook_square next (t := rs) (by rw [moved.2.2.2]; exact krkBoard_rs moved.1)
      rw [←nsEq, ←nrEq] at geometry
      have atKing : q.board m.src = some ⟨q.turn, .king⟩ := by
        rw [src, turn, material.2.2.2]; exact krkBoard_sk
      rw [isPseudo_of_king atKing] at pseudo
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at pseudo
      exact Or.inl ⟨src, pseudo.2.1, distance, moved, geometry.2⟩
  · obtain ⟨moved, sees⟩ := KRKMatingMove.rook_move_model material turn legal src
    have nsEq := king_square next (t := sk) (by rw [moved.2.2.2]; exact krkBoard_sk)
    have nrEq := rook_square next (t := m.dst) (by rw [moved.2.2.2]; exact krkBoard_rs moved.1)
    rw [←nsEq, ←nrEq] at geometry
    have atRook : q.board m.src = some ⟨q.turn, .rook⟩ := by
      rw [src, turn, material.2.2.2]; exact krkBoard_rs material.1
    unfold isPseudo at pseudo
    rw [atRook] at pseudo
    simp only [beq_self_eq_true, Bool.true_and, Bool.and_eq_true,
      Option.isNone_iff_eq_none] at pseudo
    exact Or.inr ⟨src, pseudo.2.1, sees, moved, geometry.2⟩
  · exact False.elim (opp_ne σ (colour.trans turn).symm)

end EndgameChess.Rules.KRKCastleFour
