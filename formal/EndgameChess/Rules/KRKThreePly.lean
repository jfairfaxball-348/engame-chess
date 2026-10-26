import EndgameChess.Rules.KRKLastReplyKey

namespace EndgameChess.Rules.KRKThreePly
open EndgameChess.KK KRKMateGeometry KRKImmediate KRKLastReply KRKMatingMove
set_option maxHeartbeats 500000

/-- Coordinate witnesses in the explicit last-reply regions. There is no
recursive game predicate or position-value lookup in these definitions. -/
def KingEntry (sk rs wk : Square) : Prop :=
  ∃ t, dInf sk t = 1 ∧ t ≠ rs ∧ 2 ≤ dInf t wk ∧ LastReply t rs wk

def RookEntry (sk rs wk : Square) : Prop :=
  ∃ t, RookSees rs t sk wk ∧ t ≠ sk ∧ t ≠ wk ∧ LastReply sk t wk

def Three (sk rs wk : Square) : Prop :=
  MateNow sk rs wk ∨ KingEntry sk rs wk ∨ RookEntry sk rs wk

private theorem king_square {q : Position} {σ : Colour} {sk rs wk t : Square}
    (hk : IsKRK q σ sk rs wk) (atKing : q.board t = some ⟨σ, .king⟩) : t = sk := by
  rw [hk.2.2.2] at atKing
  rcases krkBoard_some atKing with ⟨e, _⟩ | ⟨_, bad⟩ | ⟨_, bad⟩
  · exact e
  · have badKind := congrArg Piece.kind bad; cases badKind
  · exact False.elim (opp_ne σ (congrArg Piece.colour bad))

private theorem rook_square {q : Position} {σ : Colour} {sk rs wk t : Square}
    (hk : IsKRK q σ sk rs wk) (atRook : q.board t = some ⟨σ, .rook⟩) : t = rs := by
  rw [hk.2.2.2] at atRook
  rcases krkBoard_some atRook with ⟨_, bad⟩ | ⟨e, _⟩ | ⟨_, bad⟩
  · have badKind := congrArg Piece.kind bad; cases badKind
  · exact e
  · have badKind := congrArg Piece.kind bad; cases badKind

/-- Castling is retained as an actual legal alternative. Its resulting king
and rook placement cannot belong to the last-reply region. -/
theorem castle_not_last {q : Position} {σ : Colour} {sk rs wk ns nr : Square}
    {m : Move} (hk : IsKRK q σ sk rs wk) (turn : q.turn = σ)
    (src : m.src = sk) (castle : canCastle q m = true)
    (next : IsKRK (play q m) σ ns nr wk) : ¬LastReply ns nr wk := by
  have source : q.board m.src = some ⟨σ, .king⟩ := by
    rw [src, hk.2.2.2]; exact krkBoard_sk
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
    intro last
    rw [←nsEq, ←nrEq] at last
    cases σ <;> simp [LastReply, HorizontalLast, homeRank] at last <;> omega
  · have dest : m.dst = ((2 : Fin 8), homeRank σ) := Prod.ext queen.1.1.1.1.1.1.1.1 row
    have move : m = ⟨((4 : Fin 8), homeRank σ), ((2 : Fin 8), homeRank σ), none⟩ := by
      cases m; simp only [Move.mk.injEq]; exact ⟨start, dest, promo⟩
    rw [start] at source
    have nsEq := king_square next (t := ((2 : Fin 8), homeRank σ))
      (by rw [move]; simp [play, turn, source])
    have nrEq := rook_square next (t := ((3 : Fin 8), homeRank σ))
      (by rw [move]; simp [play, turn, source])
    intro last
    rw [←nsEq, ←nrEq] at last
    cases σ <;> simp [LastReply, HorizontalLast, homeRank] at last <;> omega

theorem king_move_model {q : Position} {σ : Colour} {sk rs wk : Square}
    {m : Move} (hk : IsKRK q σ sk rs wk) (turn : q.turn = σ)
    (src : m.src = sk) (legal : isLegal q m = true)
    (castle : canCastle q m ≠ true) :
    IsKRK (play q m) σ m.dst rs wk ∧ dInf sk m.dst = 1 := by
  have pseudo : isPseudo q m = true := by
    simp only [isLegal, Bool.and_eq_true] at legal; exact legal.1
  have atKing : q.board m.src = some ⟨q.turn, .king⟩ := by
    rw [src, turn, hk.2.2.2]; exact krkBoard_sk
  rw [isPseudo_of_king atKing] at pseudo
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, Bool.or_eq_true] at pseudo
  obtain ⟨target, promo, geom⟩ := pseudo
  have distance : dInf sk m.dst = 1 := by
    rw [←src]; exact kingGeom_iff.mp (geom.resolve_right castle)
  have notOld : m.dst ≠ sk := Ne.symm (ne_of_dInf_pos (by omega))
  have notRook : m.dst ≠ rs := by
    intro eq
    exact (targetOK_some target (by rw [eq, hk.2.2.2]; exact krkBoard_rs hk.1)).1 turn.symm
  have notWeak : m.dst ≠ wk := by
    intro eq
    exact (targetOK_some target (by rw [eq, hk.2.2.2]; exact krkBoard_wk hk.2.1 hk.2.2.1)).2 rfl
  have board := play_board_simple atKing (by decide) promo (fun _ => by rwa [src])
  refine ⟨⟨notRook, notWeak, hk.2.2.1, ?_⟩, distance⟩
  rw [board]; funext x; rw [hk.2.2.2, turn, src]; unfold krkBoard
  by_cases e1 : x = m.dst
  · subst x; simp
  · by_cases e2 : x = sk
    · subst x; simp [e1, hk.1, hk.2.1]
    · simp [e1, e2]

/-- An actual legal move reaching the last-reply region is an ordinary king
step or rook relocation, with canonical move data. -/
theorem last_entry_move {q : Position} {σ : Colour} {sk rs wk ns nr : Square}
    {m : Move} (material : IsKRK q σ sk rs wk) (turn : q.turn = σ)
    (legal : isLegal q m = true) (next : IsKRK (play q m) σ ns nr wk)
    (last : LastReply ns nr wk) :
    (m.src = sk ∧ m.promo = none ∧ dInf sk m.dst = 1 ∧
      IsKRK (play q m) σ m.dst rs wk ∧ LastReply m.dst rs wk) ∨
    (m.src = rs ∧ m.promo = none ∧ RookSees rs m.dst sk wk ∧
      IsKRK (play q m) σ sk m.dst wk ∧ LastReply sk m.dst wk) := by
  have pseudo : isPseudo q m = true := by
    simp only [isLegal, Bool.and_eq_true] at legal; exact legal.1
  obtain ⟨piece, source, colour⟩ := own_of_isPseudo pseudo
  rw [material.2.2.2] at source
  rcases krkBoard_some source with ⟨src, rfl⟩ | ⟨src, rfl⟩ | ⟨_, rfl⟩
  · by_cases castle : canCastle q m = true
    · exact False.elim (castle_not_last material turn src castle next last)
    · obtain ⟨moved, distance⟩ := king_move_model material turn src legal castle
      have nsEq := king_square next (t := m.dst) (by rw [moved.2.2.2]; exact krkBoard_sk)
      have nrEq := rook_square next (t := rs) (by rw [moved.2.2.2]; exact krkBoard_rs moved.1)
      rw [←nsEq, ←nrEq] at last
      have atKing : q.board m.src = some ⟨q.turn, .king⟩ := by
        rw [src, turn, material.2.2.2]; exact krkBoard_sk
      rw [isPseudo_of_king atKing] at pseudo
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at pseudo
      exact Or.inl ⟨src, pseudo.2.1, distance, moved, last⟩
  · obtain ⟨moved, sees⟩ := rook_move_model material turn legal src
    have nsEq := king_square next (t := sk) (by rw [moved.2.2.2]; exact krkBoard_sk)
    have nrEq := rook_square next (t := m.dst) (by rw [moved.2.2.2]; exact krkBoard_rs moved.1)
    rw [←nsEq, ←nrEq] at last
    have atRook : q.board m.src = some ⟨q.turn, .rook⟩ := by
      rw [src, turn, material.2.2.2]; exact krkBoard_rs material.1
    unfold isPseudo at pseudo
    rw [atRook] at pseudo
    simp only [beq_self_eq_true, Bool.true_and, Bool.and_eq_true,
      Option.isNone_iff_eq_none] at pseudo
    exact Or.inr ⟨src, pseudo.2.1, sees, moved, last⟩
  · exact False.elim (opp_ne σ (colour.trans turn).symm)

/-- An explicit rook entry has the canonical actual legal move, with flags
preserved by play rather than reconstructed from a geometric board. -/
theorem rook_entry_legal {q : Position} {σ : Colour} {sk rs wk t : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ) (far : 2 ≤ dInf sk wk)
    (sees : RookSees rs t sk wk) (notKing : t ≠ sk) (notWeak : t ≠ wk)
    (last : LastReply sk t wk) : isLegal q ⟨rs, t, none⟩ = true := by
  obtain ⟨r, ⟨m, legal, rfl⟩, next⟩ := step_sound
    (show Matches q σ ⟨sk, rs, wk, true⟩ from ⟨material, turn⟩)
    (StepM.rook sees.1 sees.2.1 sees.2.2 notKing notWeak far)
  rcases last_entry_move material turn legal next.1 last with
    ⟨_, _, distance, moved, _⟩ | ⟨src, promo, _, moved, _⟩
  · have dst := king_square next.1 (t := m.dst)
      (by rw [moved.2.2.2]; exact krkBoard_sk)
    rw [dst, (dInf_eq_zero_iff.mpr rfl)] at distance
    contradiction
  · have dst := rook_square next.1 (t := m.dst)
      (by rw [moved.2.2.2]; exact krkBoard_rs moved.1)
    have canonical : m = ⟨rs, t, none⟩ := by
      cases m; simp only [Move.mk.injEq]; exact ⟨src, dst, promo⟩
    rwa [canonical] at legal

/-- Complete geometric three-ply criterion on legal strong arrivals. Every
ordinary strong move and both castling alternatives are covered. -/
theorem strong_three_iff {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ)
    (far : 2 ≤ dInf sk wk) (notCheck : ¬RookSees rs wk sk wk) :
    MateWithin σ 3 q ↔ Three sk rs wk := by
  constructor
  · intro win
    rcases win with goal | ⟨_, chosen | defended⟩
    · exact False.elim (opp_ne σ (turn.symm.trans goal.1))
    · obtain ⟨_, r, ⟨m, legal, rfl⟩, child⟩ := chosen
      have nextTurn : (play q m).turn = σ.opp := by rw [play_turn, turn]
      obtain ⟨ns, nr, next⟩ := krk_strong_material material turn legal
      have nextFar := KRKEdgeDepth.arrival_far ⟨m, legal, rfl⟩ next
      rcases (weak_two_iff next nextTurn nextFar).mp child with mate | last
      · exact Or.inl ((immediate_iff material turn far notCheck).mp ⟨_, ⟨m, legal, rfl⟩, nextTurn, mate⟩)
      · have pseudo : isPseudo q m = true := by
          simp only [isLegal, Bool.and_eq_true] at legal; exact legal.1
        obtain ⟨piece, source, colour⟩ := own_of_isPseudo pseudo
        rw [material.2.2.2] at source
        rcases krkBoard_some source with ⟨src, rfl⟩ | ⟨src, rfl⟩ | ⟨_, rfl⟩
        · by_cases castle : canCastle q m = true
          · exact False.elim (castle_not_last material turn src castle next last)
          · obtain ⟨moved, distance⟩ := king_move_model material turn src legal castle
            have nsEq := king_square next (t := m.dst) (by rw [moved.2.2.2]; exact krkBoard_sk)
            have nrEq := rook_square next (t := rs) (by rw [moved.2.2.2]; exact krkBoard_rs moved.1)
            rw [←nsEq, ←nrEq] at last
            exact Or.inr (Or.inl ⟨m.dst, distance, moved.1, KRKEdgeDepth.arrival_far ⟨m, legal, rfl⟩ moved, last⟩)
        · obtain ⟨moved, sees⟩ := rook_move_model material turn legal src
          have nsEq := king_square next (t := sk) (by rw [moved.2.2.2]; exact krkBoard_sk)
          have nrEq := rook_square next (t := m.dst) (by rw [moved.2.2.2]; exact krkBoard_rs moved.1)
          rw [←nsEq, ←nrEq] at last
          exact Or.inr (Or.inr ⟨m.dst, sees, Ne.symm moved.1, moved.2.2.1, last⟩)
        · exact False.elim (opp_ne σ (colour.trans turn).symm)
    · exact False.elim (opp_ne σ (turn.symm.trans defended.1))
  · rintro (immediate | king | rook)
    · obtain ⟨r, legal, goal⟩ := (immediate_iff material turn far notCheck).mpr immediate
      exact mateWithin_mono (mateWithin_choose turn legal (show MateWithin σ 0 r from goal)) (by omega)
    · obtain ⟨t, distance, notRook, nextFar, last⟩ := king
      obtain ⟨r, legal, next⟩ := step_sound
        (show Matches q σ ⟨sk, rs, wk, true⟩ from ⟨material, turn⟩)
        (StepM.king distance notRook nextFar)
      exact mateWithin_choose turn legal ((weak_two_iff next.1 next.2 nextFar).mpr (Or.inr last))
    · obtain ⟨t, sees, notKing, notWeak, last⟩ := rook
      obtain ⟨r, legal, next⟩ := step_sound
        (show Matches q σ ⟨sk, rs, wk, true⟩ from ⟨material, turn⟩)
        (StepM.rook sees.1 sees.2.1 sees.2.2 notKing notWeak far)
      exact mateWithin_choose turn legal ((weak_two_iff next.1 next.2 far).mpr (Or.inr last))

end EndgameChess.Rules.KRKThreePly
