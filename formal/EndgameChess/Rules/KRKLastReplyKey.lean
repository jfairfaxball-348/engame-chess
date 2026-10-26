import EndgameChess.Rules.KRKLastReplyHistory
import EndgameChess.Rules.RawClaims.ExclusionCharacterization

namespace EndgameChess.Rules.KRKLastReply
open EndgameChess.KK RawHistoryLayer

private theorem weak_move_shape {q : Position} {σ : Colour} {sk rs wk : Square}
    {m : Move} (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp)
    (legal : isLegal q m = true) :
    m.src = wk ∧ m.promo = none ∧ (play q m).board m.dst = some ⟨σ.opp, .king⟩ := by
  have pseudo : isPseudo q m = true := by
    simp only [isLegal, Bool.and_eq_true] at legal
    exact legal.1
  obtain ⟨piece, source, colour⟩ := own_of_isPseudo pseudo
  rw [material.2.2.2] at source
  rcases krkBoard_some source with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨src, rfl⟩
  · exact False.elim (opp_ne σ (colour.trans turn))
  · exact False.elim (opp_ne σ (colour.trans turn))
  · have atKing : q.board m.src = some ⟨q.turn, .king⟩ := by
      rw [turn, src, material.2.2.2]
      exact krkBoard_wk material.2.1 material.2.2.1
    rw [isPseudo_of_king atKing] at pseudo
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at pseudo
    have promo := pseudo.2.1
    refine ⟨src, promo, ?_⟩
    simp [play, atKing, turn, promo]

/-- Canonical data for every actual weak move that retains exact KRK. -/
theorem weak_move_eq {q : Position} {σ : Colour} {sk rs wk u : Square} {m : Move}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp)
    (legal : isLegal q m = true) (next : IsKRK (play q m) σ sk rs u) :
    m = ⟨wk, u, none⟩ := by
  obtain ⟨src, promo, atKing⟩ := weak_move_shape material turn legal
  rw [next.2.2.2] at atKing
  have dst : m.dst = u := by
    rcases krkBoard_some atKing with ⟨_, bad⟩ | ⟨_, bad⟩ | ⟨eq, _⟩
    · exact False.elim (opp_ne σ (congrArg Piece.colour bad).symm)
    · have badKind := congrArg Piece.kind bad; cases badKind
    · exact eq
  cases m
  simp only [Move.mk.injEq]
  exact ⟨src, dst, promo⟩

/-- Expose the actual canonical move in model soundness for a weak step. -/
theorem lone_step_legal {q : Position} {σ : Colour} {sk rs wk u : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp)
    (step : StepM ⟨sk, rs, wk, false⟩ ⟨sk, rs, u, true⟩) :
    isLegal q ⟨wk, u, none⟩ = true := by
  obtain ⟨r, ⟨m, legal, rfl⟩, next⟩ := step_sound
    (show Matches q σ ⟨sk, rs, wk, false⟩ from ⟨material, turn⟩) step
  have canonical := weak_move_eq material turn legal next.1
  rwa [canonical] at legal

/-- The coordinate last-reply region determines one actual move, including
its source and promotion data, for every legal defender alternative. -/
theorem unique_legal_reply {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp)
    (far : 2 ≤ dInf sk wk) (geometry : LastReply sk rs wk) :
    ∃ t, isLegal q ⟨wk, t, none⟩ = true ∧
      ∀ m, isLegal q m = true → m = ⟨wk, t, none⟩ := by
  obtain ⟨safe, ⟨t, step⟩, every⟩ := (model_last_iff far).mpr geometry
  obtain ⟨r, ⟨m, legal, rfl⟩, next⟩ := step_sound
    (show Matches q σ ⟨sk, rs, wk, false⟩ from ⟨material, turn⟩) step
  have dstOf : ∀ n, isLegal q n = true → n.dst = t := by
    intro n hn
    obtain ⟨u, nextU, stepU⟩ := krk_safe_reply material turn safe ⟨n, hn, rfl⟩
    have same := ready_neighbour_unique far
      (by cases step with | lone h _ _ _ => exact h)
      (by cases stepU with | lone h _ _ _ => exact h)
      (every t step) (every u stepU)
    have atKing := (weak_move_shape material turn hn).2.2
    rw [nextU.1.2.2.2] at atKing
    have dst : n.dst = u := by
      rcases krkBoard_some atKing with ⟨_, bad⟩ | ⟨_, bad⟩ | ⟨eq, _⟩
      · exact False.elim (opp_ne σ (congrArg Piece.colour bad).symm)
      · have badKind := congrArg Piece.kind bad; cases badKind
      · exact eq
    exact dst.trans same.symm
  have shape : ∀ n, isLegal q n = true → n = ⟨wk, t, none⟩ := by
    intro n hn
    obtain ⟨src, promo, _⟩ := weak_move_shape material turn hn
    have dst := dstOf n hn
    cases n
    simp only [Move.mk.injEq]
    exact ⟨src, dst, promo⟩
  exact ⟨t, by simpa only [shape m legal] using legal, shape⟩

theorem weak_safe_quiet {q : Position} {σ : Colour} {sk rs wk : Square}
    {m : Move} (material : IsKRK q σ sk rs wk) (turn : q.turn = σ.opp)
    (safe : SafeRook sk rs wk) (legal : isLegal q m = true) :
    RawClock.zeroing q m = false := by
  have pseudo : isPseudo q m = true := by
    simp only [isLegal, Bool.and_eq_true] at legal
    exact legal.1
  obtain ⟨noPawn, targets⟩ := krk_material_targets material pseudo
  obtain ⟨u, next, _⟩ := krk_safe_reply material turn safe ⟨m, legal, rfl⟩
  have empty : q.board m.dst = none := by
    cases atDst : q.board m.dst with
    | none => rfl
    | some piece =>
      have dst := (targets piece atDst).1
      have arrived := (weak_move_shape material turn legal).2.2
      have retained : (play q m).board m.dst = some ⟨σ, .rook⟩ := by
        rw [dst, next.1.2.2.2]
        exact krkBoard_rs next.1.1
      rw [arrived] at retained
      have bad := congrArg (fun o => o.map Piece.kind) retained
      cases bad
  have pawnFalse : (q.board m.src == some ⟨q.turn, .pawn⟩) = false := by
    rw [Bool.eq_false_iff]
    simpa using noPawn
  simp [RawClock.zeroing, pawnFalse, empty]

/-- Evaluate the current/intended claim test using just the current key and
the unique forced child key, both counted in the original incoming trace. -/
theorem no_claim_at_unique_reply {s : RawTrace.State} {σ : Colour}
    {sk rs wk t : Square} (material : IsKRK (RawTrace.erase s) σ sk rs wk)
    (turn : (RawTrace.erase s).turn = σ.opp) (far : 2 ≤ dInf sk wk)
    (geometry : LastReply sk rs wk)
    (legal : isLegal (RawTrace.erase s) ⟨wk, t, none⟩ = true) :
    ¬RawClaims.AvailableThreshold s ↔
      RawClock.clock s.trace < 99 ∧ RawRepetition.currentOccurrences s < 3 ∧
      RawRepetition.occurrences s.trace (play (RawTrace.erase s) ⟨wk, t, none⟩) < 2 := by
  obtain ⟨u, _, unique⟩ := unique_legal_reply material turn far geometry
  have uniqueT : ∀ m, isLegal (RawTrace.erase s) m = true → m = ⟨wk, t, none⟩ := by
    intro m hm
    exact (unique m hm).trans (unique _ legal).symm
  have quiet := weak_safe_quiet material turn geometry.1 legal
  constructor
  · intro absent
    obtain ⟨_, count, every⟩ := (RawClaims.no_threshold_iff s).mp absent
    obtain ⟨clock, childCount⟩ := every _ legal
    rw [RawClock.append_clock, quiet] at clock
    simp only [Bool.false_eq_true, ↓reduceIte] at clock
    exact ⟨by omega, count, childCount⟩
  · rintro ⟨clock, count, childCount⟩
    apply (RawClaims.no_threshold_iff s).mpr
    refine ⟨by omega, count, ?_⟩
    intro m hm
    have same := uniqueT m hm
    subst m
    constructor
    · rw [RawClock.append_clock, quiet]
      simp only [Bool.false_eq_true, ↓reduceIte]
      omega
    · exact childCount

/-- In the evaluated geometry, the complete high-clock RAW outcome is three
integer inequalities on the original history and its one forced child key. -/
theorem high_clock_actual_key_iff {s : State} {σ : Colour} {sk rs wk t : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s)
    (turn : (erase s).turn = σ.opp) (far : 2 ≤ dInf sk wk)
    (high : 97 ≤ RawClock.clock s.val.trace) (geometry : LastReply sk rs wk)
    (legal : isLegal (erase s) ⟨wk, t, none⟩ = true) :
    KRKWinning.ActualWin σ s ↔
      RawClock.clock s.val.trace < 99 ∧ RawRepetition.currentOccurrences s.val < 3 ∧
      RawRepetition.occurrences s.val.trace (play (erase s) ⟨wk, t, none⟩) < 2 := by
  rw [high_clock_actual_iff material ongoing turn high]
  simp only [geometry, true_and]
  exact no_claim_at_unique_reply material turn far geometry legal

end EndgameChess.Rules.KRKLastReply
