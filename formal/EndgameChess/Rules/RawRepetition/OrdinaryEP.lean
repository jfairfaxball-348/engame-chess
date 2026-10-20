import EndgameChess.Rules.RawRepetition.Definitions

/-! S048 / EC-C030: old ep is irrelevant outside the raw EP shape. -/
namespace EndgameChess.Rules.RawRepetition

open EndgameChess.KK

/-- Changing the raw marker preserves pseudo-legality and full play outside EP shape. -/
theorem ordinary_ep_irrelevance (q : Position) (m : Move) (e : Option Square)
    (ordinary : ¬(RawClock.Pawn q m ∧ m.src.1 ≠ m.dst.1 ∧ q.board m.dst = none)) :
    isPseudo {q with ep := e} m = isPseudo q m ∧
      play {q with ep := e} m = play q m := by
  have noCapture (a : Option Square) :
      ((q.board m.src == some ⟨q.turn, .pawn⟩) && a == some m.dst &&
        m.src.1 != m.dst.1 && (q.board m.dst).isNone) = false := by
    apply Bool.eq_false_iff.mpr
    intro yes
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, Option.isNone_iff_eq_none] at yes
    exact ordinary ⟨yes.1.1.1, yes.1.2, yes.2⟩
  constructor
  · cases source : q.board m.src with
    | none => simp [isPseudo, source]
    | some pc =>
      by_cases colour : pc.colour = q.turn
      · cases kind : pc.kind <;>
          try { simp [isPseudo, source, kind, targetOK, canCastle] }
        have pawn : RawClock.Pawn q m := by
          unfold RawClock.Pawn
          rw [source]
          cases pc
          simp_all
        have shape : m.src.1 = m.dst.1 ∨ q.board m.dst ≠ none := by
          by_cases files : m.src.1 = m.dst.1
          · exact Or.inl files
          · exact Or.inr (fun empty => ordinary ⟨pawn, files, empty⟩)
        have moves : pawnMoveOK {q with ep := e} m = pawnMoveOK q m := by
          rcases shape with files | occupied
          · have zero : dx m.src m.dst = 0 := by simp [dx, files]
            simp [pawnMoveOK, pawnCaptureGeom, zero]
          · cases dest : q.board m.dst with
            | none => exact False.elim (occupied dest)
            | some piece => simp [pawnMoveOK, dest]
        simp [isPseudo, source, kind, targetOK, moves]
      · have wrong : (pc.colour == q.turn) = false := by
          exact Bool.eq_false_iff.mpr (fun yes => colour (beq_iff_eq.mp yes))
        simp [isPseudo, source, wrong]
  · simp only [play, noCapture, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

end EndgameChess.Rules.RawRepetition
