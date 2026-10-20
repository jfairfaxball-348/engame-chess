import EndgameChess.Rules.RawRepetition.NormalizationDefinitions
import EndgameChess.Rules.RawRepetition.OrdinaryEP
import EndgameChess.Rules.RawRepetition.EPCharacterization

/-! S050 / EC-C031: legal moves and their full played endpoints survive normalization. -/
namespace EndgameChess.Rules.RawRepetition

/-- Effective-ep normalization preserves legality and every legal played position. -/
theorem normalizeEP_preserves (q : Position) (m : Move) :
    isLegal (normalizeEP q) m = isLegal q m ∧
      (isLegal q m = true → play (normalizeEP q) m = play q m) := by
  classical
  by_cases available : ∃ move, LegalEP q move
  · have same : normalizeEP q = q := by
      simp [normalizeEP, effectiveEP, available]
    simp [same]
  · by_cases shape : RawClock.Pawn q m ∧ m.src.1 ≠ m.dst.1 ∧ q.board m.dst = none
    · have illegal : isLegal q m = false := by
        apply Bool.eq_false_iff.mpr
        intro legal
        exact available ⟨m, (legalEP_iff_shape q m).mpr ⟨legal, shape⟩⟩
      have source := shape.1
      change q.board m.src = some ⟨q.turn, .pawn⟩ at source
      have nonzero : dx m.src m.dst ≠ 0 := by
        intro zero
        apply shape.2.1
        apply Fin.ext
        simp only [dx] at zero
        omega
      have normalizedIllegal : isLegal (normalizeEP q) m = false := by
        simp [isLegal, normalizeEP, effectiveEP, available, isPseudo, source,
          pawnMoveOK, nonzero, shape.2.2]
      simp [illegal, normalizedIllegal]
    · obtain ⟨pseudo, played⟩ := ordinary_ep_irrelevance q m (effectiveEP q) shape
      change isPseudo (normalizeEP q) m = isPseudo q m at pseudo
      change play (normalizeEP q) m = play q m at played
      constructor
      · change (isPseudo (normalizeEP q) m && !inCheck (play (normalizeEP q) m) q.turn) = _
        rw [pseudo, played]
        rfl
      · intro _
        exact played

end EndgameChess.Rules.RawRepetition
