import EndgameChess.Rules.RawRepetition.KeyDefinitions
import EndgameChess.Rules.RawRepetition.Normalization

/-! S052 / EC-C032: full normalized-key equality preserves actual legal play. -/
namespace EndgameChess.Rules.RawRepetition

/-- Equal normalized keys have equal legality and full endpoints of legal moves. -/
theorem key_legal_congr (q r : Position) (same : key q = key r) (m : Move) :
    isLegal q m = isLegal r m ∧
      (isLegal q m = true → play q m = play r m) := by
  have normalized : normalizeEP q = normalizeEP r := same
  obtain ⟨qLegal, qPlay⟩ := normalizeEP_preserves q m
  obtain ⟨rLegal, rPlay⟩ := normalizeEP_preserves r m
  have legal : isLegal q m = isLegal r m :=
    qLegal.symm.trans ((congrArg (fun p => isLegal p m) normalized).trans rLegal)
  refine ⟨legal, ?_⟩
  intro actual
  have atR : isLegal r m = true := legal.symm.trans actual
  exact (qPlay actual).symm.trans
    ((congrArg (fun p => play p m) normalized).trans (rPlay atR))

end EndgameChess.Rules.RawRepetition
