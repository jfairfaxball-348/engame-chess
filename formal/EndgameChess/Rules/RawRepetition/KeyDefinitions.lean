import EndgameChess.Rules.RawRepetition.NormalizationDefinitions

/-! S052 / EC-C032: full normalized record as raw repetition-key candidate. -/
namespace EndgameChess.Rules.RawRepetition

/-- Full normalized board/turn/rights/effective-target record, without a FIDE iff claim. -/
noncomputable def key (q : Position) : Position := normalizeEP q

end EndgameChess.Rules.RawRepetition
