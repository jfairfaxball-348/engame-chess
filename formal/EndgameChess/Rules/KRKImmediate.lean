import EndgameChess.Rules.KRKMatingMove

namespace EndgameChess.Rules.KRKImmediate
open EndgameChess.KK KRKMateGeometry KRKMatingMove
set_option maxHeartbeats 200000

/-- The only possible horizontal-check mating destination. -/
def rankTarget (rs wk : Square) : Square := (rs.1, wk.2)
/-- The only possible vertical-check mating destination. -/
def fileTarget (rs wk : Square) : Square := (wk.1, rs.2)

/-- Fully evaluated coordinate/clearance criterion, with no move search. -/
def MateNow (sk rs wk : Square) : Prop :=
  (Horizontal sk (rankTarget rs wk) wk ∧ RookSees rs (rankTarget rs wk) sk wk) ∨
  (Horizontal (sk.2, sk.1) ((fileTarget rs wk).2, (fileTarget rs wk).1) (wk.2, wk.1) ∧
    RookSees rs (fileTarget rs wk) sk wk)

private theorem horizontal_destination {sk rs wk dst : Square}
    (distinct : rs ≠ wk) (notCheck : ¬RookSees rs wk sk wk)
    (move : RookSees rs dst sk wk) (terminal : Horizontal sk dst wk) :
    dst = rankTarget rs wk := by
  obtain ⟨rank, edge, gap, _⟩ := terminal
  have off : rs.2.val ≠ wk.2.val := by
    intro oldRank
    apply notCheck
    simp only [RookSees, RookLine, OnSeg, ne_iff_coords] at distinct ⊢
    omega
  have line := move.1.2
  apply Prod.ext
  · apply Fin.ext
    change dst.1.val = rs.1.val
    omega
  · apply Fin.ext
    exact rank

private theorem target_distinct {sk dst wk : Square} (h : Terminal sk dst wk) :
    dst ≠ sk ∧ dst ≠ wk := by
  rcases h with h | h
  · obtain ⟨rank, edge, gap, _⟩ := h
    simp only [ne_iff_coords, absDiff] at gap ⊢
    omega
  · obtain ⟨file, edge, gap, _⟩ := h
    dsimp only at file edge gap
    simp only [ne_iff_coords, absDiff] at gap ⊢
    omega

/-- The actual kernel's immediate mate existential is eliminated exactly.
King moves and castling are covered by `mating_source`, not excluded by flags. -/
theorem immediate_iff {q : Position} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK q σ sk rs wk) (turn : q.turn = σ)
    (far : 2 ≤ dInf sk wk) (notCheck : ¬RookSees rs wk sk wk) :
    (∃ r, Legal q r ∧ MateGoal σ r) ↔ MateNow sk rs wk := by
  constructor
  · rintro ⟨r, ⟨m, legal, rfl⟩, goal⟩
    have source := mating_source material turn legal notCheck goal.2
    obtain ⟨next, move⟩ := rook_move_model material turn legal source
    have terminal := (kernel_mate_iff next goal.1 far).mp goal.2
    rcases terminal with horizontal | vertical
    · have dest := horizontal_destination material.2.2.1 notCheck move horizontal
      left
      simpa only [dest] using And.intro horizontal move
    · have dest : (m.dst.2, m.dst.1) = rankTarget (rs.2, rs.1) (wk.2, wk.1) :=
        horizontal_destination
          (by change symSwap.f rs ≠ symSwap.f wk; exact symSwap.ne_iff.mpr material.2.2.1)
          (by change ¬RookSees (symSwap.f rs) (symSwap.f wk) (symSwap.f sk) (symSwap.f wk)
              rwa [symSwap.sees_iff])
          ((symSwap.sees_iff _ _ _ _).mpr move) vertical
      have actual : m.dst = fileTarget rs wk := by
        have a := congrArg Prod.fst dest
        have b := congrArg Prod.snd dest
        exact Prod.ext b a
      right
      simpa only [actual] using And.intro vertical move
  · intro now
    have realize : ∀ dst, Terminal sk dst wk → RookSees rs dst sk wk →
        ∃ r, Legal q r ∧ MateGoal σ r := by
      intro dst terminal move
      obtain ⟨notKing, notWeak⟩ := target_distinct terminal
      obtain ⟨r, legal, matchBoard⟩ := step_sound
        (show Matches q σ ⟨sk, rs, wk, true⟩ from ⟨material, turn⟩)
        (StepM.rook move.1 move.2.1 move.2.2 notKing notWeak far)
      exact ⟨r, legal, matchBoard.2,
        (kernel_mate_iff matchBoard.1 matchBoard.2 far).mpr terminal⟩
    rcases now with ⟨horizontal, move⟩ | ⟨vertical, move⟩
    · exact realize _ (Or.inl horizontal) move
    · exact realize _ (Or.inr vertical) move

end EndgameChess.Rules.KRKImmediate
