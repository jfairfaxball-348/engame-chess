import EndgameChess.Rules.KRKThreePlyHistory
import EndgameChess.Rules.KRKBound.Transport

namespace EndgameChess.Rules.KRKGeometricSymmetry
open EndgameChess.KK KRKMateGeometry KRKImmediate KRKLastReply
set_option maxHeartbeats 500000

theorem last_valid {sk rs wk : Square} (last : LastReply sk rs wk) :
    sk ≠ rs ∧ sk ≠ wk ∧ rs ≠ wk ∧ 2 ≤ dInf sk wk := by
  rcases last.2 with horizontal | vertical <;>
    simp only [HorizontalLast] at * <;>
    simp only [ne_iff_coords, dInf, absDiff] <;> omega

private theorem horizontal_source_valid {sk rs wk : Square}
    (horizontal : Horizontal sk (rankTarget rs wk) wk) (sees : RookSees rs (rankTarget rs wk) sk wk) :
    sk ≠ rs ∧ sk ≠ wk ∧ rs ≠ wk ∧ 2 ≤ dInf sk wk ∧ ¬RookSees rs wk sk wk := by
  have line := sees.1
  clear sees
  simp only [Horizontal, rankTarget, absDiff] at horizontal
  simp only [RookLine, rankTarget] at line
  have offFile : rs.1.val ≠ wk.1.val := by omega
  have offRank : rs.2.val ≠ wk.2.val := by
    intro equal
    exact line.1 ⟨True.intro, equal⟩
  have far : 2 ≤ dInf sk wk := by simp only [dInf, absDiff]; omega
  refine ⟨?_, ne_of_dInf_pos (by omega), ?_, far, ?_⟩
  · rw [ne_iff_coords]; omega
  · rw [ne_iff_coords]; omega
  · intro seen
    exact seen.1.2.elim offFile offRank

theorem immediate_valid {sk rs wk : Square} (now : MateNow sk rs wk) :
    sk ≠ rs ∧ sk ≠ wk ∧ rs ≠ wk ∧ 2 ≤ dInf sk wk ∧ ¬RookSees rs wk sk wk := by
  rcases now with ⟨horizontal, sees⟩ | ⟨vertical, sees⟩
  · exact horizontal_source_valid horizontal sees
  · have mapped := horizontal_source_valid (sk := symSwap.f sk) (rs := symSwap.f rs) (wk := symSwap.f wk)
      vertical ((symSwap.sees_iff _ _ _ _).mpr sees)
    simpa only [symSwap.ne_iff, symSwap.dInf_eq, symSwap.sees_iff] using mapped

/-- Pure last-reply geometry transports through every certified board
isometry. Synthetic castling-free boards are used only in this proof. -/
theorem last_map (g : BoardSym) {sk rs wk : Square} (last : LastReply sk rs wk) :
    LastReply (g.f sk) (g.f rs) (g.f wk) := by
  obtain ⟨different, notKing, notRook, far⟩ := last_valid last
  let q := krkPos .white sk rs wk .black
  let r := krkPos .white (g.f sk) (g.f rs) (g.f wk) .black
  have material : IsKRK q .white sk rs wk := ⟨different, notKing, notRook, rfl⟩
  have mapped : IsKRK r .white (g.f sk) (g.f rs) (g.f wk) :=
    ⟨g.ne_iff.mpr different, g.ne_iff.mpr notKing, g.ne_iff.mpr notRook, rfl⟩
  have source : Matches q .white ⟨sk, rs, wk, false⟩ := ⟨material, rfl⟩
  have target : Matches r .white ((⟨sk, rs, wk, false⟩ : KRKState).map g) := ⟨mapped, rfl⟩
  have win := (weak_two_iff material rfl far).mpr (Or.inr last)
  have transported := krk_bound_transport g source rfl target win
  rcases (weak_two_iff mapped rfl (by rwa [g.dInf_eq])).mp transported with mate | done
  · obtain ⟨_, ⟨t, step⟩, _⟩ := (model_last_iff far).mpr last
    obtain ⟨u, legal, _⟩ := step_sound target (step_map g step)
    exact False.elim (mate.2 ⟨u, legal⟩)
  · exact done

theorem last_map_iff (g : BoardSym) {sk rs wk : Square} :
    LastReply (g.f sk) (g.f rs) (g.f wk) ↔ LastReply sk rs wk := by
  constructor
  · intro last
    simpa only [g.invol] using last_map g last
  · exact last_map g

/-- Pure immediate-mate geometry transports without transporting any
actual flags, incoming trace or repetition keys. -/
theorem immediate_map (g : BoardSym) {sk rs wk : Square} (now : MateNow sk rs wk) :
    MateNow (g.f sk) (g.f rs) (g.f wk) := by
  obtain ⟨different, notKing, notRook, far, notCheck⟩ := immediate_valid now
  let q := krkPos .white sk rs wk .white
  let r := krkPos .white (g.f sk) (g.f rs) (g.f wk) .white
  have material : IsKRK q .white sk rs wk := ⟨different, notKing, notRook, rfl⟩
  have mapped : IsKRK r .white (g.f sk) (g.f rs) (g.f wk) :=
    ⟨g.ne_iff.mpr different, g.ne_iff.mpr notKing, g.ne_iff.mpr notRook, rfl⟩
  have source : Matches q .white ⟨sk, rs, wk, true⟩ := ⟨material, rfl⟩
  have target : Matches r .white ((⟨sk, rs, wk, true⟩ : KRKState).map g) := ⟨mapped, rfl⟩
  obtain ⟨u, legal, goal⟩ := (KRKImmediate.immediate_iff material rfl far notCheck).mpr now
  have win : MateWithin .white 1 q := mateWithin_choose rfl legal goal
  have transported := krk_bound_transport g source rfl target win
  have move : ∃ v, Legal r v ∧ MateGoal .white v := by
    rcases transported with goal | ⟨_, chosen | defended⟩
    · cases goal.1
    · exact chosen.2
    · cases defended.1
  apply (KRKImmediate.immediate_iff mapped rfl (by rwa [g.dInf_eq]) ?_).mp move
  intro sees
  exact notCheck ((g.sees_iff _ _ _ _).mp sees)

theorem immediate_map_iff (g : BoardSym) {sk rs wk : Square} :
    MateNow (g.f sk) (g.f rs) (g.f wk) ↔ MateNow sk rs wk := by
  constructor
  · intro now
    simpa only [g.invol] using immediate_map g now
  · exact immediate_map g

end EndgameChess.Rules.KRKGeometricSymmetry
