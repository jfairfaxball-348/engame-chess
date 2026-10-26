import EndgameChess.Rules.KRKEdgeDepth

namespace EndgameChess.Rules.KRKLastReply
open EndgameChess.KK KRKMateGeometry KRKImmediate
set_option maxHeartbeats 100000

/-- Among all neighbours of a legally separated weak king, at most one can
be ready for immediate mate with the same strong king and rook. -/
theorem ready_neighbour_unique {sk rs wk t u : Square}
    (far : 2 ≤ dInf sk wk) (stepT : dInf wk t = 1) (stepU : dInf wk u = 1)
    (readyT : MateNow sk rs t) (readyU : MateNow sk rs u) : t = u := by
  rcases readyT with ⟨ht, _⟩ | ⟨ht, _⟩ <;>
    rcases readyU with ⟨hu, _⟩ | ⟨hu, _⟩
  · have rankT := KRKEdgeDepth.horizontal_predecessor far stepT ht
    have rankU := KRKEdgeDepth.horizontal_predecessor far stepU hu
    obtain ⟨_, edgeT, _, leftT, rightT, middleT⟩ := ht
    obtain ⟨_, edgeU, _, leftU, rightU, middleU⟩ := hu
    have close : absDiff t.1.val u.1.val ≤ 1 := by
      simp only [absDiff]; omega
    clear edgeT edgeU leftT rightT middleT leftU rightU middleU far
    rw [square_eq_iff]
    simp only [dInf, absDiff] at stepT stepU close
    omega
  · have rankT := KRKEdgeDepth.horizontal_predecessor far stepT ht
    have fileU := KRKEdgeDepth.horizontal_predecessor
      (sk := symSwap.f sk) (wk := symSwap.f wk) (t := symSwap.f u)
      (by rwa [symSwap.dInf_eq]) (by rwa [symSwap.dInf_eq]) hu
    obtain ⟨_, edgeT, _, leftT, rightT, middleT⟩ := ht
    obtain ⟨_, edgeU, _, leftU, rightU, middleU⟩ := hu
    dsimp only [symSwap] at fileU edgeU leftU rightU middleU
    simp only [dInf, absDiff] at stepT stepU
    omega
  · have fileT := KRKEdgeDepth.horizontal_predecessor
      (sk := symSwap.f sk) (wk := symSwap.f wk) (t := symSwap.f t)
      (by rwa [symSwap.dInf_eq]) (by rwa [symSwap.dInf_eq]) ht
    have rankU := KRKEdgeDepth.horizontal_predecessor far stepU hu
    obtain ⟨_, edgeT, _, leftT, rightT, middleT⟩ := ht
    obtain ⟨_, edgeU, _, leftU, rightU, middleU⟩ := hu
    dsimp only [symSwap] at fileT edgeT leftT rightT middleT
    simp only [dInf, absDiff] at stepT stepU
    omega
  · have fileT := KRKEdgeDepth.horizontal_predecessor
      (sk := symSwap.f sk) (wk := symSwap.f wk) (t := symSwap.f t)
      (by rwa [symSwap.dInf_eq]) (by rwa [symSwap.dInf_eq]) ht
    have fileU := KRKEdgeDepth.horizontal_predecessor
      (sk := symSwap.f sk) (wk := symSwap.f wk) (t := symSwap.f u)
      (by rwa [symSwap.dInf_eq]) (by rwa [symSwap.dInf_eq]) hu
    obtain ⟨_, edgeT, _, leftT, rightT, middleT⟩ := ht
    obtain ⟨_, edgeU, _, leftU, rightU, middleU⟩ := hu
    dsimp only [symSwap] at fileT fileU edgeT leftT rightT middleT edgeU leftU rightU middleU
    have close : absDiff t.2.val u.2.val ≤ 1 := by
      simp only [absDiff]; omega
    clear edgeT edgeU leftT rightT middleT leftU rightU middleU far
    rw [square_eq_iff]
    simp only [dInf, absDiff] at stepT stepU close
    omega

def HorizontalLast (sk rs wk : Square) : Prop :=
  ((wk.2.val = 0 ∧ sk.2.val = 2) ∨ (wk.2.val = 7 ∧ sk.2.val = 5)) ∧
  rs.2.val ≠ wk.2.val ∧
  ((wk.1.val = 0 ∧ sk.1.val = 1 ∧ 3 ≤ rs.1.val) ∨
   (wk.1.val = 7 ∧ sk.1.val = 6 ∧ rs.1.val ≤ 4) ∨
   (0 < wk.1.val ∧ wk.1.val < 7 ∧
     (((sk.1.val = wk.1.val + 1 ∨ (wk.1.val = 6 ∧ sk.1.val = 6)) ∧
        rs.1.val + 1 = wk.1.val) ∨
      ((sk.1.val + 1 = wk.1.val ∨ (wk.1.val = 1 ∧ sk.1.val = 1)) ∧
        rs.1.val = wk.1.val + 1))))

/-- Evaluated two-ply weak-turn geometry. SafeRook retains the diagonal
capture boundary, including rooks just one rank inward. -/
def LastReply (sk rs wk : Square) : Prop :=
  SafeRook sk rs wk ∧
    (HorizontalLast sk rs wk ∨ HorizontalLast (sk.2, sk.1) (rs.2, rs.1) (wk.2, wk.1))

private theorem horizontal_last_necessary {sk rs wk t : Square}
    (far : 2 ≤ dInf sk wk)
    (step : StepM ⟨sk, rs, wk, false⟩ ⟨sk, rs, t, true⟩)
    (horizontal : Horizontal sk (rankTarget rs t) t)
    (ready : MateNow sk rs t)
    (every : ∀ u, StepM ⟨sk, rs, wk, false⟩ ⟨sk, rs, u, true⟩ → MateNow sk rs u) :
    HorizontalLast sk rs wk := by
  have distance : dInf wk t = 1 := by cases step with | lone h _ _ _ => exact h
  have notRook : t ≠ rs := by cases step with | lone _ h _ _ => exact h
  have notCheck : ¬RookSees rs t sk t := by cases step with | lone _ _ _ h => exact h
  have sameRank := KRKEdgeDepth.horizontal_predecessor far distance horizontal
  obtain ⟨_, edge, gap, left, right, middle⟩ := horizontal
  change 2 ≤ absDiff rs.1.val t.1.val at gap
  have off : rs.2.val ≠ wk.2.val := by
    intro same
    apply notCheck
    simp only [RookSees, RookLine, OnSeg, ne_iff_coords] at notRook ⊢
    omega
  have stepFile : absDiff wk.1.val t.1.val = 1 := by
    simpa only [dInf, sameRank, absDiff, Nat.sub_self, Nat.add_zero,
      Nat.zero_add, Nat.max_zero] using distance
  by_cases toRight : t.1.val = wk.1.val + 1
  · have away : 0 < wk.1.val → rs.1.val + 1 = wk.1.val := by
      intro positive
      let u : Square := (⟨wk.1.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) wk.1.isLt⟩, wk.2)
      by_cases rookFile : rs.1.val = u.1.val
      · dsimp only [u] at rookFile; omega
      · have other : StepM ⟨sk, rs, wk, false⟩ ⟨sk, rs, u, true⟩ := by
          refine StepM.lone ?_ ?_ ?_ ?_
          · simp only [u, dInf, absDiff]; omega
          · simp only [u, ne_iff_coords]; omega
          · simp only [u, dInf, absDiff]; omega
          · intro seen; exact seen.1.2.elim rookFile (by dsimp [u]; exact off)
        have same := ready_neighbour_unique far distance
          (show dInf wk u = 1 by simp only [u, dInf, absDiff]; omega) ready (every u other)
        have x := congrArg (fun s : Square => s.1.val) same
        dsimp only [u] at x
        omega
    clear step ready every far notCheck notRook distance stepFile
    refine ⟨by omega, off, ?_⟩
    by_cases corner : wk.1.val = 0
    · left
      have king := middle (by omega) (by omega)
      simp only [absDiff] at gap
      exact ⟨corner, by omega, by omega⟩
    · right; right
      have positive : 0 < wk.1.val := by omega
      refine ⟨positive, by omega, Or.inl ⟨?_, away positive⟩⟩
      by_cases top : t.1.val = 7
      · have king := right top; omega
      · have king := middle (by omega) (by omega); omega
  · have toLeft : t.1.val + 1 = wk.1.val := by simp only [absDiff] at stepFile; omega
    have away : wk.1.val < 7 → rs.1.val = wk.1.val + 1 := by
      intro small
      let u : Square := (⟨wk.1.val + 1, Nat.add_lt_add_right small 1⟩, wk.2)
      by_cases rookFile : rs.1.val = u.1.val
      · exact rookFile
      · have other : StepM ⟨sk, rs, wk, false⟩ ⟨sk, rs, u, true⟩ := by
          refine StepM.lone ?_ ?_ ?_ ?_
          · simp only [u, dInf, absDiff]; omega
          · simp only [u, ne_iff_coords]; omega
          · simp only [u, dInf, absDiff]; omega
          · intro seen; exact seen.1.2.elim rookFile (by dsimp [u]; exact off)
        have same := ready_neighbour_unique far distance
          (show dInf wk u = 1 by simp only [u, dInf, absDiff]; omega) ready (every u other)
        have x := congrArg (fun s : Square => s.1.val) same
        dsimp only [u] at x
        omega
    clear step ready every far notCheck notRook distance stepFile
    refine ⟨by omega, off, ?_⟩
    by_cases corner : wk.1.val = 7
    · right; left
      have king := middle (by omega) (by omega)
      simp only [absDiff] at gap
      exact ⟨corner, by omega, by omega⟩
    · right; right
      have small : wk.1.val < 7 := by omega
      refine ⟨by omega, small, Or.inr ⟨?_, away small⟩⟩
      by_cases bottom : t.1.val = 0
      · have king := left bottom; omega
      · have king := middle (by omega) (by omega); omega

private theorem swap_ready {sk rs wk : Square} (ready : MateNow sk rs wk) :
    MateNow (symSwap.f sk) (symSwap.f rs) (symSwap.f wk) := by
  rcases ready with ⟨horizontal, move⟩ | ⟨vertical, move⟩
  · exact Or.inr ⟨horizontal, (symSwap.sees_iff _ _ _ _).mpr move⟩
  · exact Or.inl ⟨vertical, (symSwap.sees_iff _ _ _ _).mpr move⟩

set_option maxHeartbeats 500000 in
private theorem last_case_0 {sk rs wk : Square}
    (edge : (wk.2.val = 0 ∧ sk.2.val = 2) ∨ (wk.2.val = 7 ∧ sk.2.val = 5))
    (off : rs.2.val ≠ wk.2.val)
    (cornerL : wk.1.val = 0 ∧ sk.1.val = 1 ∧ 3 ≤ rs.1.val) :
    ∃ t, StepM ⟨sk, rs, wk, false⟩ ⟨sk, rs, t, true⟩ ∧ MateNow sk rs t ∧
      ∀ u, StepM ⟨sk, rs, wk, false⟩ ⟨sk, rs, u, true⟩ → u = t := by
  obtain ⟨hx, sx, gap⟩ := cornerL
  let t : Square := (1, wk.2)
  have geometry : StepM ⟨sk, rs, wk, false⟩ ⟨sk, rs, t, true⟩ ∧
      Horizontal sk (rankTarget rs t) t ∧ RookSees rs (rankTarget rs t) sk t := by
    rcases edge with ⟨hy, sy⟩ | ⟨hy, sy⟩
    all_goals
      refine ⟨StepM.lone ?_ ?_ ?_ ?_, ?_, ?_⟩ <;> dsimp [t] <;>
        simp [Horizontal, rankTarget, RookSees, RookLine, OnSeg, ne_iff_coords, dInf, absDiff, hy, sy, hx, sx] at * <;> omega
  refine ⟨t, geometry.1, Or.inl geometry.2, ?_⟩
  clear geometry
  intro u step
  cases step with
  | lone distance notRook far notCheck =>
    rw [square_eq_iff]
    dsimp [t]
    clear t
    rcases edge with ⟨hy, sy⟩ | ⟨hy, sy⟩
    all_goals
      simp [dInf, absDiff, hy, sy, hx, sx] at distance far ⊢
      omega

set_option maxHeartbeats 500000 in
private theorem last_case_1 {sk rs wk : Square}
    (edge : (wk.2.val = 0 ∧ sk.2.val = 2) ∨ (wk.2.val = 7 ∧ sk.2.val = 5))
    (off : rs.2.val ≠ wk.2.val)
    (cornerR : wk.1.val = 7 ∧ sk.1.val = 6 ∧ rs.1.val ≤ 4) :
    ∃ t, StepM ⟨sk, rs, wk, false⟩ ⟨sk, rs, t, true⟩ ∧ MateNow sk rs t ∧
      ∀ u, StepM ⟨sk, rs, wk, false⟩ ⟨sk, rs, u, true⟩ → u = t := by
  obtain ⟨hx, sx, gap⟩ := cornerR
  let t : Square := (6, wk.2)
  have geometry : StepM ⟨sk, rs, wk, false⟩ ⟨sk, rs, t, true⟩ ∧
      Horizontal sk (rankTarget rs t) t ∧ RookSees rs (rankTarget rs t) sk t := by
    rcases edge with ⟨hy, sy⟩ | ⟨hy, sy⟩
    all_goals
      refine ⟨StepM.lone ?_ ?_ ?_ ?_, ?_, ?_⟩ <;> dsimp [t] <;>
        simp [Horizontal, rankTarget, RookSees, RookLine, OnSeg, ne_iff_coords, dInf, absDiff, hy, sy, hx, sx] at * <;> omega
  refine ⟨t, geometry.1, Or.inl geometry.2, ?_⟩
  clear geometry
  intro u step
  cases step with
  | lone distance notRook far notCheck =>
    rw [square_eq_iff]
    dsimp [t]
    clear t
    rcases edge with ⟨hy, sy⟩ | ⟨hy, sy⟩
    all_goals
      simp [dInf, absDiff, hy, sy, hx, sx] at distance far ⊢
      omega

set_option maxHeartbeats 500000 in
private theorem last_case_2 {sk rs wk : Square}
    (edge : (wk.2.val = 0 ∧ sk.2.val = 2) ∨ (wk.2.val = 7 ∧ sk.2.val = 5))
    (off : rs.2.val ≠ wk.2.val)
    (inside : 0 < wk.1.val) (small : wk.1.val < 7)
    (right : (sk.1.val = wk.1.val + 1 ∨ (wk.1.val = 6 ∧ sk.1.val = 6)) ∧ rs.1.val + 1 = wk.1.val) :
    ∃ t, StepM ⟨sk, rs, wk, false⟩ ⟨sk, rs, t, true⟩ ∧ MateNow sk rs t ∧
      ∀ u, StepM ⟨sk, rs, wk, false⟩ ⟨sk, rs, u, true⟩ → u = t := by
  let t : Square := (⟨wk.1.val + 1, Nat.add_lt_add_right small 1⟩, wk.2)
  have geometry : StepM ⟨sk, rs, wk, false⟩ ⟨sk, rs, t, true⟩ ∧
      Horizontal sk (rankTarget rs t) t ∧ RookSees rs (rankTarget rs t) sk t := by
    rcases edge with ⟨hy, sy⟩ | ⟨hy, sy⟩
    all_goals
      refine ⟨StepM.lone ?_ ?_ ?_ ?_, ?_, ?_⟩ <;> dsimp [t] <;>
        simp [Horizontal, rankTarget, RookSees, RookLine, OnSeg, ne_iff_coords, dInf, absDiff, hy, sy] at * <;> omega
  refine ⟨t, geometry.1, Or.inl geometry.2, ?_⟩
  clear geometry
  intro u step
  cases step with
  | lone distance notRook far notCheck =>
    rw [square_eq_iff]
    dsimp [t]
    clear t
    rcases right with ⟨sx | ⟨corner, sx⟩, rx⟩ <;>
      rcases edge with ⟨hy, sy⟩ | ⟨hy, sy⟩
    all_goals
      have avoid : u.1.val ≠ rs.1.val := by
        intro same
        apply notCheck
        simp only [RookSees, RookLine, OnSeg, ne_iff_coords] at notRook ⊢
        omega
      clear notCheck notRook
      simp [dInf, absDiff, hy, sy, sx] at distance far ⊢
      omega

set_option maxHeartbeats 500000 in
private theorem last_case_3 {sk rs wk : Square}
    (edge : (wk.2.val = 0 ∧ sk.2.val = 2) ∨ (wk.2.val = 7 ∧ sk.2.val = 5))
    (off : rs.2.val ≠ wk.2.val)
    (inside : 0 < wk.1.val) (small : wk.1.val < 7)
    (left : (sk.1.val + 1 = wk.1.val ∨ (wk.1.val = 1 ∧ sk.1.val = 1)) ∧ rs.1.val = wk.1.val + 1) :
    ∃ t, StepM ⟨sk, rs, wk, false⟩ ⟨sk, rs, t, true⟩ ∧ MateNow sk rs t ∧
      ∀ u, StepM ⟨sk, rs, wk, false⟩ ⟨sk, rs, u, true⟩ → u = t := by
  let t : Square := (⟨wk.1.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) wk.1.isLt⟩, wk.2)
  have geometry : StepM ⟨sk, rs, wk, false⟩ ⟨sk, rs, t, true⟩ ∧
      Horizontal sk (rankTarget rs t) t ∧ RookSees rs (rankTarget rs t) sk t := by
    rcases edge with ⟨hy, sy⟩ | ⟨hy, sy⟩
    all_goals
      refine ⟨StepM.lone ?_ ?_ ?_ ?_, ?_, ?_⟩ <;> dsimp [t] <;>
        simp [Horizontal, rankTarget, RookSees, RookLine, OnSeg, ne_iff_coords, dInf, absDiff, hy, sy] at * <;> omega
  refine ⟨t, geometry.1, Or.inl geometry.2, ?_⟩
  clear geometry
  intro u step
  cases step with
  | lone distance notRook far notCheck =>
    rw [square_eq_iff]
    dsimp [t]
    clear t
    have kingCases : sk.1.val = wk.1.val - 1 ∨ (wk.1.val = 1 ∧ sk.1.val = 1) := by omega
    have rx := left.2
    clear left
    rcases kingCases with sx | ⟨corner, sx⟩ <;>
      rcases edge with ⟨hy, sy⟩ | ⟨hy, sy⟩
    all_goals
      have avoid : u.1.val ≠ rs.1.val := by
        intro same
        apply notCheck
        simp only [RookSees, RookLine, OnSeg, ne_iff_coords] at notRook ⊢
        omega
      clear notCheck notRook
      simp [dInf, absDiff, hy, sy, sx] at distance far ⊢
      omega

private theorem horizontal_last_sufficient {sk rs wk : Square}
    (h : HorizontalLast sk rs wk) :
    ∃ t, StepM ⟨sk, rs, wk, false⟩ ⟨sk, rs, t, true⟩ ∧ MateNow sk rs t ∧
      ∀ u, StepM ⟨sk, rs, wk, false⟩ ⟨sk, rs, u, true⟩ → u = t := by
  obtain ⟨edge, off, cornerL | cornerR | ⟨inside, small, right | left⟩⟩ := h
  · exact last_case_0 edge off cornerL
  · exact last_case_1 edge off cornerR
  · exact last_case_2 edge off inside small right
  · exact last_case_3 edge off inside small left

/-- Specific last-defender-move geometry, not a recursive game solver. -/
theorem model_last_iff {sk rs wk : Square} (far : 2 ≤ dInf sk wk) :
    (SafeRook sk rs wk ∧
      (∃ t, StepM ⟨sk, rs, wk, false⟩ ⟨sk, rs, t, true⟩) ∧
      ∀ t, StepM ⟨sk, rs, wk, false⟩ ⟨sk, rs, t, true⟩ → MateNow sk rs t) ↔
      LastReply sk rs wk := by
  constructor
  · rintro ⟨safe, ⟨t, step⟩, every⟩
    have ready := every t step
    refine ⟨safe, ?_⟩
    rcases ready with ⟨horizontal, move⟩ | ⟨vertical, move⟩
    · exact Or.inl (horizontal_last_necessary far step horizontal (Or.inl ⟨horizontal, move⟩) every)
    · right
      have everySwap : ∀ u,
          StepM ⟨symSwap.f sk, symSwap.f rs, symSwap.f wk, false⟩
            ⟨symSwap.f sk, symSwap.f rs, u, true⟩ →
          MateNow (symSwap.f sk) (symSwap.f rs) u := by
        intro u swappedStep
        have originalStep := step_map symSwap swappedStep
        have originalReady := every (symSwap.f u) originalStep
        exact swap_ready originalReady
      exact horizontal_last_necessary
        (by change 2 ≤ dInf (symSwap.f sk) (symSwap.f wk); rwa [symSwap.dInf_eq])
        (step_map symSwap step) vertical (swap_ready (Or.inr ⟨vertical, move⟩)) everySwap
  · rintro ⟨safe, horizontal | vertical⟩
    · obtain ⟨t, step, ready, unique⟩ := horizontal_last_sufficient horizontal
      exact ⟨safe, ⟨t, step⟩, fun u hu => by rw [unique u hu]; exact ready⟩
    · obtain ⟨t, step, ready, unique⟩ := horizontal_last_sufficient vertical
      refine ⟨safe, ⟨symSwap.f t, step_map symSwap step⟩, ?_⟩
      intro u hu
      have same := unique (symSwap.f u) (step_map symSwap hu)
      have readyU : MateNow (symSwap.f sk) (symSwap.f rs) (symSwap.f u) := by
        rw [same]; exact ready
      exact swap_ready readyU

end EndgameChess.Rules.KRKLastReply
