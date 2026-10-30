import EndgameChess.Rules.KPK.Coord.Forced
import EndgameChess.Rules.KPK.Coord.Replies

/-! The rule of the square. If the lone king is too far from the promotion square
and the pawn's own king is not ahead of it on its file, the pawn simply runs. The
one exception is a corner stalemate, avoided by a single waiting king move. -/
namespace EndgameChess.Rules.KPK.Coord
open EndgameChess.KK

/-- Pushes the pawn still needs, counting the first double step. -/
def Pushes (d n : Nat) : Prop := (d = 1 ∧ n = 5) ∨ (2 ≤ d ∧ n + d = 7)

/-- The lone king is more than `m` king steps from the promotion square. -/
def Outside (m c e f : Nat) : Prop := c + m < e ∨ e + m < c ∨ f + m < 7

/-- The pawn's own king does not stand ahead of it. -/
def Clear (a b c d : Nat) : Prop := ¬ (a = c ∧ d < b)

/-- A rook or queen on `b8` would stalemate the king on `a1`, next to `a3` or `b3`. -/
def CornerTrap (a b c d e f : Nat) : Prop :=
  d = 6 ∧ c = 1 ∧ e = 0 ∧ f = 0 ∧ a ≤ 1 ∧ b = 2

def RunS (a b c d e f : Nat) : Prop :=
  Clear a b c d ∧ ∃ n, Pushes d n ∧ Outside n c e f

def RunW (a b c d e f : Nat) : Prop :=
  Clear a b c d ∧ ¬ Capture a b c d e f ∧ ∃ n, Pushes d n ∧ Outside (n + 1) c e f

set_option maxHeartbeats 2000000 in
/-- A promoted rook keeps a legal reply unless the corner trap is on the board. -/
theorem rook_reply {a b c e f : Nat} (ha : a ≤ 7) (hb : b ≤ 7) (hc : c ≤ 3) (he : e ≤ 7)
    (hf : f ≤ 6) (apart : Apart a b e f) (off : Outside 1 c e f) (side : e ≠ c)
    (noTrap : ¬ (c = 1 ∧ e = 0 ∧ f = 0 ∧ a ≤ 1 ∧ b = 2)) :
    ∃ x y, Near e f x y ∧ x ≤ 7 ∧ y ≤ 7 ∧ ¬ (x = c ∧ y = 7) ∧ Apart a b x y ∧
      (OffRook c x y ∨ Shielded a b c x y) := by
  apply Classical.byContradiction
  intro no
  have t (x y : Nat) : ¬ (Near e f x y ∧ x ≤ 7 ∧ y ≤ 7 ∧ ¬ (x = c ∧ y = 7) ∧ Apart a b x y ∧
      (OffRook c x y ∨ Shielded a b c x y)) := fun h => no ⟨x, y, h⟩
  have h1 := t (e + 1) f
  have h2 := t (e - 1) f
  have h3 := t e (f + 1)
  have h4 := t e (f - 1)
  have h5 := t (e + 1) (f - 1)
  have h6 := t (e - 1) (f - 1)
  have h7 := t (e + 1) (f + 1)
  have h8 := t (e - 1) (f + 1)
  unfold Near Apart OffRook Shielded at h1 h2 h3 h4 h5 h6 h7 h8
  unfold Outside at off
  unfold Apart at apart
  have z0 : f = 0 ∨ 1 ≤ f := by omega
  have z1 : e = 0 ∨ 1 ≤ e := by omega
  have z2 : c = 0 ∨ 1 ≤ c := by omega
  rcases apart with k | k | k | k <;>
    rcases Nat.lt_or_gt_of_ne side with g | g <;>
    rcases z0 with z0 | z0 <;> rcases z1 with z1 | z1 <;> omega

/-- With no trap, promoting to a rook on `(c,7)` wins. -/
theorem run_rook {a b c e f : Nat} (ha : a ≤ 7) (hb : b ≤ 7) (hc : c ≤ 3) (he : e ≤ 7) (hf : f ≤ 7)
    (apart : Apart a b e f) (off : Outside 1 c e f)
    (noTrap : ¬ (c = 1 ∧ e = 0 ∧ f = 0 ∧ a ≤ 1 ∧ b = 2)) : RookGood a b c e f := by
  have safe : PieceSafe a b c e f := by
    unfold PieceSafe Capture Near
    unfold Outside at off
    omega
  refine ⟨safe, ?_⟩
  by_cases rank : RankCheck a b c e f
  · exact Or.inl rank
  by_cases file : FileCheck a b c e f
  · exact Or.inr (Or.inl file)
  refine Or.inr (Or.inr ?_)
  unfold RankCheck at rank
  unfold FileCheck at file
  unfold Apart at apart
  by_cases top : f = 7
  · refine ⟨e, 6, ?_, by omega, by omega, by omega, ?_, Or.inl ?_⟩
    · unfold Near; omega
    · unfold Apart; omega
    · unfold OffRook; omega
  by_cases same : e = c
  · refine ⟨c + 1, f, ?_, by omega, by omega, by omega, ?_, Or.inl ?_⟩
    · unfold Near; omega
    · unfold Apart; omega
    · unfold OffRook; omega
  exact rook_reply ha hb hc he (by omega) apart off same noTrap

/-- Phases of the run: the only quiet move is the waiting move out of the trap. -/
def runPlan : Plan where
  S j a b c d e f := RunS a b c d e f ∧
    ((j = 0 ∧ ¬ CornerTrap a b c d e f) ∨ (j = 1 ∧ CornerTrap a b c d e f))
  W j a b c d e f := RunW a b c d e f ∧ ((j = 0 ∧ ¬ (d = 6 ∧ b = 2)) ∨ j = 1)
  S_le := by
    intro j a b c d e f h
    obtain ⟨_, h⟩ := h
    omega
  W_le := by
    intro j a b c d e f h
    obtain ⟨_, h⟩ := h
    omega
  strong := by
    intro j a b c d e f D h
    obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
    have k1 := D.1.k1
    obtain ⟨⟨clear, n, pushes, out⟩, side⟩ := h
    unfold Clear at clear
    unfold Pushes at pushes
    unfold Outside at out
    rcases side with ⟨rfl, noTrap⟩ | ⟨rfl, trap⟩
    · refine Or.inl ?_
      by_cases top : d = 6
      · subst top
        have sq : Free a b e f c (6 + 1) := by unfold Free; omega
        have good : RookGood a b c e f := run_rook u1 u2 u3 u6 u7 k1
          (by unfold Outside; omega)
          (fun t => noTrap ⟨rfl, t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2⟩)
        exact Or.inr (Or.inr (Or.inr ⟨rfl, sq, good⟩))
      by_cases low : d = 1
      · subst low
        refine Or.inr (Or.inl ⟨rfl, by unfold Free; omega, by unfold Free; omega, 1, by omega, ?_, Or.inr rfl⟩)
        refine ⟨by unfold Clear; omega, by unfold Capture Near; omega, 4, ?_, ?_⟩
        · unfold Pushes; omega
        · unfold Outside; omega
      · refine Or.inl ⟨by unfold Free; omega, by omega, 1, by omega, ?_, Or.inr rfl⟩
        refine ⟨by unfold Clear; omega, by unfold Capture Near; omega, n - 1, ?_, ?_⟩
        · unfold Pushes; omega
        · unfold Outside; omega
    · refine Or.inr ?_
      unfold CornerTrap at trap
      refine ⟨0, rfl, a, 3, ?_, ?_, Or.inl ⟨rfl, by omega⟩⟩
      · unfold KingStep Near Apart; omega
      · refine ⟨by unfold Clear; omega, by unfold Capture Near; omega, n, ?_, ?_⟩
        · unfold Pushes; omega
        · unfold Outside; omega
  weak := by
    intro j a b c d e f D h
    obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
    obtain ⟨⟨clear, keep, n, pushes, out⟩, side⟩ := h
    have pushes' := pushes
    have out' := out
    unfold Pushes at pushes'
    unfold Outside at out'
    refine ⟨keep, weak_reply D (by omega) keep, ?_⟩
    intro x y step
    obtain ⟨⟨n1, n2, n3, n4⟩, n5, n6⟩ := WeakStep.bounds step
    have run : RunS a b c d x y := ⟨clear, n, pushes, by unfold Outside; omega⟩
    by_cases trap : CornerTrap a b c d x y
    · have t := trap
      unfold CornerTrap at t
      refine ⟨1, ?_, run, Or.inr ⟨rfl, trap⟩⟩
      omega
    · refine ⟨0, by omega, run, Or.inl ⟨rfl, trap⟩⟩

/-- The rule of the square, pawn owner to move, in a fresh game: an actual win, by a
waiting king move first if the corner stalemate is on the board. -/
theorem fresh_runaway_strong {σ : Colour} {q : Position} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk) (turn : q.turn = σ)
    (safe : ¬ PawnSees σ ps wk)
    (run : RunS (mx ps sk) (height σ sk) (mx ps ps) (height σ ps) (mx ps wk) (height σ wk)) :
    FreshGame.Within σ 604 (FreshGame.fresh q) := by
  by_cases trap : CornerTrap (mx ps sk) (height σ sk) (mx ps ps) (height σ ps) (mx ps wk) (height σ wk)
  · exact fresh_plan_strong (P := runPlan) (j := 1) h fresh turn safe ⟨run, Or.inr ⟨rfl, trap⟩⟩
  · exact fresh_plan_strong (P := runPlan) (j := 0) h fresh turn safe ⟨run, Or.inl ⟨rfl, trap⟩⟩

/-- The rule of the square, lone king to move, in a fresh game: an actual win. -/
theorem fresh_runaway_weak {σ : Colour} {q : Position} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk) (turn : q.turn = σ.opp)
    (run : RunW (mx ps sk) (height σ sk) (mx ps ps) (height σ ps) (mx ps wk) (height σ wk)) :
    FreshGame.Within σ 604 (FreshGame.fresh q) :=
  fresh_plan_weak (P := runPlan) (j := 1) h fresh turn ⟨run, Or.inr rfl⟩

end EndgameChess.Rules.KPK.Coord
