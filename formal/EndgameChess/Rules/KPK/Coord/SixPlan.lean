import EndgameChess.Rules.KPK.Coord.SixMain
import EndgameChess.Rules.KPK.Coord.SixCover

/-! The sixth and seventh ranks of a bishop or centre pawn are classified: outside the
guards the pawn owner wins. -/
namespace EndgameChess.Rules.KPK.Coord
open EndgameChess.KK

def PS (j a b c d e f : Nat) : Prop :=
  2 ≤ c ∧ j ≤ 10 ∧ ((d = 6 ∧ j ≤ 2 ∧ SevS j a b c e f) ∨ (d = 5 ∧ ¬ S5 a b c e f ∧ Phi j a b c))

def PW (j a b c d e f : Nat) : Prop :=
  2 ≤ c ∧ j ≤ 10 ∧ ((d = 6 ∧ j ≤ 2 ∧ SevW j a b c e f) ∨ (d = 6 ∧ 2 ≤ j ∧ W6 a b c e f) ∨
    (d = 5 ∧ W5win j a b c e f))

theorem domS_of_step {a b c e f x y : Nat} (D : Dom a b c 6 e f) (st : WeakStep a b c 6 e f x y) :
    DomS a b c 6 x y := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  exact ⟨⟨u1, u2, u3, u4, u5, st.2.1, st.2.2.1, D.k2, st.k6, st.k7⟩, st.k8⟩

/-- The winning plan on the sixth and seventh ranks. -/
def sixPlan : Plan where
  S := PS
  W := PW
  S_le := fun h => by have := h.2.1; omega
  W_le := fun h => by have := h.2.1; omega
  strong := by
    intro j a b c d e f D h
    obtain ⟨hc, hj, ⟨rfl, h2, h⟩ | ⟨rfl, n, ph⟩⟩ := h
    · rcases sev_strong (W := PW) D hc h2 h with q | ⟨i, rfl, x, y, st, w⟩
      · exact Or.inl q
      · exact Or.inr ⟨i, rfl, x, y, st, hc, by omega, Or.inl ⟨rfl, by omega, w⟩⟩
    · rcases six_move D hc n ph (fun sq k bs u => step5_cover D hc n sq k bs u) with
        ⟨fr, w⟩ | ⟨i, rfl, x, y, st, w⟩
      · exact Or.inl (Or.inl ⟨fr, by omega, 10, by omega, hc, by omega, Or.inr (Or.inl ⟨rfl, by omega, w⟩)⟩)
      · exact Or.inr ⟨i, rfl, x, y, st, hc, by omega, Or.inr (Or.inr ⟨rfl, w⟩)⟩
  weak := by
    intro j a b c d e f D h
    obtain ⟨hc, hj, ⟨rfl, h2, h⟩ | ⟨rfl, two, w⟩ | ⟨rfl, ph, keep, reply, all⟩⟩ := h
    · obtain ⟨q1, q2, q3⟩ := sev_weak D hc h
      exact ⟨q1, q2, fun x y st => ⟨j, Nat.le_refl j, hc, hj, Or.inl ⟨rfl, h2, q3 x y st⟩⟩⟩
    · obtain ⟨q1, q2, q3⟩ := w
      refine ⟨q1, q2, fun x y st => ⟨2, two, hc, by omega, Or.inl ⟨rfl, by omega, ?_⟩⟩⟩
      exact sev_cover (domS_of_step D st) hc (q3 x y st)
    · exact ⟨keep, reply, fun x y st => ⟨j, Nat.le_refl j, hc, hj, Or.inr ⟨rfl, all x y st, ph⟩⟩⟩

/-- A bishop or centre pawn on the sixth rank, pawn owner to move, outside the guard: an
actual win. With `fresh_six_hold` this classifies these roots. -/
theorem fresh_sixth_win {σ : Colour} {q : Position} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk) (turn : q.turn = σ)
    (safe : ¬ PawnSees σ ps wk) (file : 2 ≤ mx ps ps) (rank : height σ ps = 5)
    (out : ¬ S5 (mx ps sk) (height σ sk) (mx ps ps) (mx ps wk) (height σ wk)) :
    FreshGame.Within σ 604 (FreshGame.fresh q) := by
  have cfg := fresh_cfg h fresh
  have D : Dom (mx ps sk) (height σ sk) (mx ps ps) (height σ ps) (mx ps wk) (height σ wk) :=
    dom_of_cfg cfg
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  refine fresh_plan_strong (P := sixPlan) (j := 10) h fresh turn safe
    ⟨file, by omega, Or.inr ⟨rank, out, Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, ?_⟩)))⟩⟩
  unfold Ch
  omega

end EndgameChess.Rules.KPK.Coord
