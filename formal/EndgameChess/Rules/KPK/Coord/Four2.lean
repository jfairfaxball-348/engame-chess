import EndgameChess.Rules.KPK.Coord.Four

/-! Fourth rank: lowering a king on the sixth or seventh rank keeps its races. -/
namespace EndgameChess.Rules.KPK.Coord

/-! ### A high king

With the king on the sixth or seventh rank, lowering it by a rank keeps every race of the
region except one: lone king in front of the pawn on the last rank, king two files out on
the seventh. -/

/-- The short races of `M4`, read as distances. -/
def Near4 (a b c e f : Nat) : Prop :=
  (¬ Ch a b (c + 1) 5 1 ∨ Ch e f (c + 1) 5 1) ∧ (¬ Ch a b (c - 1) 5 1 ∨ Ch e f (c - 1) 5 1) ∧
  (¬ Ch a b (c + 1) 6 1 ∨ Ch e f (c + 1) 6 1) ∧ (¬ Ch a b (c - 1) 6 1 ∨ Ch e f (c - 1) 6 1) ∧
  (¬ Ch a b (c + 1) 6 2 ∨ Ch e f (c + 1) 6 2) ∧ (¬ Ch a b (c - 1) 6 2 ∨ Ch e f (c - 1) 6 2)

theorem near4_of {a b c e f : Nat} (hc : 1 ≤ c) (h : M4 a b c e f) : Near4 a b c e f := by
  obtain ⟨⟨r1, r2, r3, r4⟩, -, -⟩ := h
  exact ⟨rc1 hc (Or.inl rfl) r1, rc1 hc (Or.inr (by omega)) r3, rc1 hc (Or.inl rfl) r2,
    rc1 hc (Or.inr (by omega)) r4, (rc2 hc (Or.inl rfl) r2).imp id (fun w => w.1),
    (rc2 hc (Or.inr (by omega)) r4).imp id (fun w => w.1)⟩

/-- The exceptional shape. -/
def HiEx (a b c e f : Nat) : Prop := b = 6 ∧ e = c ∧ f = 7 ∧ (a = c + 2 ∨ a + 2 = c)

set_option maxHeartbeats 8000000 in
theorem rc_lower {a b c e f p q : Nat} (hc : 1 ≤ c) (h3 : c ≤ 3) (hb : b = 5 ∨ b = 6)
    (hp : p = c + 1 ∨ p + 1 = c) (hq : q = 5 ∨ q = 6) (ha : a ≤ 7) (sq : Sq4 c e f) (hf : f ≤ 7)
    (r : Rc a (b + 1) c e f p q) (N : Near4 a (b + 1) c e f) (ap : Apart a b e f)
    (nk : ¬ K4 a b c) (nx : ¬ HiEx a b c e f) : Rc a b c e f p q := by
  intro n kr
  by_cases k0 : KR a (b + 1) c p q n
  · exact r n k0
  have old := r (n + 1) (kr_step hc hp hq (show Near a (b + 1) a b by unfold Near; omega)
    (by omega) kr)
  clear r
  obtain ⟨z1, z2, z3, z4, z5, z6⟩ := N
  unfold Ch at z1 z2 z3 z4 z5 z6
  unfold HiEx at nx
  unfold K4 at nk
  unfold Sq4 at sq
  unfold Apart at ap
  unfold KR Thru at kr k0
  unfold WR Cross Hit at old ⊢
  unfold Ch at kr k0 old ⊢
  rcases hb with rfl | rfl <;> rcases hq with rfl | rfl <;> rcases hp with rfl | hp' <;>
    omega

set_option maxHeartbeats 4000000 in
theorem oc_lower {a b c e f t : Nat} (hb : b = 5 ∨ b = 6)
    (h : Oc a (b + 1) c e f t) (o0 : (Ch a b t 5 0 ∨ Ch a b t 6 0) → (Ch e f c 5 0 ∨ Ch e f c 6 0)) :
    Oc a b c e f t := by
  intro n kr
  by_cases zero : n = 0
  · subst zero
    exact o0 kr
  apply h n
  unfold Ch at *
  omega

end EndgameChess.Rules.KPK.Coord
