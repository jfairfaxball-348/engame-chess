import EndgameChess.Rules.KPK.Coord.Runaway

/-! Key squares of a non-rook pawn. A king two ranks ahead of its pawn, on the pawn's
file or an adjacent one, wins with either side to move. The king advances, or the pawn
moves when the lone king would otherwise take the opposition; near the last ranks the
opposition no longer holds. -/
namespace EndgameChess.Rules.KPK.Coord
open EndgameChess.KK

/-- The pawn's file or an adjacent one. -/
def Cl (a c : Nat) : Prop := a ≤ c + 1 ∧ c ≤ a + 1

/-- Phase budget of level `k`; two more low on the board. -/
def Bud (d j k : Nat) : Prop := (3 ≤ d ∧ k ≤ j) ∨ (d ≤ 2 ∧ k + 2 ≤ j)

def Stale (a c d e f : Nat) : Prop := c = 1 ∧ d = 5 ∧ a = 2 ∧ e = 0 ∧ f = 7

/-- The lone king stands on the only square that stops a side-step around it. -/
def Blk (a c d e f : Nat) : Prop := a ≠ c ∧ e = c ∧ f = d + 4

def SL2 (j a b c d e f : Nat) : Prop :=
  Cl a c ∧ b = d + 2 ∧ d ≤ 5 ∧
    ((3 ≤ d ∧ ¬ (d = 5 ∧ a = c)) ∨ (d = 5 ∧ a = c ∧ 1 ≤ j) ∨
      (d ≤ 2 ∧ 1 ≤ j ∧ ¬ Blk a c d e f) ∨ (d ≤ 2 ∧ 2 ≤ j))

def WL2 (j a b c d e f : Nat) : Prop :=
  Cl a c ∧ b = d + 2 ∧ d ≤ 5 ∧ ¬ Near e f c d ∧ ¬ Stale a c d e f ∧
    ((3 ≤ d ∧ ¬ (d = 5 ∧ a = c)) ∨ (d = 5 ∧ a = c ∧ 1 ≤ j) ∨
      (d ≤ 2 ∧ 2 ≤ j) ∨ (d ≤ 2 ∧ a = c ∧ e = c ∧ f = d + 4 ∧ 1 ≤ j))

def Lev (j a c d : Nat) : Prop :=
  (d = 5 ∧ a ≠ c) ∨ (d = 5 ∧ a = c ∧ 1 ≤ j) ∨
    (d ≤ 4 ∧ ((a = c + 1 ∧ Bud d j 2) ∨ (a = c ∧ Bud d j 3) ∨ (a + 1 = c ∧ Bud d j 4)))

def SL1 (j a b c d e f : Nat) : Prop :=
  Cl a c ∧ b = d + 1 ∧ d ≤ 5 ∧ ¬ (d ≤ 3 ∧ e = a ∧ f = d + 3) ∧
    (Lev j a c d ∨ (d ≤ 4 ∧ a = c ∧ Bud d j 1 ∧ ¬ (e = c ∧ f = d + 3) ∧ ¬ Near e f c d))

def WL1 (j a b c d e f : Nat) : Prop :=
  Cl a c ∧ b = d + 1 ∧ d ≤ 5 ∧ ¬ Stale a c d e f ∧
    (3 < d ∨ (e = a ∧ f = d + 3) ∨ ¬ Near e f a (d + 3)) ∧
    (Lev j a c d ∨ (d ≤ 4 ∧ a = c ∧ e = c ∧ f = d + 3 ∧ Bud d j 1))

def L0Lev (j a c d : Nat) : Prop := (a = c + 1 ∧ Bud d j 3) ∨ (a + 1 = c ∧ Bud d j 5)

def SL0 (j a b c d f : Nat) : Prop := L0Lev j a c d ∧ b = d ∧ d ≤ 5 ∧ f ≤ d

def WL0 (j a b c d f : Nat) : Prop := L0Lev j a c d ∧ b = d ∧ d ≤ 5 ∧ f + 1 ≤ d

def SL3 (a b c d f : Nat) : Prop := Cl a c ∧ b = d + 3 ∧ d ≤ 2 ∧ d + 3 ≤ f

def WL3 (a b c d f : Nat) : Prop := Cl a c ∧ b = d + 3 ∧ d ≤ 2 ∧ d + 4 ≤ f

/-- King beside the seventh-rank pawn or next to the promotion square. -/
def R6 (a b c d : Nat) : Prop := d = 6 ∧ (a = c + 1 ∨ a + 1 = c) ∧ (b = 6 ∨ b = 7)

def SZ (a b c d e f : Nat) : Prop :=
  d = 5 ∧ a = c + 1 ∧ b = 5 ∧ f = 7 ∧ (e = c ∨ e = c + 2)

def WZ (a b c d e f : Nat) : Prop := d = 5 ∧ a = c + 1 ∧ b = 5 ∧ f = 7 ∧ e = c + 1

def WB (j a b c d e f : Nat) : Prop :=
  d = 6 ∧ a = c + 1 ∧ b = 5 ∧ f = 7 ∧ (e = c ∨ e = c + 2) ∧ 1 ≤ j

def SB (j a b c d e f : Nat) : Prop :=
  d = 6 ∧ a = c + 1 ∧ b = 5 ∧ ((e + 1 = c ∧ f = 6 ∧ 1 ≤ j) ∨ (e = c + 3 ∧ (f = 6 ∨ f = 7)))

def KS (j a b c d e f : Nat) : Prop :=
  2 ≤ c ∧ j ≤ 9 ∧ (SL2 j a b c d e f ∨ SL1 j a b c d e f ∨ SL0 j a b c d f ∨ SL3 a b c d f ∨
    R6 a b c d ∨ SZ a b c d e f ∨ SB j a b c d e f)

def KW (j a b c d e f : Nat) : Prop :=
  2 ≤ c ∧ j ≤ 9 ∧ (WL2 j a b c d e f ∨ WL1 j a b c d e f ∨ WL0 j a b c d f ∨ WL3 a b c d f ∨
    R6 a b c d ∨ WZ a b c d e f ∨ WB j a b c d e f)

set_option maxHeartbeats 4000000 in
/-- The lone king keeps a move around a supported pawn, apart from the stalemate. -/
theorem key_reply {a b c d e f : Nat} (D : Dom a b c d e f) (hc : 1 ≤ c) (keep : ¬ Capture a b c d e f)
    (R : (Cl a c ∧ (b = d + 1 ∨ b = d + 2) ∧ d ≤ 5 ∧ ¬ Stale a c d e f) ∨ R6 a b c d) :
    ∃ x y, WeakStep a b c d e f x y := by
  by_cases top : f ≤ 6 ∨ d ≤ 4 ∨ c + 2 < e ∨ e + 2 < c
  · exact weak_reply D top keep
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  have k1 := D.k1
  unfold Stale Cl at R
  unfold R6 at R
  apply Classical.byContradiction
  intro no
  have t (x y : Nat) : ¬ WeakStep a b c d e f x y := fun s => no ⟨x, y, s⟩
  have h1 := t (e + 1) f
  have h2 := t (e - 1) f
  have h4 := t e (f - 1)
  have h5 := t (e + 1) (f - 1)
  have h6 := t (e - 1) (f - 1)
  unfold WeakStep Near Apart Att at h1 h2 h4 h5 h6
  have z : f = 7 := by omega
  subst z
  rcases R with ⟨⟨q1, q2⟩, q3, q4, q5⟩ | ⟨q1, q2, q3⟩ <;>
    rcases Nat.lt_trichotomy e c with g | g | g <;> omega

/-- A strong move inside the key-square strategy. -/
def KMove (j a b c d e f : Nat) : Prop :=
  StrongPush KW a b c d e f ∨ ∃ i, j = i + 1 ∧ ∃ x y, KingStep a b c d e f x y ∧ KW i x y c d e f

theorem go_push {j a b c d e f l : Nat} (fr : Free a b e f c (d + 1)) (lim : d + 1 ≤ 6) (hl : l ≤ 40)
    (w : KW l a b c (d + 1) e f) : KMove j a b c d e f := Or.inl (Or.inl ⟨fr, lim, l, hl, w⟩)

theorem go_king {j a b c d e f : Nat} (i x y : Nat) (hj : j = i + 1) (s : KingStep a b c d e f x y)
    (w : KW i x y c d e f) : KMove j a b c d e f := Or.inr ⟨i, hj, x, y, s, w⟩

macro "kstep" : tactic => `(tactic| (unfold KingStep Near Apart; omega))
macro "kfree" : tactic => `(tactic| (unfold Free; omega))
macro "kl2" : tactic => `(tactic| (refine ⟨by omega, by omega, Or.inl ⟨by unfold Cl; omega, by omega, by omega, by unfold Near; omega, by unfold Stale; omega, ?_⟩⟩; omega))
macro "kl1" : tactic => `(tactic| (refine ⟨by omega, by omega, Or.inr (Or.inl ⟨by unfold Cl; omega, by omega, by omega, by unfold Stale; omega, by unfold Near; omega, ?_⟩)⟩; unfold Lev Bud; omega))
macro "kl0" : tactic => `(tactic| (refine ⟨by omega, by omega, Or.inr (Or.inr (Or.inl ?_))⟩; unfold WL0 L0Lev Bud; omega))
macro "kl3" : tactic => `(tactic| (refine ⟨by omega, by omega, Or.inr (Or.inr (Or.inr (Or.inl ?_)))⟩; unfold WL3 Cl; omega))
macro "kz" : tactic => `(tactic| (refine ⟨by omega, by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))⟩; unfold WZ; omega))
macro "kb" : tactic => `(tactic| (refine ⟨by omega, by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_)))))⟩; unfold WB; omega))
macro "kr6" : tactic => `(tactic| (refine ⟨by omega, by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))⟩; unfold R6; omega))

set_option maxHeartbeats 4000000 in
theorem key_sl2 {j a b c d e f : Nat} (D : DomS a b c d e f) (hc : 2 ≤ c) (hj : j ≤ 9)
    (h : SL2 j a b c d e f) : KMove j a b c d e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  have k1 := D.1.k1
  have k3 := D.1.k3
  have k4 := D.k4
  unfold SL2 Cl Blk at h
  obtain ⟨⟨c1, c2⟩, rfl, d5, h⟩ := h
  by_cases low : d ≤ 2
  · by_cases q : (e = a ∧ f = d + 4) ∨ ¬ Near e f a (d + 4)
    · exact go_push (l := 9) (by kfree) (by omega) (by omega) (by unfold Near at q; kl1)
    unfold Near at q
    by_cases t1 : Apart a (d + 3) e f
    · exact go_king (j - 1) a (d + 3) (by omega) (by unfold Apart at t1; kstep) (by
        unfold Apart at t1; kl3)
    by_cases t2 : Apart c (d + 3) e f
    · exact go_king (j - 1) c (d + 3) (by omega) (by unfold Apart at t1 t2; kstep) (by
        unfold Apart at t1 t2; kl3)
    unfold Apart at t1 t2
    by_cases mid : a = c
    · subst mid
      by_cases t3 : Apart (a + 1) (d + 3) e f
      · exact go_king (j - 1) (a + 1) (d + 3) (by omega) (by unfold Apart at t3; kstep) (by
          unfold Apart at t3; kl3)
      · unfold Apart at t3
        exact go_king (j - 1) (a - 1) (d + 3) (by omega) (by kstep) (by kl3)
    · exact go_king (j - 1) c (d + 2) (by omega) (by kstep) (by kl2)
  · by_cases five : d = 5 ∧ a = c
    · obtain ⟨rfl, rfl⟩ := five
      by_cases t1 : Apart (a + 1) 6 e f
      · exact go_king (j - 1) (a + 1) 6 (by omega) (by unfold Apart at t1; kstep) (by
          unfold Apart at t1; kl1)
      · unfold Apart at t1
        exact go_king (j - 1) (a - 1) 6 (by omega) (by kstep) (by kl1)
    by_cases top : d = 5
    · exact go_push (l := 9) (by kfree) (by omega) (by omega) (by kr6)
    · exact go_push (l := 9) (by kfree) (by omega) (by omega) (by kl1)

set_option maxHeartbeats 4000000 in
theorem key_sl1 {j a b c d e f : Nat} (D : DomS a b c d e f) (hc : 2 ≤ c) (hj : j ≤ 9)
    (h : SL1 j a b c d e f) : KMove j a b c d e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  have k1 : Apart a b e f := D.1.k1
  unfold SL1 Cl at h
  obtain ⟨⟨c1, c2⟩, rfl, d5, nopp, lev⟩ := h
  have J5 : d = 5 → a = c → 1 ≤ j := by
    unfold Lev Bud at lev; intro _ _; omega
  have J4 : ¬ Near e f c d → ¬ (d = 4 ∧ e = a ∧ f = 7) → d ≠ 5 →
      (3 ≤ d ∧ 1 ≤ j) ∨ (d ≤ 2 ∧ 3 ≤ j) := by
    unfold Lev Bud at lev; intro _ _ _; omega
  have J3 : a = c → Near e f c d → d ≠ 5 → (3 ≤ d ∧ 3 ≤ j) ∨ (d ≤ 2 ∧ 5 ≤ j) := by
    intro m n q
    rcases lev with l | ⟨_, _, _, _, l⟩
    · unfold Lev Bud at l; omega
    · exact absurd n l
  have J2 : d = 4 → e = a → f = 7 → (e = c ∧ 3 ≤ j) ∨ e = c + 1 ∨ (e + 1 = c ∧ 4 ≤ j) := by
    unfold Lev Bud at lev; intro _ _ _; omega
  have J1 : a ≠ c → e = c → f = d + 3 → d ≠ 5 → (3 ≤ d ∧ 2 ≤ j) ∨ (d ≤ 2 ∧ 4 ≤ j) := by
    unfold Lev Bud at lev; intro _ _ _ _; omega
  clear lev
  by_cases five : d = 5
  · subst five
    by_cases mid : a = c
    · subst mid
      have J := J5 rfl rfl
      by_cases t1 : Apart (a + 1) 6 e f
      · exact go_king (j - 1) (a + 1) 6 (by omega) (by unfold Apart at t1; kstep) (by
          unfold Apart at t1 k1; kl1)
      · unfold Apart at t1 k1
        exact go_king (j - 1) (a - 1) 6 (by omega) (by kstep) (by kl1)
    · exact go_push (l := 9) (by unfold Apart at k1; kfree) (by omega) (by omega) (by kr6)
  by_cases np : Near e f c d
  · by_cases mid : a = c
    · subst mid
      have J := J3 rfl np five
      unfold Near at np
      unfold Apart at k1
      exact go_king (j - 1) (a + 1) (d + 1) (by omega) (by kstep) (by kl1)
    · unfold Near at np
      unfold Apart at k1
      have k4 := D.k4
      exact go_push (l := 9) (by kfree) (by omega) (by omega) (by kl0)
  by_cases zug : d = 4 ∧ e = a ∧ f = 7
  · obtain ⟨rfl, rfl, rfl⟩ := zug
    have J := J2 rfl rfl rfl
    by_cases right : e = c + 1
    · exact go_push (l := 9) (by kfree) (by omega) (by omega) (by kz)
    · clear J1 J2 J3 J4 J5 nopp
      rcases J with ⟨rfl, J⟩ | J0 | ⟨J0, J⟩
      · exact go_king (j - 1) (e + 1) 5 (by omega) (by unfold Apart at k1; kstep) (by kl1)
      · omega
      · exact go_king (j - 1) c 5 (by omega) (by unfold Apart at k1; kstep) (by kl1)
  have J := J4 np zug five
  by_cases blocked : e = c ∧ f = d + 3 ∧ a ≠ c
  · obtain ⟨rfl, rfl, mid⟩ := blocked
    have J6 := J1 mid rfl rfl five
    clear J1 J2 J3 J4 J5 J zug nopp np
    unfold Apart at k1
    exact go_king (j - 1) e (d + 1) (by omega) (by kstep) (by kl1)
  have far : (3 ≤ d ∧ 1 ≤ j) ∨ (d ≤ 2 ∧ 3 ≤ j) := J
  clear J J1 J2 J3 J4 J5
  have good : ∃ t, Cl t c ∧ Near a (d + 1) t (d + 2) ∧ t ≤ 7 ∧ Apart t (d + 2) e f := by
    by_cases t1 : Apart a (d + 2) e f
    · exact ⟨a, by unfold Cl; omega, by unfold Near; omega, by omega, t1⟩
    by_cases t2 : Apart c (d + 2) e f
    · refine ⟨c, by unfold Cl; omega, by unfold Near; omega, by omega, t2⟩
    by_cases mid : a = c
    · subst mid
      by_cases t3 : Apart (a + 1) (d + 2) e f
      · exact ⟨a + 1, by unfold Cl; omega, by unfold Near; omega, by omega, t3⟩
      · unfold Apart at t1 t3 k1
        refine ⟨a - 1, by unfold Cl; omega, by unfold Near; omega, by omega, ?_⟩
        unfold Apart
        omega
    · unfold Apart at t1 t2 k1
      omega
  obtain ⟨t, g1, g2, g3, g4⟩ := good
  clear zug nopp
  have ns : ¬ Stale t c d e f := by unfold Stale; omega
  refine go_king (j - 1) t (d + 2) (by omega) ⟨g2, g3, by omega, by omega, g4⟩ ⟨hc, by omega, Or.inl ⟨g1, rfl, by omega, np, ns, ?_⟩⟩
  rcases far with ⟨f1, f2⟩ | ⟨f1, f2⟩
  · exact Or.inl ⟨f1, by omega⟩
  · exact Or.inr (Or.inr (Or.inl ⟨f1, by omega⟩))

set_option maxHeartbeats 4000000 in
theorem key_sl0 {j a b c d e f : Nat} (D : DomS a b c d e f) (hc : 2 ≤ c) (hj : j ≤ 9)
    (h : SL0 j a b c d f) : KMove j a b c d e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  have k1 := D.1.k1
  have k2 := D.1.k2
  have k3 := D.1.k3
  have k4 := D.k4
  unfold SL0 L0Lev Bud at h
  obtain ⟨lev, rfl, d5, low⟩ := h
  exact go_king (j - 1) a (b + 1) (by omega) (by kstep) (by kl1)

theorem key_sl3 {j a b c d e f : Nat} (D : DomS a b c d e f) (hc : 2 ≤ c)
    (h : SL3 a b c d f) : KMove j a b c d e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  have k1 := D.1.k1
  unfold SL3 Cl at h
  exact go_push (l := 9) (by kfree) (by omega) (by omega) (by kl2)

/-- A rook next to the supporting king gives check or leaves a step away from it. -/
theorem r6_good {a b c d e f : Nat} (D : DomS a b c d e f) (h : R6 a b c d) :
    RookGood a b c e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  have k1 := D.1.k1
  unfold R6 at h
  have safe : PieceSafe a b c e f := by
    unfold PieceSafe Capture Near
    omega
  refine ⟨safe, ?_⟩
  by_cases rank : RankCheck a b c e f
  · exact Or.inl rank
  by_cases file : FileCheck a b c e f
  · exact Or.inr (Or.inl file)
  refine Or.inr (Or.inr ?_)
  unfold RankCheck at rank
  unfold FileCheck at file
  by_cases low : f = 0
  · refine ⟨e, 1, ?_, by omega, by omega, by omega, ?_, Or.inl ?_⟩
    · unfold Near; omega
    · unfold Apart; omega
    · unfold OffRook; omega
  · refine ⟨e, f - 1, ?_, by omega, by omega, by omega, ?_, Or.inl ?_⟩
    · unfold Near; omega
    · unfold Apart; omega
    · unfold OffRook; omega

set_option maxHeartbeats 4000000 in
theorem key_tops {j a b c d e f : Nat} (D : DomS a b c d e f) (hc : 2 ≤ c) (hj : j ≤ 9)
    (h : R6 a b c d ∨ SZ a b c d e f ∨ SB j a b c d e f) : KMove j a b c d e f := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  have k1 := D.1.k1
  have k3 := D.1.k3
  have k4 := D.k4
  rcases h with h | h | h
  · have good := r6_good D h
    unfold R6 at h
    exact Or.inl (Or.inr (Or.inr (Or.inr ⟨by omega, by kfree, good⟩)))
  · unfold SZ at h
    exact go_push (l := 9) (by kfree) (by omega) (by omega) (by kb)
  · unfold SB at h
    obtain ⟨rfl, rfl, rfl, h⟩ := h
    rcases h with ⟨q1, q2, q3⟩ | ⟨q1, q2⟩
    · exact go_king (j - 1) (c + 1) 6 (by omega) (by kstep) (by kr6)
    · refine Or.inl (Or.inr (Or.inr (Or.inr ⟨rfl, by kfree, ?_⟩)))
      exact run_rook u1 u2 u3 u6 u7 k1 (by unfold Outside; omega) (by omega)

/-- Every reply of the lone king stays inside the key-square strategy. -/
theorem key_weak {j a b c d e f : Nat} (D : Dom a b c d e f) (h : KW j a b c d e f) :
    ¬ Capture a b c d e f ∧ (∃ x y, WeakStep a b c d e f x y) ∧
      ∀ x y, WeakStep a b c d e f x y → ∃ i, i ≤ j ∧ KS i a b c d x y := by
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := D.bounds
  have k2 := D.k2
  have k3 := D.k3
  obtain ⟨hc, hj, h⟩ := h
  have ns : ¬ Stale a c d e f := by unfold Stale; omega
  rcases h with h | h | h | h | h | h | h
  · unfold WL2 Cl at h
    obtain ⟨⟨c1, c2⟩, rfl, d5, np, st, ph⟩ := h
    have keep : ¬ Capture a (d + 2) c d e f := fun q => np q.1
    refine ⟨keep, key_reply D (by omega) keep (Or.inl ⟨by unfold Cl; omega, by omega, d5, ns⟩), ?_⟩
    intro x y step
    obtain ⟨n, n5, n6⟩ := WeakStep.bounds step
    refine ⟨j, Nat.le_refl j, hc, hj, Or.inl ⟨by unfold Cl; omega, rfl, d5, ?_⟩⟩
    unfold Blk
    omega
  · unfold WL1 Cl at h
    obtain ⟨⟨c1, c2⟩, rfl, d5, st, op, lev⟩ := h
    have keep : ¬ Capture a (d + 1) c d e f := by
      unfold Capture Near; omega
    refine ⟨keep, key_reply D (by omega) keep (Or.inl ⟨by unfold Cl; omega, by omega, d5, ns⟩), ?_⟩
    intro x y step
    obtain ⟨⟨n1, n2, n3, n4⟩, n5, n6⟩ := WeakStep.bounds step
    have n7 := step.k5
    refine ⟨j, Nat.le_refl j, hc, hj, Or.inr (Or.inl ⟨by unfold Cl; omega, rfl, d5, ?_, ?_⟩)⟩
    · unfold Near at op
      omega
    · rcases lev with l | ⟨q1, q2, q3, q4, q5⟩
      · exact Or.inl l
      · refine Or.inr ⟨q1, q2, q5, ?_, ?_⟩
        · omega
        · unfold Near; omega
  · unfold WL0 L0Lev at h
    obtain ⟨lev, rfl, d5, low⟩ := h
    have keep : ¬ Capture a b c b e f := by
      unfold Capture Near; omega
    refine ⟨keep, weak_reply D (by omega) keep, ?_⟩
    intro x y step
    obtain ⟨⟨n1, n2, n3, n4⟩, n5, n6⟩ := WeakStep.bounds step
    exact ⟨j, Nat.le_refl j, hc, hj, Or.inr (Or.inr (Or.inl ⟨lev, rfl, d5, by omega⟩))⟩
  · unfold WL3 Cl at h
    obtain ⟨⟨c1, c2⟩, rfl, d5, low⟩ := h
    have keep : ¬ Capture a (d + 3) c d e f := by
      unfold Capture Near; omega
    refine ⟨keep, weak_reply D (by omega) keep, ?_⟩
    intro x y step
    obtain ⟨⟨n1, n2, n3, n4⟩, n5, n6⟩ := WeakStep.bounds step
    exact ⟨j, Nat.le_refl j, hc, hj, Or.inr (Or.inr (Or.inr (Or.inl
      ⟨by unfold Cl; omega, rfl, d5, by omega⟩)))⟩
  · have h' := h
    unfold R6 at h
    have keep : ¬ Capture a b c d e f := by
      unfold Capture Near; omega
    refine ⟨keep, key_reply D (by omega) keep (Or.inr h'), ?_⟩
    intro x y step
    exact ⟨j, Nat.le_refl j, hc, hj, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h'))))⟩
  · unfold WZ at h
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
    have keep : ¬ Capture (c + 1) 5 c 5 (c + 1) 7 := by
      unfold Capture Near; omega
    refine ⟨keep, ⟨c, 7, by unfold WeakStep Near Apart Att; omega⟩, ?_⟩
    intro x y step
    obtain ⟨⟨n1, n2, n3, n4⟩, n5, n6⟩ := WeakStep.bounds step
    have n7 := step.k5
    have n8 := step.k7
    have n9 := step.k8
    have n0 := step.k6
    exact ⟨j, Nat.le_refl j, hc, hj, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by
      unfold SZ; omega))))))⟩
  · unfold WB at h
    obtain ⟨rfl, rfl, rfl, rfl, side, one⟩ := h
    have keep : ¬ Capture (c + 1) 5 c 6 e 7 := by
      unfold Capture Near; omega
    have reply : ∃ x y, WeakStep (c + 1) 5 c 6 e 7 x y := by
      rcases side with rfl | rfl
      · exact ⟨e - 1, 6, by unfold WeakStep Near Apart Att; omega⟩
      · exact ⟨c + 3, 7, by unfold WeakStep Near Apart Att; omega⟩
    refine ⟨keep, reply, ?_⟩
    intro x y step
    obtain ⟨⟨n1, n2, n3, n4⟩, n5, n6⟩ := WeakStep.bounds step
    have n7 := step.k5
    have n8 := step.k7
    have n9 := step.k8
    have n0 := step.k6
    refine ⟨j, Nat.le_refl j, hc, hj, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_)))))⟩
    unfold SB
    omega

/-- The key-square strategy of a bishop or centre pawn. -/
def keyPlan : Plan where
  S := KS
  W := KW
  S_le := by
    intro j a b c d e f h
    have := h.2.1
    omega
  W_le := by
    intro j a b c d e f h
    have := h.2.1
    omega
  strong := by
    intro j a b c d e f D h
    obtain ⟨hc, hj, h⟩ := h
    rcases h with h | h | h | h | h
    · exact key_sl2 D hc hj h
    · exact key_sl1 D hc hj h
    · exact key_sl0 D hc hj h
    · exact key_sl3 D hc h
    · exact key_tops D hc hj h
  weak := key_weak

/-- A key square of a pawn on its bishop or central files: with the pawn owner to move
the king may stand two ranks ahead on the pawn's file or an adjacent one. -/
theorem fresh_key_strong {σ : Colour} {q : Position} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk) (turn : q.turn = σ)
    (safe : ¬ PawnSees σ ps wk) (file : 2 ≤ mx ps ps) (hd : height σ ps ≤ 5)
    (side : Cl (mx ps sk) (mx ps ps)) (ahead : height σ sk = height σ ps + 2) :
    FreshGame.Within σ 604 (FreshGame.fresh q) :=
  fresh_plan_strong (P := keyPlan) (j := 2) h fresh turn safe
    ⟨file, by omega, Or.inl ⟨side, ahead, hd, by unfold Blk; omega⟩⟩

/-- A key square with the lone king to move and the pawn out of its reach. -/
theorem fresh_key_weak {σ : Colour} {q : Position} {sk ps wk : Square}
    (h : IsKPK q σ sk ps wk) (fresh : FreshLegal q sk ps wk) (turn : q.turn = σ.opp)
    (file : 2 ≤ mx ps ps) (hd : height σ ps ≤ 5) (side : Cl (mx ps sk) (mx ps ps))
    (ahead : height σ sk = height σ ps + 2)
    (far : ¬ Near (mx ps wk) (height σ wk) (mx ps ps) (height σ ps)) :
    FreshGame.Within σ 604 (FreshGame.fresh q) :=
  fresh_plan_weak (P := keyPlan) (j := 2) h fresh turn
    ⟨file, by omega, Or.inl ⟨side, ahead, hd, far, by unfold Stale; omega, by omega⟩⟩

end EndgameChess.Rules.KPK.Coord
