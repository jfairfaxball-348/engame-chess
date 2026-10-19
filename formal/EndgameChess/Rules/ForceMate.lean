import EndgameChess.Rules.ForcingDefinitions

/-! EC-C009: soundness, budget monotonicity, terminal inversion, dead-reply obstruction.
Paper proof: proofs/EC-C009_FORCING.md. -/
namespace EndgameChess.Rules
open EndgameChess.KK

private theorem prepend_reach {q r t : Position} (hl : Legal q r) (hr : ReachK r t) :
    ReachK q t := by
  induction hr with
  | refl => exact ReachK.tail (ReachK.refl _) hl
  | tail _ hs ih => exact ReachK.tail ih hs

theorem mateWithin_mono_step {σ : Colour} {n : Nat} {q : Position}
    (h : MateWithin σ n q) : MateWithin σ (n + 1) q := by
  induction n generalizing q with
  | zero => exact Or.inl h
  | succ n ih =>
    rcases h with hg | ⟨hd, hc | hf⟩
    · exact Or.inl hg
    · obtain ⟨ht, r, hl, hw⟩ := hc
      exact Or.inr ⟨hd, Or.inl ⟨ht, r, hl, ih hw⟩⟩
    · obtain ⟨ht, hn, hall⟩ := hf
      exact Or.inr ⟨hd, Or.inr ⟨ht, hn, fun r hr => ih (hall r hr)⟩⟩

theorem mateWithin_mono {σ : Colour} {n m : Nat} {q : Position}
    (h : MateWithin σ n q) (hle : n ≤ m) : MateWithin σ m q := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  clear hle
  induction k with
  | zero => simpa using h
  | succ k ih => exact mateWithin_mono_step ih

theorem mateWithin_sound {σ : Colour} {n : Nat} {q : Position}
    (h : MateWithin σ n q) : ∃ t, ReachK q t ∧ MateGoal σ t := by
  induction n generalizing q with
  | zero => exact ⟨q, ReachK.refl q, h⟩
  | succ n ih =>
    rcases h with hg | ⟨_, hc | hf⟩
    · exact ⟨q, ReachK.refl q, hg⟩
    · obtain ⟨_, r, hl, hw⟩ := hc
      obtain ⟨t, ht, hm⟩ := ih hw
      exact ⟨t, prepend_reach hl ht, hm⟩
    · obtain ⟨_, ⟨r, hl⟩, hall⟩ := hf
      obtain ⟨t, ht, hm⟩ := ih (hall r hl)
      exact ⟨t, prepend_reach hl ht, hm⟩

theorem forceMate_not_dead {σ : Colour} {q : Position} (h : ForceMate σ q) : ¬ DeadK q := by
  obtain ⟨n, hn⟩ := h
  obtain ⟨t, ht, _, hm⟩ := mateWithin_sound hn
  exact fun hd => hd ⟨t, ht, hm⟩

theorem forceMate_of_goal {σ : Colour} {q : Position} (h : MateGoal σ q) : ForceMate σ q :=
  ⟨0, h⟩

theorem forceMate_no_moves_iff {σ : Colour} {q : Position}
    (hn : ¬ ∃ r, Legal q r) : ForceMate σ q ↔ MateGoal σ q := by
  constructor
  · rintro ⟨n, h⟩
    cases n with
    | zero => exact h
    | succ n =>
      rcases h with hg | ⟨_, hc | hf⟩
      · exact hg
      · obtain ⟨_, r, hr, _⟩ := hc
        exact False.elim (hn ⟨r, hr⟩)
      · exact False.elim (hn hf.2.1)
  · exact forceMate_of_goal

theorem dead_reply_not_forceMate {σ : Colour} {q r : Position}
    (ht : q.turn = σ.opp) (hl : Legal q r) (hd : DeadK r) : ¬ ForceMate σ q := by
  rintro ⟨n, h⟩
  have ng : ¬ MateGoal σ q := fun hg => hg.2.2 ⟨r, hl⟩
  cases n with
  | zero => exact ng h
  | succ n =>
    rcases h with hg | ⟨_, hc | hf⟩
    · exact ng hg
    · exact opp_ne σ (hc.1.symm.trans ht)
    · exact forceMate_not_dead ⟨n, hf.2.2 r hl⟩ hd

theorem stalemate_not_forceMate {σ : Colour} {q : Position}
    (hc : inCheck q q.turn = false) (hn : ¬ ∃ r, Legal q r) : ¬ ForceMate σ q := by
  intro h
  have hg := (forceMate_no_moves_iff hn).1 h
  have hcheck := hg.2.1
  rw [hc] at hcheck
  cases hcheck

private theorem finite_reply_bound (σ : Colour) (xs : List Position)
    (hall : ∀ r ∈ xs, ForceMate σ r) : ∃ n, ∀ r ∈ xs, MateWithin σ n r := by
  induction xs with
  | nil => exact ⟨0, by simp⟩
  | cons a xs ih =>
    obtain ⟨n, hn⟩ := hall a (by simp)
    obtain ⟨m, hm⟩ := ih (fun r hr => hall r (by simp [hr]))
    refine ⟨n + m, fun r hr => ?_⟩
    simp only [List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact mateWithin_mono hn (by omega)
    · exact mateWithin_mono (hm r hr) (by omega)

/-- A single chosen forcing successor suffices at the named winner's turn. -/
theorem forceMate_choose {σ : Colour} {q r : Position} (ht : q.turn = σ)
    (hl : Legal q r) (hw : ForceMate σ r) : ForceMate σ q := by
  obtain ⟨n, hn⟩ := hw
  have hd : ¬ DeadK q := by
    obtain ⟨t, hrt, _, hm⟩ := mateWithin_sound hn
    exact fun h => h ⟨t, prepend_reach hl hrt, hm⟩
  exact ⟨n + 1, Or.inr ⟨hd, Or.inl ⟨ht, r, hl, hn⟩⟩⟩

/-- Kernel finite branching combines pointwise forcing bounds for all legal replies. -/
theorem forceMate_defend {σ : Colour} {q : Position} (ht : q.turn = σ.opp)
    (hne : ∃ r, Legal q r) (hall : ∀ r, Legal q r → ForceMate σ r) : ForceMate σ q := by
  obtain ⟨n, hn⟩ := finite_reply_bound σ (legalPositions q)
    (fun r hr => hall r (mem_legalPositions.1 hr))
  obtain ⟨r, hr⟩ := hne
  obtain ⟨k, hk⟩ := hall r hr
  have hd : ¬ DeadK q := by
    obtain ⟨t, hrt, _, hm⟩ := mateWithin_sound hk
    exact fun h => h ⟨t, prepend_reach hr hrt, hm⟩
  exact ⟨n + 1, Or.inr ⟨hd, Or.inr ⟨ht, ⟨r, hr⟩,
    fun s hs => hn s (mem_legalPositions.2 hs)⟩⟩⟩

end EndgameChess.Rules
