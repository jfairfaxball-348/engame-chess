import EndgameChess.Rules.KRKBound.Budget

/-! EC-C040: same-budget alternating strategy transport, no source castling. -/
namespace EndgameChess.Rules
open EndgameChess.KK

private theorem safe_map (g : BoardSym) {sk rs wk : Square}
    (hs : SafeRook sk rs wk) : SafeRook (g.f sk) (g.f rs) (g.f wk) := by
  simpa only [SafeRook, g.dInf_eq] using hs

private theorem mapped_goal (g : BoardSym) {q t : Position} {σ : Colour}
    {a : KRKState} (hq : Matches q σ a) (ht : Matches t σ (a.map g))
    (hg : MateGoal σ q) : MateGoal σ t := by
  have ha : a.strong = false := by
    cases he : a.strong
    · rfl
    · have hh := hq.2
      rw [he] at hh
      simp only [ite_true] at hh
      exact False.elim (opp_ne σ (hh.symm.trans hg.1))
  have qt : q.turn = σ.opp := by simpa [ha] using hq.2
  have tt : t.turn = σ.opp := by simpa [KRKState.map, ha] using ht.2
  have hs := krk_force_weak_safe hq.1 qt (forceMate_of_goal hg)
  have hsm := safe_map g hs
  refine ⟨tt, ?_, ?_⟩
  · rw [tt]
    have hc := hg.2.1
    rw [qt] at hc
    have hc' := (inCheck_weak_krk hq.1.1 hq.1.2.1 hq.1.2.2.1 hq.1.2.2.2).1 hc
    apply (inCheck_weak_krk ht.1.1 ht.1.2.1 ht.1.2.2.1 ht.1.2.2.2).2
    simpa only [KRKState.map, g.dInf_eq, g.sees_iff] using hc'
  · rintro ⟨r, hr⟩
    obtain ⟨w, hm, hs'⟩ := krk_safe_reply ht.1 tt hsm hr
    have hsback := step_map g hs'
    have hstart : (⟨(a.map g).sk, (a.map g).rs, (a.map g).wk, false⟩ : KRKState).map g = a := by
      cases a; simp_all [KRKState.map, g.invol]
    rw [hstart] at hsback
    obtain ⟨u, hu, _⟩ := step_sound hq hsback
    exact hg.2.2 ⟨u, hu⟩

/-- Transport a castling-free source winning strategy to a reflected/transposed
exact KRK board with arbitrary flags. Preserves the stated budget; no optimality claim. -/
theorem krk_bound_transport (g : BoardSym) {q t : Position} {σ : Colour}
    {a : KRKState} (hq : Matches q σ a) (hn : q.castling = noRights)
    (ht : Matches t σ (a.map g)) {n : Nat} (hw : MateWithin σ n q) :
    MateWithin σ n t := by
  induction n generalizing q t a with
  | zero => exact mapped_goal g hq ht hw
  | succ n ih =>
    rcases hw with hg | ⟨hnd, hc | hd⟩
    · exact Or.inl (mapped_goal g hq ht hg)
    · obtain ⟨qt, r, hr, hwin⟩ := hc
      have ha : a.strong = true := by
        cases he : a.strong
        · have hh := hq.2
          rw [he] at hh
          simp only [Bool.false_eq_true, ite_false] at hh
          exact False.elim (opp_ne σ (qt.symm.trans hh))
        · rfl
      obtain ⟨b, hb, hs⟩ := krk_strong_reply hq.1 qt hn hr
      have hstart : (⟨a.sk, a.rs, a.wk, true⟩ : KRKState) = a := by
        cases a; simp_all
      rw [hstart] at hs
      obtain ⟨u, hu, hum⟩ := step_sound ht (step_map g hs)
      apply mateWithin_choose (by simpa [KRKState.map, ha] using ht.2) hu
      exact ih hb (noRights_after_legal hn hr) hum hwin
    · obtain ⟨qt, hne, hall⟩ := hd
      have ha : a.strong = false := by
        cases he : a.strong
        · rfl
        · have hh := hq.2
          rw [he] at hh
          simp only [ite_true] at hh
          exact False.elim (opp_ne σ (hh.symm.trans qt))
      have ha0 : a = ⟨a.sk, a.rs, a.wk, false⟩ := by cases a; simp_all
      have hsource : ForceMate σ q := ⟨n + 1, Or.inr ⟨hnd, Or.inr ⟨qt, hne, hall⟩⟩⟩
      have hs := krk_force_weak_safe hq.1 qt hsource
      have hsm := safe_map g hs
      have tt : t.turn = σ.opp := by simpa [KRKState.map, ha] using ht.2
      obtain ⟨r, hr⟩ := hne
      obtain ⟨w, hm, hs'⟩ := krk_safe_reply hq.1 qt hs hr
      rw [← ha0] at hs'
      obtain ⟨u, hu, _⟩ := step_sound ht (step_map g hs')
      apply mateWithin_defend tt ⟨u, hu⟩
      intro u hu
      obtain ⟨w, hum, hus⟩ := krk_safe_reply ht.1 tt hsm hu
      have hsback := step_map g hus
      have hstart : (⟨(a.map g).sk, (a.map g).rs, (a.map g).wk, false⟩ : KRKState).map g = a := by
        cases a; simp_all [KRKState.map, g.invol]
      rw [hstart] at hsback
      obtain ⟨r, hr, hrm⟩ := step_sound hq hsback
      apply ih hrm (noRights_after_legal hn hr) ?_ (hall r hr)
      simpa only [KRKState.map_map] using hum

end EndgameChess.Rules
