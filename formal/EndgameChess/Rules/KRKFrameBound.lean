import EndgameChess.Rules.KRKSixNear

namespace EndgameChess.Rules.KRKFrameBound
open EndgameChess.KK KRKNativeFrame
set_option maxHeartbeats 300000

private theorem safe_map (g : Frame) {sk rs wk : Square} (safe : SafeRook sk rs wk) :
    SafeRook (g.f sk) (g.f rs) (g.f wk) := by
  simpa only [SafeRook,g.distance] using safe

private theorem mapped_goal (g : Frame) {q t : Position} {σ : Colour}
    {a : KRKState} (hq : Matches q σ a) (ht : Matches t σ (g.mapState a))
    (goal : MateGoal σ q) : MateGoal σ t := by
  have weak : a.strong = false := by
    cases he : a.strong
    · rfl
    · have turn := hq.2
      rw [he] at turn
      simp only [ite_true] at turn
      exact False.elim (opp_ne σ (turn.symm.trans goal.1))
  have qt : q.turn = σ.opp := by simpa [weak] using hq.2
  have tt : t.turn = σ.opp := by simpa [Frame.mapState,weak] using ht.2
  have safe := krk_force_weak_safe hq.1 qt (forceMate_of_goal goal)
  have mappedSafe := safe_map g safe
  refine ⟨tt,?_,?_⟩
  · rw [tt]
    have check := goal.2.1
    rw [qt] at check
    have geometric := (inCheck_weak_krk hq.1.1 hq.1.2.1 hq.1.2.2.1 hq.1.2.2.2).1 check
    apply (inCheck_weak_krk ht.1.1 ht.1.2.1 ht.1.2.2.1 ht.1.2.2.2).2
    simpa only [Frame.mapState,g.distance,g.sees] using geometric
  · rintro ⟨r,edge⟩
    obtain ⟨w,_,step⟩ := krk_safe_reply ht.1 tt mappedSafe edge
    have back := g.inverse.map_step step
    have start : g.inverse.mapState ⟨(g.mapState a).sk,(g.mapState a).rs,(g.mapState a).wk,false⟩ = a := by
      cases a
      simp_all [Frame.mapState,Frame.inverse,g.left_inv]
    rw [start] at back
    obtain ⟨u,legal,_⟩ := step_sound hq back
    exact goal.2.2 ⟨u,legal⟩

/-- Geometric frame transport uses castling-free synthetic source boards.
No actual trace, clock, repetition key or rights are transformed. -/
theorem bound_transport (g : Frame) {q t : Position} {σ : Colour} {a : KRKState}
    (hq : Matches q σ a) (noCastle : q.castling = noRights)
    (ht : Matches t σ (g.mapState a)) {n : Nat} (win : MateWithin σ n q) : MateWithin σ n t := by
  induction n generalizing q t a with
  | zero => exact mapped_goal g hq ht win
  | succ n ih =>
    rcases win with goal | ⟨_,chosen | defended⟩
    · exact Or.inl (mapped_goal g hq ht goal)
    · obtain ⟨turn,r,edge,child⟩ := chosen
      have strong : a.strong = true := by
        cases he : a.strong
        · have qt := hq.2
          rw [he] at qt
          simp only [Bool.false_eq_true,ite_false] at qt
          exact False.elim (opp_ne σ (turn.symm.trans qt))
        · rfl
      obtain ⟨b,next,step⟩ := krk_strong_reply hq.1 turn noCastle edge
      have start : (⟨a.sk,a.rs,a.wk,true⟩ : KRKState) = a := by cases a; simp_all
      rw [start] at step
      obtain ⟨u,legal,mapped⟩ := step_sound ht (g.map_step step)
      apply mateWithin_choose (by simpa [Frame.mapState,strong] using ht.2) legal
      exact ih next (noRights_after_legal noCastle edge) mapped child
    · obtain ⟨turn,live,all⟩ := defended
      have weak : a.strong = false := by
        cases he : a.strong
        · rfl
        · have qt := hq.2
          rw [he] at qt
          simp only [ite_true] at qt
          exact False.elim (opp_ne σ (qt.symm.trans turn))
      have source : ForceMate σ q := ⟨n+1,Or.inr ⟨by omega,Or.inr ⟨turn,live,all⟩⟩⟩
      have safe := krk_force_weak_safe hq.1 turn source
      have mappedSafe := safe_map g safe
      have tt : t.turn = σ.opp := by simpa [Frame.mapState,weak] using ht.2
      obtain ⟨r,edge⟩ := live
      obtain ⟨w,_,step⟩ := krk_safe_reply hq.1 turn safe edge
      have start : (⟨a.sk,a.rs,a.wk,false⟩ : KRKState) = a := by cases a; simp_all
      rw [start] at step
      obtain ⟨u,legal,_⟩ := step_sound ht (g.map_step step)
      apply mateWithin_defend tt ⟨u,legal⟩
      intro u legal
      obtain ⟨w,mapped,step⟩ := krk_safe_reply ht.1 tt mappedSafe legal
      have back := g.inverse.map_step step
      have inverseStart : g.inverse.mapState ⟨(g.mapState a).sk,(g.mapState a).rs,(g.mapState a).wk,false⟩ = a := by
        cases a
        simp_all [Frame.mapState,Frame.inverse,g.left_inv]
      rw [inverseStart] at back
      obtain ⟨r,edge,next⟩ := step_sound hq back
      apply ih next (noRights_after_legal noCastle edge) ?_ (all r edge)
      simpa only [Frame.mapState,Frame.inverse,g.right_inv] using mapped

theorem five_map (g : Frame) {sk rs wk : Square}
    (distinct : sk ≠ rs) (notKing : sk ≠ wk) (notRook : rs ≠ wk)
    (far : 2 ≤ dInf sk wk) (notCheck : ¬RookSees rs wk sk wk)
    (clear : KRKFiveGeometry.Clear sk rs wk) : KRKFiveGeometry.Clear (g.f sk) (g.f rs) (g.f wk) := by
  let q := krkPos .white sk rs wk .white
  let r := krkPos .white (g.f sk) (g.f rs) (g.f wk) .white
  have material : IsKRK q .white sk rs wk := ⟨distinct,notKing,notRook,rfl⟩
  have mapped : IsKRK r .white (g.f sk) (g.f rs) (g.f wk) :=
    ⟨g.ne_iff.mpr distinct,g.ne_iff.mpr notKing,g.ne_iff.mpr notRook,rfl⟩
  have win := (KRKFiveGeometry.kernel_five_iff material rfl far notCheck).mpr clear
  have transported := bound_transport g
    (show Matches q .white ⟨sk,rs,wk,true⟩ from ⟨material,rfl⟩) rfl
    (show Matches r .white (g.mapState ⟨sk,rs,wk,true⟩) from ⟨mapped,rfl⟩) win
  exact (KRKFiveGeometry.kernel_five_iff mapped rfl (by rwa [g.distance])
    (fun seen => notCheck ((g.sees _ _ _ _).mp seen))).mp transported

theorem six_map (g : Frame) {sk rs wk : Square} (distinct : sk ≠ rs)
    (clear : KRKSixGeometry.Clear sk rs wk) : KRKSixGeometry.Clear (g.f sk) (g.f rs) (g.f wk) := by
  obtain ⟨safe,⟨t,guard⟩,all⟩ := clear
  have step : StepM ⟨sk,rs,wk,false⟩ ⟨sk,rs,t,true⟩ := StepM.lone guard.1 guard.2.1 guard.2.2.1 guard.2.2.2
  refine ⟨safe_map g safe,⟨g.f t,KRKCornerWeakBand.step_guard (g.map_step step)⟩,?_⟩
  intro u next
  have back := g.inverse.map_step (StepM.lone next.1 next.2.1 next.2.2.1 next.2.2.2)
  change StepM ⟨g.r (g.f sk),g.r (g.f rs),g.r (g.f wk),false⟩
    ⟨g.r (g.f sk),g.r (g.f rs),g.r u,true⟩ at back
  simp only [g.left_inv] at back
  have guardBack := KRKCornerWeakBand.step_guard back
  have far := guardBack.2.2.1
  have mapped := five_map g distinct (ne_of_dInf_pos (by omega)) guardBack.2.1.symm far guardBack.2.2.2
    (all _ guardBack)
  simpa only [g.right_inv] using mapped

end EndgameChess.Rules.KRKFrameBound
