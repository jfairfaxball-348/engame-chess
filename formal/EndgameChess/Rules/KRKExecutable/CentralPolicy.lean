import EndgameChess.Rules.KRKExecutable.LowerRouting

/-! The actual uncut tagged central policy. Every action names a concrete
source coordinate; all legal defender replies occur in the derivation.
No outcome-existence witness is used as a move-selection certificate. -/
namespace EndgameChess.Rules.KRKExecutable
open EndgameChess.KK EndgameChess.Rules EndgameChess.Rules.KRKCentral
set_option maxHeartbeats 4000000

inductive CentralStage where
  | central | lower (direction : Bool) | exit | restore | centre
  deriving DecidableEq

theorem policy_backFile (d : Bool) (k : Fin 8) (rs : Square) :
    pursuitFile d (backRook d k rs)=k.val := by
  cases d <;> simp [backRook,backFile,pursuitFile] <;> omega

def afterCatchUp (su : Square) : CentralStage :=
  if su.1.val=3 ∨ su.1.val=4 then .central else .centre

/-- A typed source action. Constructor premises are the actual dispatch
guards; target coordinates and successor control tags are fixed. -/
inductive CentralChoice (σ : Colour) :
    CentralStage → Position → CentralStage → Position → Prop
  | chase (d : Bool) {q c sk rs wk}
      (hq : Matches q σ ⟨sk,rs,wk,true⟩)
      (hb : sk.2.val+1=rs.2.val) (hw : wk.2.val=rs.2.val+1)
      (hs : 3≤pursuitFile d sk)
      (hx : pursuitFile d sk+2≤pursuitFile d wk)
      (hf : 3≤absDiff rs.1.val wk.1.val)
      (hm : Matches c σ ⟨lowerPursuitDestination d sk
        (by have h := pursuitFile_bound d wk; omega),rs,wk,false⟩) :
      CentralChoice σ (.lower d) q (.lower d) c
  | wait (d : Bool) {q c sk rs wk}
      (hq : Matches q σ ⟨sk,rs,wk,true⟩)
      (hb : sk.2.val+1=rs.2.val) (hw : wk.2.val=rs.2.val+1)
      (hs : 3≤pursuitFile d sk) (hx : pursuitFile d sk<pursuitFile d wk)
      (hwait : ¬ (pursuitFile d sk+2≤pursuitFile d wk ∧
        3≤absDiff rs.1.val wk.1.val))
      (hm : Matches c σ ⟨sk,centralBackDestination d rs,wk,false⟩) :
      CentralChoice σ (.lower d) q (.lower d) c
  | alignedRescue {q c sk rs wk}
      (hq : Matches q σ ⟨sk,rs,wk,true⟩)
      (hb : sk.2.val+1=rs.2.val) (hw : rs.2.val<wk.2.val)
      (hs : sk.1.val=3 ∨ sk.1.val=4) (ha : sk.1.val=wk.1.val)
      (hf : ¬ 2≤absDiff rs.1.val wk.1.val)
      (hm : Matches c σ ⟨sk,centralAlignedRescueDestination rs wk,wk,false⟩) :
      CentralChoice σ .central q .central c
  | upperRepair (d : Bool) {q c sk rs wk}
      (hq : Matches q σ ⟨sk,rs,wk,true⟩)
      (hb : sk.2.val+1=rs.2.val) (hw : rs.2.val+2≤wk.2.val)
      (hs : sk.1.val=3 ∨ sk.1.val=4)
      (hx : pursuitFile d sk<pursuitFile d wk)
      (hf : ¬ 2≤absDiff rs.1.val wk.1.val)
      (hm : Matches c σ ⟨sk,centralBackDestination d rs,wk,false⟩) :
      CentralChoice σ .central q .central c
  | upper {q c sk rs wk}
      (hq : Matches q σ ⟨sk,rs,wk,true⟩)
      (hb : sk.2.val+1=rs.2.val) (hw : rs.2.val+2≤wk.2.val)
      (hx : 1≤sk.1.val ∧ sk.1.val≤6)
      (hf : 2≤absDiff rs.1.val wk.1.val)
      (hm : Matches c σ ⟨sk,rankAdvanceDestination rs (by omega),wk,false⟩) :
      CentralChoice σ .exit q .restore c
  | check {q c sk rs wk}
      (hq : Matches q σ ⟨sk,rs,wk,true⟩)
      (hb : sk.2.val+1=rs.2.val) (hw : wk.2.val=rs.2.val+1)
      (ha : sk.1.val=wk.1.val) (hx : 1≤sk.1.val ∧ sk.1.val≤6)
      (hf : 2≤absDiff rs.1.val wk.1.val)
      (hm : Matches c σ ⟨sk,alignedReadyDestination rs wk,wk,false⟩) :
      CentralChoice σ .exit q .restore c
  | far {q c sk rs wk}
      (hq : Matches q σ ⟨sk,rs,wk,true⟩)
      (hb : sk.2.val+2=rs.2.val) (hw : rs.2.val<wk.2.val)
      (hx : 1≤sk.1.val ∧ sk.1.val≤6)
      (hf : ¬ 3≤absDiff rs.1.val wk.1.val)
      (hm : Matches c σ ⟨sk,restorationFarDestination rs wk,wk,false⟩) :
      CentralChoice σ .restore q .restore c
  | catchUp {q c sk rs wk}
      (hq : Matches q σ ⟨sk,rs,wk,true⟩)
      (hb : sk.2.val+2=rs.2.val) (hw : rs.2.val<wk.2.val)
      (hx : 1≤sk.1.val ∧ sk.1.val≤6)
      (hf : 3≤absDiff rs.1.val wk.1.val)
      (hm : Matches c σ ⟨restorationKingDestination sk (by omega) hx,rs,wk,false⟩) :
      CentralChoice σ .restore q
        (afterCatchUp (restorationKingDestination sk (by omega) hx)) c
  | centre {q c sk rs wk}
      (hq : Matches q σ ⟨sk,rs,wk,true⟩)
      (hb : sk.2.val+1=rs.2.val) (hw : rs.2.val<wk.2.val)
      (hx : sk.1.val=2 ∨ sk.1.val=5)
      (hf : 2≤absDiff rs.1.val wk.1.val)
      (hm : Matches c σ ⟨restorationCentreDestination sk,rs,wk,false⟩) :
      CentralChoice σ .centre q .central c

theorem centralChoice_turns {σ s q t c} (h : CentralChoice σ s q t c) :
    q.turn=σ ∧ c.turn=σ.opp := by
  cases h with
  | chase d hq hb hw hs hx hf hm => exact ⟨hq.2,hm.2⟩
  | wait d hq hb hw hs hx hf hm => exact ⟨hq.2,hm.2⟩
  | alignedRescue hq hb hw hs ha hf hm => exact ⟨hq.2,hm.2⟩
  | upperRepair d hq hb hw hs hx hf hm => exact ⟨hq.2,hm.2⟩
  | upper hq hb hw hx hf hm => exact ⟨hq.2,hm.2⟩
  | check hq hb hw ha hx hf hm => exact ⟨hq.2,hm.2⟩
  | far hq hb hw hx hf hm => exact ⟨hq.2,hm.2⟩
  | catchUp hq hb hw hx hf hm => exact ⟨hq.2,hm.2⟩
  | centre hq hb hw hx hf hm => exact ⟨hq.2,hm.2⟩

/-- Zero-ply control dispatch, never an extra chess move. -/
inductive CentralRoute (σ : Colour) : CentralStage → Position → CentralStage → Prop
  | fullExit {q sk rs wk}
      (hq : Matches q σ ⟨sk,rs,wk,true⟩)
      (hs : sk.1.val=3 ∨ sk.1.val=4) (he : Exit σ rs.2.val q) :
      CentralRoute σ .central q .exit
  | fullLower (d : Bool) {q sk rs wk}
      (hq : Matches q σ ⟨sk,rs,wk,true⟩)
      (hb : sk.2.val+1=rs.2.val) (hw : wk.2.val=rs.2.val+1)
      (hs : sk.1.val=3 ∨ sk.1.val=4)
      (hx : pursuitFile d sk<pursuitFile d wk) :
      CentralRoute σ .central q (.lower d)
  | lowerExit (d : Bool) {q y} (he : Exit σ y q) :
      CentralRoute σ (.lower d) q .exit

/-- Universal finite play tree for the selected tagged source coordinates.
The bound counts actual chess plies, including defending plies. -/
inductive CentralRun (σ : Colour) : CentralStage → Position → Nat → Prop
  | mate {s q t c} : CentralChoice σ s q t c → Legal q c → MateGoal σ c →
      CentralRun σ s q 1
  | pair {s q t c n} : CentralChoice σ s q t c → Legal q c →
      (∃ v, Legal c v) → (∀ v, Legal c v → CentralRun σ t v n) →
      CentralRun σ s q (n+2)
  | route {s q t n} : CentralRoute σ s q t → CentralRun σ t q n → CentralRun σ s q n
  | mono {s q n m} : CentralRun σ s q n → n≤m → CentralRun σ s q m

theorem centralRun_mateWithin {σ s q n} (h : CentralRun σ s q n) :
    MateWithin σ n q := by
  induction h with
  | mate chosen hl goal =>
    exact mateWithin_choose (centralChoice_turns chosen).1 hl goal
  | pair chosen hl hne _ ih =>
    exact mateWithin_pair (centralChoice_turns chosen).1 hl
      (centralChoice_turns chosen).2 hne ih
  | route _ _ ih => exact ih
  | mono _ hn ih => exact mateWithin_mono ih hn

def PolicyExitBound (σ : Colour) (y E : Nat) : Prop :=
  ∀ q, Exit σ y q → CentralRun σ .exit q E

def PolicyCentralBound (σ : Colour) (y C : Nat) : Prop :=
  ∀ {q sk rs wk}, Matches q σ ⟨sk,rs,wk,true⟩ → sk.2.val+1=y →
    rs.2.val=y → y<wk.2.val → (sk.1.val=3 ∨ sk.1.val=4) →
    CentralRun σ .central q C

theorem policy_lower_bind (d : Bool) {σ : Colour} {y E : Nat}
    (hexit : PolicyExitBound σ y E) {q sk rs wk}
    (hq : Matches q σ ⟨sk,rs,wk,true⟩)
    (hb : sk.2.val+1=rs.2.val) (hry : rs.2.val=y)
    (hw : wk.2.val=rs.2.val+1)
    (hs : 3≤pursuitFile d sk) (hx : pursuitFile d sk<pursuitFile d wk) :
    CentralRun σ (.lower d) q (E+2*lowerRoutingRank d sk rs wk) := by
  suffices main : ∀ n, ∀ {q sk rs wk}, Matches q σ ⟨sk,rs,wk,true⟩ →
      sk.2.val+1=rs.2.val → rs.2.val=y → wk.2.val=rs.2.val+1 →
      3≤pursuitFile d sk → pursuitFile d sk<pursuitFile d wk →
      lowerRoutingRank d sk rs wk≤n → CentralRun σ (.lower d) q (E+2*n) by
    exact main _ hq hb hry hw hs hx (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
    intro q sk rs wk hq hb hry hw hs hx hn
    have h7 := pursuitFile_bound d wk
    unfold lowerRoutingRank lowerRoutingDebt at hn
    split at hn <;> (try split at hn) <;> omega
  | succ n ih =>
    intro q sk rs wk hq hb hry hw hs hx hn
    by_cases hc : pursuitFile d sk+2≤pursuitFile d wk ∧
        3≤absDiff rs.1.val wk.1.val
    · obtain ⟨c,hl,hm,hne,hall⟩ := lowerChaseRouting_sound d hq hb hw hs hc.1 hc.2
      apply CentralRun.mono (n := E+2*n+2) ?_ (by omega)
      refine CentralRun.pair (.chase d hq hb hw hs hc.1 hc.2 hm) hl hne ?_
      intro v hv
      obtain ⟨t,hmt,he | ⟨hbu,hty,hsu,hlt,hdrop⟩⟩ := hall v hv
      · exact CentralRun.mono (CentralRun.route (.lowerExit d he) (hexit v (by simpa only [hry] using he))) (by omega)
      · exact ih hmt hbu hry hty hsu hlt (by omega)
    · obtain ⟨c,hl,hm,hne,hall⟩ := lowerWaitRouting_sound d hq hb hw hs hx hc
      apply CentralRun.mono (n := E+2*n+2) ?_ (by omega)
      refine CentralRun.pair (.wait d hq hb hw hs hx hc hm) hl hne ?_
      intro v hv
      obtain ⟨t,hmt,he | ⟨hty,hlt,hdrop⟩⟩ := hall v hv
      · exact CentralRun.mono (CentralRun.route (.lowerExit d he) (hexit v (by simpa only [hry] using he))) (by omega)
      · exact ih hmt hb hry hty hs hlt (by omega)

/-- The last alignment pair returns to a full central epoch. -/
theorem policy_centre_bind {σ : Colour} {y C : Nat}
    (hcentral : PolicyCentralBound σ y C) {q sk rs wk}
    (hq : Matches q σ ⟨sk,rs,wk,true⟩)
    (hb : sk.2.val+1=rs.2.val) (hry : rs.2.val=y)
    (hw : rs.2.val<wk.2.val) (hx : sk.1.val=2 ∨ sk.1.val=5)
    (hf : 2≤absDiff rs.1.val wk.1.val) :
    CentralRun σ .centre q (C+2) := by
  obtain ⟨c,hl,hm,hne,hall⟩ := restorationCentre_sound hq (by omega) hw hx hf
  refine CentralRun.pair (.centre hq hb hw hx hf hm) hl hne ?_
  intro v hv
  obtain ⟨t,hmt,hty,hcentre⟩ := hall v hv
  exact hcentral hmt (by change sk.2.val+1=y; omega) hry (by omega) hcentre

/-- The selected catch-up king pair, followed by centre alignment only
when the explicit destination lies on file 2 or 5. -/
theorem policy_catchUp_bind {σ : Colour} {y C : Nat}
    (hcentral : PolicyCentralBound σ y C) {q sk rs wk}
    (hq : Matches q σ ⟨sk,rs,wk,true⟩)
    (hb : sk.2.val+2=rs.2.val) (hry : rs.2.val=y)
    (hw : rs.2.val<wk.2.val) (hx : 1≤sk.1.val ∧ sk.1.val≤6)
    (hf : 3≤absDiff rs.1.val wk.1.val) :
    CentralRun σ .restore q (C+4) := by
  let su := restorationKingDestination sk (by omega) hx
  have hsuy : su.2.val=sk.2.val+1 := rfl
  obtain ⟨c,hl,hm,hne,hall⟩ := restorationKing_sound hq hb hw hx hf
  refine CentralRun.pair (.catchUp hq hb hw hx hf hm) hl hne ?_
  intro v hv
  obtain ⟨t,hmt,hty,hft,hs2,hs5⟩ := hall v hv
  change Matches v σ ⟨su,rs,t,true⟩ at hmt
  change 2≤su.1.val at hs2
  change su.1.val≤5 at hs5
  by_cases hc : su.1.val=3 ∨ su.1.val=4
  · have tag : afterCatchUp su=CentralStage.central := by simp [afterCatchUp,hc]
    change CentralRun σ (afterCatchUp su) v (C+2)
    rw [tag]
    exact .mono (hcentral hmt (by omega) hry (by omega) hc) (by omega)
  · have tag : afterCatchUp su=CentralStage.centre := by simp [afterCatchUp,hc]
    change CentralRun σ (afterCatchUp su) v (C+2)
    rw [tag]
    exact policy_centre_bind hcentral hmt (by omega) hry hty (by omega) hft

/-- At most one rescue and two king pairs after an actual rook lift. -/
theorem policy_restoration_bind {σ : Colour} {y C : Nat}
    (hcentral : PolicyCentralBound σ y C) {q sk rs wk}
    (hq : Matches q σ ⟨sk,rs,wk,true⟩)
    (hb : sk.2.val+2=rs.2.val) (hry : rs.2.val=y)
    (hw : rs.2.val<wk.2.val) (hx : 1≤sk.1.val ∧ sk.1.val≤6) :
    CentralRun σ .restore q (C+6) := by
  by_cases hf : 3≤absDiff rs.1.val wk.1.val
  · exact .mono (policy_catchUp_bind hcentral hq hb hry hw hx hf) (by omega)
  · obtain ⟨c,hl,hm,hne,hall⟩ := restorationFar_sound hq hb hw hf
    refine CentralRun.pair (.far hq hb hw hx hf hm) hl hne ?_
    intro v hv
    obtain ⟨t,hmt,hty,hft⟩ := hall v hv
    exact policy_catchUp_bind hcentral hmt hb hry hty hx hft

/-- An EXIT either immediately mates or advances the rook rank before
starting restoration. This budgets the actual selected tagged moves. -/
theorem policy_exit_bind {σ : Colour} {y C : Nat}
    (hcentral : PolicyCentralBound σ (y+1) C) :
    PolicyExitBound σ y (if y=6 then 1 else C+8) := by
  intro q he
  obtain ⟨sk,rs,wk,hq,hsy,hry,hwy,hs1,hs6,hf,hshape⟩ := he
  have upper (hup : y+2≤wk.2.val) :
      CentralRun σ .exit q (if y=6 then 1 else C+8) := by
    have hy : y≠6 := by omega
    rw [ite_eq_right hy]
    obtain ⟨c,hl,hm,hne,hall⟩ := offCentreUpper_sound hq (by omega) (by omega) ⟨hs1,hs6⟩ hf
    refine CentralRun.pair (.upper hq (by omega) (by omega) ⟨hs1,hs6⟩ hf hm) hl hne ?_
    intro v hv
    obtain ⟨t,hmt,hgap,hty,hx⟩ := hall v hv
    exact policy_restoration_bind hcentral hmt hgap (by
      change rs.2.val+1=y+1; omega) hty hx
  by_cases hup : y+2≤wk.2.val
  · exact upper hup
  have ha : sk.1.val=wk.1.val := by rcases hshape with hh | hh <;> omega
  have hb : wk.2.val=rs.2.val+1 := by omega
  obtain ⟨c,hl,hm,hgoal | ⟨hne,hall⟩⟩ := alignedReadyCheck_sound hq (by omega) hb ha hf
  · exact .mono (.mate (.check hq (by omega) hb ha ⟨hs1,hs6⟩ hf hm) hl hgoal) (by split <;> omega)
  · have hy : y≠6 := by
      obtain ⟨v,hv⟩ := hne
      obtain ⟨t,_,hty,_⟩ := hall v hv
      omega
    rw [ite_eq_right hy]
    refine CentralRun.pair (.check hq (by omega) hb ha ⟨hs1,hs6⟩ hf hm) hl hne ?_
    intro v hv
    obtain ⟨t,hmt,hty,_⟩ := hall v hv
    exact policy_restoration_bind hcentral hmt (by
      change sk.2.val+2=wk.2.val; omega) (by
      change wk.2.val=y+1; omega) (by change wk.2.val<t.2.val; omega) ⟨hs1,hs6⟩

/-- The single adjacent-offset wait has the sharper even-offset tail
needed after an aligned rescue. It is the SAME selected lower action. -/
theorem policy_adjacent_bind (d : Bool) {σ : Colour} {y E : Nat}
    (hexit : PolicyExitBound σ y E) {q sk rs wk}
    (hq : Matches q σ ⟨sk,rs,wk,true⟩)
    (hb : sk.2.val+1=rs.2.val) (hry : rs.2.val=y)
    (hw : wk.2.val=rs.2.val+1) (hs : 3≤pursuitFile d sk)
    (hx : pursuitFile d wk=pursuitFile d sk+1) :
    CentralRun σ (.lower d) q (E+2*(7-pursuitFile d sk)) := by
  let k : Fin 8 := if pursuitFile d rs=0 then 1 else 0
  let nr : Square := backRook d k rs
  have hnr : pursuitFile d nr=k.val := by
    exact policy_backFile d k rs
  have hk : k.val≤1 := by dsimp [k]; split <;> decide
  have hnry : nr.2=rs.2 := rfl
  have hdistinct : nr≠rs := by
    intro he
    have hsame : pursuitFile d nr=pursuitFile d rs := congrArg (pursuitFile d) he
    dsimp [k] at hnr
    split at hnr <;> simp only [Fin.val_zero,Fin.val_one] at hnr <;> omega
  have hf3 : 3≤absDiff nr.1.val wk.1.val := by
    rw [←pursuit_absDiff d nr wk]; simp only [absDiff]; omega
  have hs6 : pursuitFile d sk≤6 := by have h7 := pursuitFile_bound d wk; omega
  have phys : 1≤sk.1.val ∧ sk.1.val≤6 := by
    cases d <;> simp only [pursuitFile,Bool.false_eq_true,↓reduceIte] at * <;> omega
  have hwait : ¬ (pursuitFile d sk+2≤pursuitFile d wk ∧
      3≤absDiff rs.1.val wk.1.val) := by omega
  obtain ⟨c,hl,hm,hne,hall⟩ := krk_wall_rook_move hq (by omega) (by omega)
    (nr := nr) rfl hdistinct hf3
  apply CentralRun.mono (n := E+2*(6-pursuitFile d sk)+2) ?_ (by omega)
  refine CentralRun.pair (.wait d hq hb hw hs (by omega) hwait hm) hl hne ?_
  intro v hv
  obtain ⟨t,hmt,hty,hft,_,hshape⟩ := hall v hv
  have done (he : Exit σ y v) : CentralRun σ (.lower d) v (E+2*(6-pursuitFile d sk)) :=
    .mono (.route (.lowerExit d he) (hexit v he)) (by omega)
  rcases hshape hw with hu | ⟨htband,hdx⟩
  · exact done ⟨sk,nr,t,hmt,by omega,by exact hry,by omega,
      phys.1,phys.2,hft,Or.inl (by omega)⟩
  by_cases ha : sk.1.val=t.1.val
  · exact done ⟨sk,nr,t,hmt,by omega,by exact hry,by omega,
      phys.1,phys.2,hft,Or.inr ha⟩
  have hdx' : absDiff (pursuitFile d t) (pursuitFile d wk)=1 := by
    rw [pursuit_absDiff]; exact hdx
  have hnot : pursuitFile d sk≠pursuitFile d t := by
    intro he; apply ha
    cases d <;> simp only [pursuitFile,Bool.false_eq_true,↓reduceIte] at he <;> omega
  have hlt : pursuitFile d sk<pursuitFile d t := by simp only [absDiff] at hdx'; omega
  have heven : (pursuitFile d t-pursuitFile d sk)%2=0 := by
    simp only [absDiff] at hdx'; omega
  have hback : pursuitFile d nr≤1 := by omega
  have rank : lowerRoutingRank d sk nr t=6-pursuitFile d sk := by
    simp only [lowerRoutingRank,lowerRoutingDebt,ite_eq_left hback,ite_eq_left heven,Nat.add_zero]
  have run := policy_lower_bind d hexit hmt hb (by exact hry) htband hs hlt
  rw [rank] at run
  exact run

/-- A ready central state behind a back rook needs at most four pairs
before exit, including a possible parity-changing wait. -/
theorem policy_back_central_bind (d : Bool) {σ : Colour} {y E : Nat}
    (hexit : PolicyExitBound σ y E) {q sk rs wk}
    (hq : Matches q σ ⟨sk,rs,wk,true⟩)
    (hb : sk.2.val+1=rs.2.val) (hry : rs.2.val=y) (hw : rs.2.val<wk.2.val)
    (hs : sk.1.val=3 ∨ sk.1.val=4)
    (hstrong : 3≤pursuitFile d sk) (hstrong6 : pursuitFile d sk≤6)
    (hr : pursuitFile d rs≤1) (hx : pursuitFile d sk≤pursuitFile d wk)
    (hf : 2≤absDiff rs.1.val wk.1.val) :
    CentralRun σ .central q (E+2*(7-pursuitFile d sk)) := by
  have done (he : Exit σ y q) : CentralRun σ .central q (E+2*(7-pursuitFile d sk)) :=
    .mono (.route (.fullExit hq hs (by simpa only [hry] using he)) (hexit q he)) (by omega)
  by_cases hup : rs.2.val+2≤wk.2.val
  · exact done ⟨sk,rs,wk,hq,by omega,hry,by omega,by omega,by omega,hf,Or.inl (by omega)⟩
  by_cases ha : sk.1.val=wk.1.val
  · exact done ⟨sk,rs,wk,hq,by omega,hry,by omega,by omega,by omega,hf,Or.inr ha⟩
  have hnot : pursuitFile d sk≠pursuitFile d wk := by
    intro he; apply ha
    cases d <;> simp only [pursuitFile,Bool.false_eq_true,↓reduceIte] at he <;> omega
  have hlt : pursuitFile d sk<pursuitFile d wk := by omega
  have hband : wk.2.val=rs.2.val+1 := by omega
  have debt : lowerRoutingDebt d sk rs wk≤1 := by
    unfold lowerRoutingDebt
    rw [ite_eq_left hr]; split <;> omega
  have rank : lowerRoutingRank d sk rs wk≤7-pursuitFile d sk := by
    unfold lowerRoutingRank; omega
  exact .route (.fullLower d hq hb hband hs hlt)
    (.mono (policy_lower_bind d hexit hq hb hry hband hstrong hlt) (by omega))

/-- The ready full central domain routes to exactly the existing lower
pursuit or aligned/upper exit, with at most five complete pairs. -/
theorem policy_ready_central_bind {σ : Colour} {y E : Nat}
    (hexit : PolicyExitBound σ y E) {q sk rs wk}
    (hq : Matches q σ ⟨sk,rs,wk,true⟩)
    (hb : sk.2.val+1=rs.2.val) (hry : rs.2.val=y) (hw : rs.2.val<wk.2.val)
    (hs : sk.1.val=3 ∨ sk.1.val=4)
    (hf : 2≤absDiff rs.1.val wk.1.val) :
    CentralRun σ .central q (E+10) := by
  have done (he : Exit σ y q) : CentralRun σ .central q (E+10) :=
    .mono (.route (.fullExit hq hs (by simpa only [hry] using he)) (hexit q he)) (by omega)
  by_cases hup : rs.2.val+2≤wk.2.val
  · exact done ⟨sk,rs,wk,hq,by omega,hry,by omega,by omega,by omega,hf,Or.inl (by omega)⟩
  by_cases ha : sk.1.val=wk.1.val
  · exact done ⟨sk,rs,wk,hq,by omega,hry,by omega,by omega,by omega,hf,Or.inr ha⟩
  have hband : wk.2.val=rs.2.val+1 := by omega
  let d : Bool := if sk.1.val<wk.1.val then true else false
  have hstrong : 3≤pursuitFile d sk := by
    by_cases hr : sk.1.val<wk.1.val <;> simp [d,hr,pursuitFile] <;> omega
  have hlt : pursuitFile d sk<pursuitFile d wk := by
    by_cases hr : sk.1.val<wk.1.val <;> simp [d,hr,pursuitFile] <;> omega
  have rank : lowerRoutingRank d sk rs wk≤5 := by
    have debt := lowerRoutingDebt_bound d sk rs wk
    unfold lowerRoutingRank; omega
  exact .route (.fullLower d hq hb hband hs hlt)
    (.mono (policy_lower_bind d hexit hq hb hry hband hstrong hlt) (by omega))

/-- All full central roots, including aligned narrow-margin rescue, reach
an EXIT within ten actual plies under these exact tagged coordinates. -/
theorem policy_central_bind {σ : Colour} {y E : Nat}
    (hexit : PolicyExitBound σ y E) : PolicyCentralBound σ y (E+10) := by
  intro q sk rs wk hq hsy hry hwy hs
  have hb : sk.2.val+1=rs.2.val := by omega
  by_cases hf : 2≤absDiff rs.1.val wk.1.val
  · exact policy_ready_central_bind hexit hq hb hry (by omega) hs hf
  by_cases ha : sk.1.val=wk.1.val
  · let nr : Square := centralAlignedRescueDestination rs wk
    have hnry : nr.2=rs.2 := rfl
    have hfar : 4≤absDiff nr.1.val wk.1.val := wall_far_margin wk.1
    have hdistinct : nr≠rs := by
      intro he
      have hefile : nr.1.val=rs.1.val := congrArg (fun x : Square => x.1.val) he
      rw [hefile] at hfar; omega
    obtain ⟨c,hl,hm,hne,hall⟩ := krk_wall_rook_move hq (by omega) (by omega)
      (nr := nr) rfl hdistinct (by omega)
    refine CentralRun.pair (.alignedRescue hq hb (by omega) hs ha hf hm) hl hne ?_
    intro v hv
    obtain ⟨t,hmt,hty,hft,hunit,_⟩ := hall v hv
    have done (he : Exit σ y v) : CentralRun σ .central v (E+8) :=
      .mono (.route (.fullExit hmt hs (by change Exit σ rs.2.val v; simpa only [hry] using he)) (hexit v he)) (by omega)
    by_cases hup : y+2≤t.2.val
    · exact done ⟨sk,nr,t,hmt,hsy,by exact hry,by omega,by omega,by omega,hft,Or.inl hup⟩
    by_cases hal : sk.1.val=t.1.val
    · exact done ⟨sk,nr,t,hmt,hsy,by exact hry,by omega,by omega,by omega,hft,Or.inr hal⟩
    have hband : t.2.val=nr.2.val+1 := by omega
    let d : Bool := if sk.1.val<t.1.val then true else false
    have hstrong : 3≤pursuitFile d sk := by
      by_cases hr : sk.1.val<t.1.val <;> simp [d,hr,pursuitFile] <;> omega
    have hgap : pursuitFile d t=pursuitFile d sk+1 := by
      by_cases hr : sk.1.val<t.1.val <;> simp [d,hr,pursuitFile] <;>
        simp only [absDiff] at hunit <;> omega
    exact .route (.fullLower d hmt hb hband hs (by omega))
      (.mono (policy_adjacent_bind d hexit hmt hb (by exact hry) hband hstrong hgap) (by omega))
  let d : Bool := if sk.1.val<wk.1.val then true else false
  have hstrong : 3≤pursuitFile d sk := by
    by_cases hr : sk.1.val<wk.1.val <;> simp [d,hr,pursuitFile] <;> omega
  have hlt : pursuitFile d sk<pursuitFile d wk := by
    by_cases hr : sk.1.val<wk.1.val <;> simp [d,hr,pursuitFile] <;> omega
  have hstrong6 : pursuitFile d sk≤6 := by have h7 := pursuitFile_bound d wk; omega
  by_cases hup : rs.2.val+2≤wk.2.val
  · let k : Fin 8 := if pursuitFile d rs=0 then 1 else 0
    let nr : Square := backRook d k rs
    have hnr : pursuitFile d nr=k.val := by
      exact policy_backFile d k rs
    have hk : k.val≤1 := by dsimp [k]; split <;> decide
    have hdistinct : nr≠rs := by
      intro he
      have hsame : pursuitFile d nr=pursuitFile d rs := congrArg (pursuitFile d) he
      dsimp [k] at hnr
      split at hnr <;> simp only [Fin.val_zero,Fin.val_one] at hnr <;> omega
    have hf3 : 3≤absDiff nr.1.val wk.1.val := by
      rw [←pursuit_absDiff d nr wk]; simp only [absDiff]; omega
    obtain ⟨c,hl,hm,hne,hall⟩ := krk_wall_rook_move hq (by omega) (by omega)
      (nr := nr) rfl hdistinct hf3
    refine CentralRun.pair (.upperRepair d hq hb hup hs hlt hf hm) hl hne ?_
    intro v hv
    obtain ⟨t,hmt,hty,hft,hunit,_⟩ := hall v hv
    have hdx : absDiff (pursuitFile d t) (pursuitFile d wk)≤1 := by
      rw [pursuit_absDiff]; exact hunit
    have ht : pursuitFile d sk≤pursuitFile d t := by simp only [absDiff] at hdx; omega
    exact .mono (policy_back_central_bind d hexit hmt hb (by exact hry) hty hs
      hstrong hstrong6 (by omega) ht hft) (by omega)
  · have hband : wk.2.val=rs.2.val+1 := by omega
    have rank : lowerRoutingRank d sk rs wk≤5 := by
      have debt := lowerRoutingDebt_bound d sk rs wk
      unfold lowerRoutingRank; omega
    exact .route (.fullLower d hq hb hband hs hlt)
      (.mono (policy_lower_bind d hexit hq hb hry hband hstrong hlt) (by omega))

/-- Complete quantitative central-to-mate induction for the actual UNCUT
policy. This 18-per-height bound is deliberately not the tighter cut policy. -/
theorem policy_uncut_central_bound {σ : Colour} {y : Nat} :
    PolicyCentralBound σ y (18*((7-y)-1)+11) := by
  suffices main : ∀ n y, 7-y=n → PolicyCentralBound σ y (18*(n-1)+11) by
    intro q sk rs wk hq hsy hry hwy hs
    exact main (7-y) y rfl hq hsy hry hwy hs
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro y hn q sk rs wk hq hsy hry hwy hs
    have hy : y≤6 := by omega
    have hn1 : 1≤n := by omega
    have child : PolicyCentralBound σ (y+1) (18*(n-2)+11) := by
      intro p s r w hp hsp hrp hwp hsc
      have hn2 : 2≤n := by omega
      have run := ih (n-1) (by omega) (y+1) (by omega) hp hsp hrp hwp hsc
      have heq : n-1-1=n-2 := by omega
      simpa only [heq] using run
    have exit := policy_exit_bind child
    have run := policy_central_bind exit hq hsy hry hwy hs
    have bound : (if y=6 then 1 else 18*(n-2)+11+8)+10 ≤18*(n-1)+11 := by
      split <;> omega
    exact .mono run bound

theorem policy_uncut_central_mateWithin {σ : Colour} {q sk rs wk}
    (hq : Matches q σ ⟨sk,rs,wk,true⟩)
    (hb : sk.2.val+1=rs.2.val) (hw : rs.2.val<wk.2.val)
    (hs : sk.1.val=3 ∨ sk.1.val=4) :
    MateWithin σ (18*((7-rs.2.val)-1)+11) q :=
  centralRun_mateWithin (policy_uncut_central_bound hq hb rfl hw hs)

/-- A useful restricted bound for the actual selected uncut policy.
This is static play, not a history/claim certificate. -/
theorem policy_uncut_rankTwo_run {σ : Colour} {q sk rs wk}
    (hq : Matches q σ ⟨sk,rs,wk,true⟩)
    (hb : sk.2.val+1=rs.2.val) (hw : rs.2.val<wk.2.val)
    (hs : sk.1.val=3 ∨ sk.1.val=4) (hr : 2≤rs.2.val) :
    CentralRun σ .central q 83 := by
  exact .mono (policy_uncut_central_bound hq hb rfl hw hs) (by omega)

#print axioms policy_uncut_central_bound
#print axioms policy_uncut_central_mateWithin
#print axioms policy_uncut_rankTwo_run
end EndgameChess.Rules.KRKExecutable
