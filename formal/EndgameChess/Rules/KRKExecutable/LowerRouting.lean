import EndgameChess.Rules.KRKExecutable.CentralBackRook

/-! KRK09: retain the oriented lower phase instead of restoring its king.
The rank pays separately for a back-rook wait and for king-file progress.
This certifies lower-to-exit routing, not a global clock-safe mate policy. -/
namespace EndgameChess.Rules.KRKExecutable
open EndgameChess.KK EndgameChess.Rules EndgameChess.Rules.KRKCentral
set_option maxHeartbeats 4000000

def lowerRoutingDebt (d : Bool) (sk rs wk : Square) : Nat :=
  if pursuitFile d rs ≤ 1 then
    if (pursuitFile d wk - pursuitFile d sk) % 2 = 0 then 0 else 1
  else 2

def lowerRoutingRank (d : Bool) (sk rs wk : Square) : Nat :=
  6 - pursuitFile d sk + lowerRoutingDebt d sk rs wk

theorem lowerRoutingDebt_bound (d : Bool) (sk rs wk : Square) :
    lowerRoutingDebt d sk rs wk ≤ 2 := by
  unfold lowerRoutingDebt
  split <;> (try split) <;> omega

/-- A chase cannot be followed by recentring: every continuing lower child
keeps the same orientation and has a strictly smaller rank. -/
theorem lowerChaseRouting_sound (d : Bool) {q : Position} {σ : Colour}
    {sk rs wk : Square}
    (hq : Matches q σ ⟨sk,rs,wk,true⟩)
    (hb : sk.2.val+1=rs.2.val) (hw : wk.2.val=rs.2.val+1)
    (hs : 3≤pursuitFile d sk)
    (hx : pursuitFile d sk+2≤pursuitFile d wk)
    (hf : 3≤absDiff rs.1.val wk.1.val) :
    let su := lowerPursuitDestination d sk
      (by have h := pursuitFile_bound d wk; omega)
    ∃ c, Legal q c ∧ Matches c σ ⟨su,rs,wk,false⟩ ∧
      (∃ v, Legal c v) ∧ ∀ v, Legal c v →
        ∃ t, Matches v σ ⟨su,rs,t,true⟩ ∧
          (Exit σ rs.2.val v ∨
            (su.2.val+1=rs.2.val ∧ t.2.val=rs.2.val+1 ∧
             3≤pursuitFile d su ∧ pursuitFile d su<pursuitFile d t ∧
             lowerRoutingRank d su rs t < lowerRoutingRank d sk rs wk)) := by
  dsimp
  have bound : pursuitFile d sk+2≤7 := by
    have h := pursuitFile_bound d wk; omega
  let su := lowerPursuitDestination d sk bound
  have coords := lowerPursuitDestination_coords d sk bound
  have hsy : su.2=sk.2 := coords.1
  have hsx : pursuitFile d su=pursuitFile d sk+1 := coords.2
  have hs6 : pursuitFile d su≤6 := by
    have h := pursuitFile_bound d wk; omega
  have phys : 1≤su.1.val ∧ su.1.val≤6 := by
    cases d <;> simp only [pursuitFile,Bool.false_eq_true,↓reduceIte] at * <;> omega
  obtain ⟨ss,c,hssy,hssx,hl,hm,hne,hall⟩ :=
    krk_pursuit_king_move d hq hb hw hx hf
  have hss : ss=su := by
    apply Prod.ext
    · apply Fin.ext
      cases d <;> simp only [pursuitFile,Bool.false_eq_true,↓reduceIte] at hssx hsx <;> omega
    · exact hssy.trans hsy.symm
  subst ss
  refine ⟨c,hl,hm,hne,?_⟩
  intro v hv
  obtain ⟨t,hmt,hft,_,hshape⟩ := hall v hv
  refine ⟨t,hmt,?_⟩
  rcases hshape with hu | ⟨hty,hdx⟩
  · exact Or.inl ⟨su,rs,t,hmt,by omega,rfl,by omega,
      phys.1,phys.2,hft,Or.inl hu⟩
  by_cases hal : su.1.val=t.1.val
  · exact Or.inl ⟨su,rs,t,hmt,by omega,rfl,by omega,
      phys.1,phys.2,hft,Or.inr hal⟩
  have hdx' : absDiff (pursuitFile d t) (pursuitFile d wk)=1 := by
    rw [pursuit_absDiff]; exact hdx
  have hnot : pursuitFile d su≠pursuitFile d t := by
    intro he; apply hal
    cases d <;> simp only [pursuitFile,Bool.false_eq_true,↓reduceIte] at he <;> omega
  have hlt : pursuitFile d su<pursuitFile d t := by
    simp only [absDiff] at hdx'; omega
  right
  refine ⟨by omega,hty,by omega,hlt,?_⟩
  change lowerRoutingRank d su rs t < lowerRoutingRank d sk rs wk
  have hparity : (pursuitFile d t-pursuitFile d su)%2=
      (pursuitFile d wk-pursuitFile d sk)%2 := by
    simp only [absDiff] at hdx'; omega
  have hdebt : lowerRoutingDebt d su rs t=lowerRoutingDebt d sk rs wk := by
    unfold lowerRoutingDebt
    rw [hparity]
  unfold lowerRoutingRank
  rw [hdebt]
  omega

/-- A back-rook relocation is a tempo phase, never a king restoration.
If the rook was already behind the king, a required wait has offset one;
every continuing lower reply makes that offset even, paying off the debt. -/
theorem lowerWaitRouting_sound (d : Bool) {q : Position} {σ : Colour}
    {sk rs wk : Square}
    (hq : Matches q σ ⟨sk,rs,wk,true⟩)
    (hb : sk.2.val+1=rs.2.val) (hw : wk.2.val=rs.2.val+1)
    (hs : 3≤pursuitFile d sk)
    (hx : pursuitFile d sk<pursuitFile d wk)
    (hwait : ¬ (pursuitFile d sk+2≤pursuitFile d wk ∧
      3≤absDiff rs.1.val wk.1.val)) :
    let nr := centralBackDestination d rs
    ∃ c, Legal q c ∧ Matches c σ ⟨sk,nr,wk,false⟩ ∧
      (∃ v, Legal c v) ∧ ∀ v, Legal c v →
        ∃ t, Matches v σ ⟨sk,nr,t,true⟩ ∧
          (Exit σ rs.2.val v ∨
            (t.2.val=rs.2.val+1 ∧
             pursuitFile d sk<pursuitFile d t ∧
             lowerRoutingRank d sk nr t < lowerRoutingRank d sk rs wk)) := by
  dsimp
  let k : Fin 8 := if pursuitFile d rs=0 then 1 else 0
  let nr : Square := backRook d k rs
  have hnr : pursuitFile d nr=k.val := by
    cases d <;> simp [nr,backRook,backFile,pursuitFile] <;> omega
  have hk : k.val≤1 := by dsimp [k]; split <;> decide
  have hdistinct : nr≠rs := by
    intro he
    have hsame : pursuitFile d nr=pursuitFile d rs := congrArg (pursuitFile d) he
    dsimp [k] at hnr
    split at hnr <;> simp only [Fin.val_zero,Fin.val_one] at hnr <;> omega
  have hf3 : 3≤absDiff nr.1.val wk.1.val := by
    rw [←pursuit_absDiff d nr wk]; simp only [absDiff]; omega
  have phys : 1≤sk.1.val ∧ sk.1.val≤6 := by
    have hw7 := pursuitFile_bound d wk
    cases d <;> simp only [pursuitFile,Bool.false_eq_true,↓reduceIte] at * <;> omega
  obtain ⟨c,hl,hm,hne,hall⟩ := krk_wall_rook_move hq (by omega) (by omega)
    (nr := nr) rfl hdistinct hf3
  refine ⟨c,hl,hm,hne,?_⟩
  intro v hv
  obtain ⟨t,hmt,hty,hft,hunit,hshape⟩ := hall v hv
  refine ⟨t,hmt,?_⟩
  rcases hshape hw with hu | ⟨htband,hdx⟩
  · exact Or.inl ⟨sk,nr,t,hmt,hb,rfl,hty,phys.1,phys.2,hft,Or.inl hu⟩
  by_cases hal : sk.1.val=t.1.val
  · exact Or.inl ⟨sk,nr,t,hmt,hb,rfl,hty,phys.1,phys.2,hft,Or.inr hal⟩
  have hdx' : absDiff (pursuitFile d t) (pursuitFile d wk)=1 := by
    rw [pursuit_absDiff]; exact hdx
  have hnot : pursuitFile d sk≠pursuitFile d t := by
    intro he; apply hal
    cases d <;> simp only [pursuitFile,Bool.false_eq_true,↓reduceIte] at he <;> omega
  have hlt : pursuitFile d sk<pursuitFile d t := by
    simp only [absDiff] at hdx'; omega
  right
  refine ⟨htband,hlt,?_⟩
  change lowerRoutingRank d sk nr t < lowerRoutingRank d sk rs wk
  have hback : pursuitFile d nr≤1 := by omega
  by_cases hr : pursuitFile d rs≤1
  · have hone : pursuitFile d wk=pursuitFile d sk+1 := by
      have hwide : pursuitFile d sk+2≤pursuitFile d wk →
          3≤absDiff rs.1.val wk.1.val := by
        intro hh
        rw [←pursuit_absDiff d rs wk]; simp only [absDiff]; omega
      omega
    have hold : (pursuitFile d wk-pursuitFile d sk)%2≠0 := by omega
    have heven : (pursuitFile d t-pursuitFile d sk)%2=0 := by
      simp only [absDiff] at hdx'; omega
    simp only [lowerRoutingRank,lowerRoutingDebt,ite_eq_left hr,ite_eq_left hback,
      ite_eq_right hold,ite_eq_left heven]
    omega
  · have debt := lowerRoutingDebt_bound d sk nr t
    have newDebt : lowerRoutingDebt d sk nr t≤1 := by
      unfold lowerRoutingDebt
      rw [ite_eq_left hback]
      split <;> omega
    simp only [lowerRoutingRank,lowerRoutingDebt,ite_eq_right hr]
    unfold lowerRoutingDebt at newDebt
    omega

/-- An upper EXIT can lift its rook even when pursuit left the strong
king off-centre. Restoration begins only AFTER this lift. -/
theorem offCentreUpper_sound {q : Position} {σ : Colour} {sk rs wk : Square}
    (hq : Matches q σ ⟨sk,rs,wk,true⟩)
    (hb : sk.2.val+1=rs.2.val) (hw : rs.2.val+2≤wk.2.val)
    (hx : 1≤sk.1.val ∧ sk.1.val≤6)
    (hf : 2≤absDiff rs.1.val wk.1.val) :
    ∃ c, Legal q c ∧
      Matches c σ ⟨sk,rankAdvanceDestination rs (by omega),wk,false⟩ ∧
      (∃ v, Legal c v) ∧ ∀ v, Legal c v →
        ∃ t, Matches v σ ⟨sk,rankAdvanceDestination rs (by omega),t,true⟩ ∧
          sk.2.val+2=(rankAdvanceDestination rs (by omega)).2.val ∧
          (rankAdvanceDestination rs (by omega)).2.val<t.2.val ∧
          1≤sk.1.val ∧ sk.1.val≤6 := by
  obtain ⟨nr,c,hfile,hrank,hl,hm,hne,hall⟩ := rank_two_pair hq (by omega) hw hf
  have heq : nr=rankAdvanceDestination rs (by omega) := by
    apply Prod.ext
    · exact hfile
    · apply Fin.ext; exact hrank
  rw [heq] at hm
  refine ⟨c,hl,hm,hne,?_⟩
  intro v hv
  obtain ⟨t,hmt,hty,_⟩ := hall v hv
  rw [heq] at hmt hty
  exact ⟨t,hmt,by change sk.2.val+2=rs.2.val+1; omega,hty,hx⟩

/-- Only the two source coordinate constructors are admitted at lower nodes. -/
def LowerChosen (σ : Colour) (d : Bool) (q c : Position) : Prop :=
  ∃ sk rs wk : Square, Matches q σ ⟨sk,rs,wk,true⟩ ∧
    if h : pursuitFile d sk+2≤pursuitFile d wk ∧
        3≤absDiff rs.1.val wk.1.val then
      Matches c σ ⟨lowerPursuitDestination d sk
        (by have hh := pursuitFile_bound d wk; omega),rs,wk,false⟩
    else Matches c σ ⟨sk,centralBackDestination d rs,wk,false⟩

/-- A finite all-reply derivation using only the selected source coordinate.
The index is a termination rank, not a claimed mating distance. -/
inductive LowerRunsToExit (σ : Colour) (y : Nat) : Position → Nat → Prop
  | exit {q n} : Exit σ y q → LowerRunsToExit σ y q n
  | pair {q c n} (d : Bool) :
      LowerChosen σ d q c → Legal q c → (∃ v, Legal c v) →
      (∀ v, Legal c v → LowerRunsToExit σ y v n) →
      LowerRunsToExit σ y q (n+1)

/-- One decreasing induction handles both pursuit and tempo. Every continuing
lower reply retains its fixed orientation; no restoration node occurs. -/
theorem lowerRouting_terminates (d : Bool) {σ : Colour} {y : Nat}
    {q : Position} {sk rs wk : Square}
    (hq : Matches q σ ⟨sk,rs,wk,true⟩)
    (hb : sk.2.val+1=rs.2.val) (hry : rs.2.val=y)
    (hw : wk.2.val=rs.2.val+1)
    (hs : 3≤pursuitFile d sk) (hx : pursuitFile d sk<pursuitFile d wk) :
    LowerRunsToExit σ y q (lowerRoutingRank d sk rs wk) := by
  suffices main : ∀ n, ∀ {q : Position} {sk rs wk : Square},
      Matches q σ ⟨sk,rs,wk,true⟩ → sk.2.val+1=rs.2.val → rs.2.val=y →
      wk.2.val=rs.2.val+1 → 3≤pursuitFile d sk →
      pursuitFile d sk<pursuitFile d wk → lowerRoutingRank d sk rs wk≤n →
      LowerRunsToExit σ y q n by
    exact main _ hq hb hry hw hs hx (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
    intro q sk rs wk hq hb hry hw hs hx hn
    have hw7 := pursuitFile_bound d wk
    unfold lowerRoutingRank lowerRoutingDebt at hn
    split at hn <;> (try split at hn) <;> omega
  | succ n ih =>
    intro q sk rs wk hq hb hry hw hs hx hn
    by_cases hc : pursuitFile d sk+2≤pursuitFile d wk ∧
        3≤absDiff rs.1.val wk.1.val
    · obtain ⟨c,hl,hm,hne,hall⟩ := lowerChaseRouting_sound d hq hb hw hs hc.1 hc.2
      refine LowerRunsToExit.pair d ?_ hl hne ?_
      · refine ⟨sk,rs,wk,hq,?_⟩
        simp only [dite_eq_left hc]
        exact hm
      · intro v hv
        obtain ⟨t,hmt,he | ⟨hbu,hty,hsu,hlt,hdrop⟩⟩ := hall v hv
        · exact .exit (by simpa only [hry] using he)
        · exact ih hmt hbu hry hty hsu hlt (by omega)
    · obtain ⟨c,hl,hm,hne,hall⟩ := lowerWaitRouting_sound d hq hb hw hs hx hc
      refine LowerRunsToExit.pair d ?_ hl hne ?_
      · refine ⟨sk,rs,wk,hq,?_⟩
        simp only [dite_eq_right hc]
        exact hm
      · intro v hv
        obtain ⟨t,hmt,he | ⟨hty,hlt,hdrop⟩⟩ := hall v hv
        · exact .exit (by simpa only [hry] using he)
        · exact ih hmt hb hry hty hs hlt (by omega)

/-- In particular every central nonaligned lower root reaches an EXIT
within five complete pairs, with the same explicit coordinate selection. -/
theorem lowerCentralWithinFive (d : Bool) {σ : Colour} {y : Nat}
    {q : Position} {sk rs wk : Square}
    (hq : Matches q σ ⟨sk,rs,wk,true⟩)
    (hb : sk.2.val+1=rs.2.val) (hry : rs.2.val=y)
    (hw : wk.2.val=rs.2.val+1)
    (hs : 3≤pursuitFile d sk) (hx : pursuitFile d sk<pursuitFile d wk) :
    ∃ n, n≤5 ∧ LowerRunsToExit σ y q n := by
  refine ⟨lowerRoutingRank d sk rs wk,?_,
    lowerRouting_terminates d hq hb hry hw hs hx⟩
  have debt := lowerRoutingDebt_bound d sk rs wk
  unfold lowerRoutingRank
  omega

#print axioms lowerCentralWithinFive
#print axioms lowerRouting_terminates
#print axioms lowerChaseRouting_sound
#print axioms lowerWaitRouting_sound
#print axioms offCentreUpper_sound
end EndgameChess.Rules.KRKExecutable
