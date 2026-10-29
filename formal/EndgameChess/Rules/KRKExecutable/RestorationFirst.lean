import EndgameChess.Rules.KRKExecutable.AlignedExit
import EndgameChess.Rules.KRKCentral.Restoration

/-!
KRK05: extract the *first executable restoration pair* already used by the
frozen KRKCentral.restoration_bound argument. This is an exact two-way
constructor: a far-file rook rescue if the margin is below three, or a
centralising king catch-up if it is at least three. Each local step has its
entire set of legal weak-king replies covered. It is NOT a total mate policy.
-/
namespace EndgameChess.Rules.KRKExecutable
open EndgameChess.KK EndgameChess.Rules EndgameChess.Rules.KRKCentral

def restorationFarDestination (rs wk : Square) : Square :=
  (wallFarFile wk.1,rs.2)

/-- The margin-deficient restoration case must relocate the rook to a far
file. Every legal reply then has margin at least three, so the constructive
king catch-up case applies; no blind rook move is permitted. -/
theorem restorationFar_sound {q : Position} {σ : Colour}
    {sk rs wk : Square}
    (hq : Matches q σ ⟨sk,rs,wk,true⟩)
    (hb : sk.2.val+2=rs.2.val)
    (hw : rs.2.val<wk.2.val)
    (hclose : ¬ 3≤absDiff rs.1.val wk.1.val) :
    let nr := restorationFarDestination rs wk
    ∃ c, Legal q c ∧ Matches c σ ⟨sk,nr,wk,false⟩ ∧
      (∃ v, Legal c v) ∧ ∀ v, Legal c v →
        ∃ t, Matches v σ ⟨sk,nr,t,true⟩ ∧
          rs.2.val<t.2.val ∧ 3≤absDiff nr.1.val t.1.val := by
  dsimp
  let nr : Square := restorationFarDestination rs wk
  have hfar : 4≤absDiff nr.1.val wk.1.val := by
    simpa only [nr,restorationFarDestination] using wall_far_margin wk.1
  have hne : nr≠rs := by
    intro he
    have hefile : nr.1.val=rs.1.val :=
      congrArg (fun s : Square => s.1.val) he
    rw [hefile] at hfar
    omega
  obtain ⟨c,hl,hm,hnonempty,hall⟩ :=
    krk_wall_rook_move hq (by omega) hw
      (nr := nr) rfl hne (by omega)
  refine ⟨c,hl,hm,hnonempty,?_⟩
  intro v hv
  obtain ⟨t,hmt,hty,_,hunit,_⟩ := hall v hv
  refine ⟨t,hmt,hty,?_⟩
  exact pursuit_margin_step (a := nr) (b := wk) (c := t) (k := 3) hfar hunit

/-- The precise king square used by the restoration proof for interior
strong-king files, moving diagonally up and toward files 3–4. -/
def restorationKingDestination (sk : Square)
    (hy : sk.2.val+2≤7) (hx : 1≤sk.1.val ∧ sk.1.val≤6) : Square :=
  (⟨if sk.1.val<3 then sk.1.val+1
    else if 4<sk.1.val then sk.1.val-1 else sk.1.val, by
      split <;> (try split) <;> omega⟩,
   ⟨sk.2.val+1,by omega⟩)

/-- At restored margin ≥3 the explicitly named king-up square is legal
and all replies leave a wall, two-file rook margin and a king in files 2–5.
A subsequent centre-alignment step is still required in files 2 or 5. -/
theorem restorationKing_sound {q : Position} {σ : Colour}
    {sk rs wk : Square}
    (hq : Matches q σ ⟨sk,rs,wk,true⟩)
    (hb : sk.2.val+2=rs.2.val)
    (hw : rs.2.val<wk.2.val)
    (hx : 1≤sk.1.val ∧ sk.1.val≤6)
    (hmargin : 3≤absDiff rs.1.val wk.1.val) :
    let su := restorationKingDestination sk (by omega) hx
    ∃ c, Legal q c ∧ Matches c σ ⟨su,rs,wk,false⟩ ∧
      (∃ v, Legal c v) ∧ ∀ v, Legal c v →
        ∃ t, Matches v σ ⟨su,rs,t,true⟩ ∧
          rs.2.val<t.2.val ∧ 2≤absDiff rs.1.val t.1.val ∧
          2≤su.1.val ∧ su.1.val≤5 := by
  dsimp
  let su : Square := restorationKingDestination sk (by omega) hx
  have hsux : 2≤su.1.val ∧ su.1.val≤5 ∧
      absDiff sk.1.val su.1.val≤1 := by
    dsimp [su,restorationKingDestination]
    split <;> (try split) <;> simp only [absDiff] <;> omega
  have hsuy : su.2.val=sk.2.val+1 := rfl
  have hstep : dInf sk su=1 := by
    change max (absDiff sk.1.val su.1.val)
      (absDiff sk.2.val su.2.val)=1
    simp only [absDiff] at *
    omega
  obtain ⟨c,hl,hm,hnonempty,hall⟩ :=
    king_below_pair hq hstep (by omega) hw hmargin
  refine ⟨c,hl,hm,hnonempty,?_⟩
  intro v hv
  obtain ⟨t,hmt,hty,hunit⟩ := hall v hv
  have hmargin2 : 2≤absDiff rs.1.val t.1.val := by
    simp only [absDiff] at *
    omega
  exact ⟨t,hmt,hty,hmargin2,hsux.1,hsux.2.1⟩

end EndgameChess.Rules.KRKExecutable
