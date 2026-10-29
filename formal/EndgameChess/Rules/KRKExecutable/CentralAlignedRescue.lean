import EndgameChess.Rules.KRKExecutable.RestorationCentre

/-!
KRK06: the first constructive action of Central.central_bound's
*aligned, rook-margin-deficient* branch. This is an exact fixed rook
destination, with every legal weak reply quantified. It is NOT a
complete central-to-mate selector.
-/
namespace EndgameChess.Rules.KRKExecutable
open EndgameChess.KK EndgameChess.Rules EndgameChess.Rules.KRKCentral

def centralAlignedRescueDestination (rs wk : Square) : Square :=
  (wallFarFile wk.1, rs.2)

/-- When a central close wall is aligned with the weak king but the rook
has fewer than two files of margin, the far-file rook relocation is legal.
Every defender reply keeps the rank wall and leaves >=3 files of margin.
Unlike a generic rook rescue, this is the explicit aligned branch in
KRKCentral.central_bound; its successor is not automatically an exit. -/
theorem centralAlignedRescue_sound {q : Position} {σ : Colour}
    {sk rs wk : Square}
    (hq : Matches q σ ⟨sk,rs,wk,true⟩)
    (hsy : sk.2.val+1=rs.2.val)
    (hw : rs.2.val<wk.2.val)
    (halign : sk.1.val=wk.1.val)
    (hclose : ¬ 2≤absDiff rs.1.val wk.1.val) :
    let nr := centralAlignedRescueDestination rs wk
    ∃ c, Legal q c ∧ Matches c σ ⟨sk,nr,wk,false⟩ ∧
      (∃ v, Legal c v) ∧ ∀ v, Legal c v →
        ∃ t, Matches v σ ⟨sk,nr,t,true⟩ ∧
          rs.2.val<t.2.val ∧ 3≤absDiff nr.1.val t.1.val := by
  dsimp
  let nr : Square := centralAlignedRescueDestination rs wk
  have hfar : 4≤absDiff nr.1.val wk.1.val := by
    simpa only [nr,centralAlignedRescueDestination] using wall_far_margin wk.1
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

#print axioms EndgameChess.Rules.KRKExecutable.centralAlignedRescue_sound

end EndgameChess.Rules.KRKExecutable
