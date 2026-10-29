import EndgameChess.Rules.KRKCentral.Positive

/-!
KRK08: an executable coordinate for the lower-band pursuit pair.

The underlying source theorem is `krk_pursuit_king_move`. This new
unfrozen adapter makes the destination explicit and classifies *all*
defender replies into an upper exit, aligned exit, or a strictly smaller
oriented file-pursuit rank. It is not a global KRK winning policy.
-/
namespace EndgameChess.Rules.KRKExecutable
open EndgameChess.KK EndgameChess.Rules EndgameChess.Rules.KRKCentral

def lowerPursuitDestination (d : Bool) (sk : Square)
    (h : pursuitFile d sk + 2 ≤ 7) : Square :=
  match d with
  | true => (⟨sk.1.val + 1, by
      simp only [pursuitFile, ↓reduceIte] at h
      omega⟩, sk.2)
  | false => (⟨sk.1.val - 1, by
      simp only [pursuitFile, Bool.false_eq_true, ↓reduceIte] at h
      omega⟩, sk.2)

theorem lowerPursuitDestination_coords (d : Bool) (sk : Square)
    (h : pursuitFile d sk + 2 ≤ 7) :
    (lowerPursuitDestination d sk h).2 = sk.2 ∧
    pursuitFile d (lowerPursuitDestination d sk h) =
      pursuitFile d sk + 1 := by
  cases d <;> simp only [lowerPursuitDestination, pursuitFile, Bool.false_eq_true, ↓reduceIte] at h ⊢ <;> omega

/-- Concrete lower-band king step: every legal defender response either
opens the upper exit, aligns the king files, or leaves the strong king
one file closer in the fixed orientation with the rook still safe. -/
theorem lowerPursuitPair_sound (d : Bool) {q : Position} {σ : Colour}
    {sk rs wk : Square}
    (hq : Matches q σ ⟨sk,rs,wk,true⟩)
    (hb : sk.2.val+1=rs.2.val)
    (hw : wk.2.val=rs.2.val+1)
    (hx : pursuitFile d sk+2≤pursuitFile d wk)
    (hf : 3≤absDiff rs.1.val wk.1.val) :
    let su := lowerPursuitDestination d sk
      (by have h := pursuitFile_bound d wk; omega)
    ∃ c, Legal q c ∧ Matches c σ ⟨su,rs,wk,false⟩ ∧
      (∃ v, Legal c v) ∧
      ∀ v, Legal c v →
        ∃ t, Matches v σ ⟨su,rs,t,true⟩ ∧
          2≤absDiff rs.1.val t.1.val ∧
          (rs.2.val+2≤t.2.val ∨
            (t.2.val=rs.2.val+1 ∧
              (su.1.val=t.1.val ∨
                (pursuitFile d su < pursuitFile d t ∧
                  7-pursuitFile d su < 7-pursuitFile d sk)))) := by
  dsimp
  obtain ⟨ss,c,hsy,hsx,hl,hm,hne,hall⟩ :=
    krk_pursuit_king_move d hq hb hw hx hf
  have bound : pursuitFile d sk+2≤7 := by
    have h := pursuitFile_bound d wk
    omega
  have hs : ss = lowerPursuitDestination d sk bound := by
    apply Prod.ext
    · apply Fin.ext
      cases d <;>
        simp only [pursuitFile, Bool.false_eq_true, ↓reduceIte] at hsx <;>
        simp only [lowerPursuitDestination, Bool.false_eq_true, ↓reduceIte] <;>
        omega
    · cases d <;> simpa [lowerPursuitDestination] using hsy
  have hcoord := (lowerPursuitDestination_coords d sk bound).2
  subst ss
  refine ⟨c,hl,hm,hne,?_⟩
  intro v hv
  obtain ⟨t,hmt,hmargin,hunit,hshape⟩ := hall v hv
  refine ⟨t,hmt,hmargin,?_⟩
  rcases hshape with upper | ⟨hband,_⟩
  · exact Or.inl upper
  · refine Or.inr ⟨hband,?_⟩
    by_cases halign : (lowerPursuitDestination d sk bound).1.val=t.1.val
    · exact Or.inl halign
    · right
      have hd : pursuitFile d (lowerPursuitDestination d sk bound) <
          pursuitFile d t := by
        cases d <;>
          simp only [pursuitFile, Bool.false_eq_true, ↓reduceIte] at * <;>
          simp only [absDiff] at * <;> omega
      constructor
      · exact hd
      · have hbelow := pursuitFile_bound d (lowerPursuitDestination d sk bound)
        omega

#print axioms EndgameChess.Rules.KRKExecutable.lowerPursuitPair_sound

end EndgameChess.Rules.KRKExecutable
