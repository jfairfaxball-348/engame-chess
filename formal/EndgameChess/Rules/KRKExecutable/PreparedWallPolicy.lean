import EndgameChess.Rules.KRKExecutable.CentralPolicy
import EndgameChess.Rules.KRKExecutable.PrepController

/-!
KRK11: the exact source-selected preparation controller, followed by
KRK10's tagged central-to-mate strategy. The entire play is a static
(all-defender) constructive strategy; no 50-move, repetition, or
arbitrary-root claims are made here.
-/
namespace EndgameChess.Rules.KRKExecutable
open EndgameChess.KK EndgameChess.Rules EndgameChess.Rules.KRKCentral
set_option maxHeartbeats 4000000

/-- The proof uses only the concrete coordinate from `prepNext`. -/
inductive PreparedChoice (σ : Colour) : Position → Position → Prop
  | next {q c sk rs wk}
      (hq : Matches q σ ⟨sk,rs,wk,true⟩)
      (hb : sk.2.val<rs.2.val) (hw : rs.2.val<wk.2.val)
      (hp : 0<prepRank sk rs wk)
      (hm : Matches c σ ⟨(prepNext sk rs wk).1,
        (prepNext sk rs wk).2,wk,false⟩) :
      PreparedChoice σ q c

theorem preparedChoice_turns {σ q c} (h : PreparedChoice σ q c) :
    q.turn=σ ∧ c.turn=σ.opp := by
  cases h with
  | next hq _ _ _ hm => exact ⟨hq.2,hm.2⟩

/-- The prepared phase hands directly to an actual selected CentralRun,
not to an existential outcome theorem or an unspecified later strategy. -/
inductive PreparedRun (σ : Colour) : Position → Nat → Prop
  | ready {q n} : CentralRun σ .central q n → PreparedRun σ q n
  | pair {q c n} : PreparedChoice σ q c → Legal q c →
      (∃ v, Legal c v) →
      (∀ v, Legal c v → PreparedRun σ v n) →
      PreparedRun σ q (n+2)
  | mono {q n m} : PreparedRun σ q n → n≤m → PreparedRun σ q m

theorem preparedRun_mateWithin {σ q n} (h : PreparedRun σ q n) :
    MateWithin σ n q := by
  induction h with
  | ready run => exact centralRun_mateWithin run
  | pair chosen hl hne _ ih =>
      exact mateWithin_pair (preparedChoice_turns chosen).1 hl
        (preparedChoice_turns chosen).2 hne ih
  | mono _ hn ih => exact mateWithin_mono ih hn

theorem prepNext_rook_rank (sk rs wk : Square) :
    (prepNext sk rs wk).2.2=rs.2 := by
  by_cases h : 2≤absDiff rs.1.val wk.1.val <;>
    simp [prepNext,h]

theorem prepNext_king_below (sk rs wk : Square)
    (hb : sk.2.val<rs.2.val) :
    (prepNext sk rs wk).1.2.val<(prepNext sk rs wk).2.2.val := by
  by_cases h : 2≤absDiff rs.1.val wk.1.val
  · simp only [prepNext,if_pos h,prepDestination]
    split <;> omega
  · simp [prepNext,h,hb]

/-- A zero preparation rank has exactly the central-wall premises. -/
theorem prepared_ready {σ q sk rs wk}
    (hq : Matches q σ ⟨sk,rs,wk,true⟩)
    (hb : sk.2.val<rs.2.val) (hw : rs.2.val<wk.2.val)
    (hz : prepRank sk rs wk=0) :
    CentralRun σ .central q (18*((7-rs.2.val)-1)+11) := by
  obtain ⟨hd,_⟩ := prepRank_zero_iff.mp hz
  have hgap : sk.2.val+1=rs.2.val := by
    unfold prepDistance at hd
    omega
  have hcentre : centreDistance sk.1.val=0 := by
    unfold prepDistance at hd
    omega
  have hfile : sk.1.val=3 ∨ sk.1.val=4 := by
    unfold centreDistance at hcentre
    split at hcentre <;> (try split at hcentre) <;> omega
  exact policy_uncut_central_bound hq hgap rfl hw hfile

/-- Every strict rank wall, not merely an already centered one, has a
finite, source-selected all-defender run to actual checkmate. Preparation
takes at most two plies per rank decrease, and the SAME central policy
handles the resulting zero-rank wall. This is a static bound only. -/
theorem policy_prepared_wall_run {σ : Colour} {q sk rs wk}
    (hq : Matches q σ ⟨sk,rs,wk,true⟩)
    (hb : sk.2.val<rs.2.val) (hw : rs.2.val<wk.2.val) :
    PreparedRun σ q
      (2*prepRank sk rs wk + (18*((7-rs.2.val)-1)+11)) := by
  let y := rs.2.val
  let B := 18*((7-y)-1)+11
  suffices main : ∀ n, ∀ {q sk rs wk},
      Matches q σ ⟨sk,rs,wk,true⟩ →
      sk.2.val<rs.2.val → rs.2.val<wk.2.val →
      rs.2.val=y → prepRank sk rs wk≤n →
      PreparedRun σ q (2*n+B) by
    exact main (prepRank sk rs wk) hq hb hw rfl (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
      intro q sk rs wk hq hb hw hry hn
      have hz : prepRank sk rs wk=0 := by omega
      have hc := prepared_ready hq hb hw hz
      rw [hry] at hc
      simpa [B] using (PreparedRun.ready hc)
  | succ n ih =>
      intro q sk rs wk hq hb hw hry hn
      by_cases hz : prepRank sk rs wk=0
      · have hc := prepared_ready hq hb hw hz
        rw [hry] at hc
        exact PreparedRun.mono (PreparedRun.ready hc) (by dsimp [B]; omega)
      · have hp : 0<prepRank sk rs wk := by omega
        obtain ⟨c,hl,hm,hne,hall⟩ := prepNext_sound hq hb hw hp
        apply PreparedRun.mono (n := 2*n+B+2) ?_ (by omega)
        refine PreparedRun.pair (.next hq hb hw hp hm) hl hne ?_
        intro v hv
        obtain ⟨t,hmt,hty,hdrop⟩ := hall v hv
        have hbelow := prepNext_king_below sk rs wk hb
        have hrook : (prepNext sk rs wk).2.2.val=y := by
          rw [prepNext_rook_rank]; exact hry
        exact ih hmt hbelow hty hrook (by omega)

theorem policy_prepared_wall_mateWithin {σ : Colour} {q sk rs wk}
    (hq : Matches q σ ⟨sk,rs,wk,true⟩)
    (hb : sk.2.val<rs.2.val) (hw : rs.2.val<wk.2.val) :
    MateWithin σ
      (2*prepRank sk rs wk + (18*((7-rs.2.val)-1)+11)) q :=
  preparedRun_mateWithin (policy_prepared_wall_run hq hb hw)

#print axioms policy_prepared_wall_run
#print axioms policy_prepared_wall_mateWithin
end EndgameChess.Rules.KRKExecutable
