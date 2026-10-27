import EndgameChess.Rules.KRKGlobalWeakBand

namespace EndgameChess.Rules.KRKStrongPrefix
open EndgameChess.KK KRKThreePly KRKLastReply KRKOppositionHistory KRKNativeFrame KRKCanonicalSlots
open KRKCornerSlotBarriers (Axis)
set_option maxHeartbeats 500000

theorem strong_quiet {q : Position} {σ : Colour} {sk rs wk : Square}
    {m : Move} (material : IsKRK q σ sk rs wk) (turn : q.turn = σ)
    (legal : isLegal q m = true) : RawClock.zeroing q m = false := by
  have pseudo : isPseudo q m = true := by
    simp only [isLegal, Bool.and_eq_true] at legal; exact legal.1
  obtain ⟨noPawn, targets⟩ := krk_material_targets material pseudo
  have empty : q.board m.dst = none := by
    cases atDst : q.board m.dst with
    | none => rfl
    | some piece => exact False.elim ((targets piece atDst).2.2 turn)
  have pawnFalse : (q.board m.src == some ⟨q.turn, .pawn⟩) = false := by
    rw [Bool.eq_false_iff]; simpa using noPawn
  simp [RawClock.zeroing, pawnFalse, empty]

def afterBoard (s : RawTrace.State) (m : Move) : Position := play (RawTrace.erase s) m

noncomputable def afterOccurrences (s : RawTrace.State) (m : Move) (q : Position) : Nat :=
  RawRepetition.occurrences s.trace q +
    (by classical exact if RawRepetition.key (afterBoard s m) = RawRepetition.key q then 1 else 0)

def firstAfter (s : RawTrace.State) (m : Move) (wk t : Square) : Position :=
  play (afterBoard s m) ⟨wk,t,none⟩

def OriginalEntryAfter (s : RawTrace.State) (m : Move) (wk t : Square) (entry : Move) (u : Square) : Prop :=
  RawClock.clock s.trace < 96 ∧
    afterOccurrences s m (play (firstAfter s m wk t) entry) < 2 ∧
    afterOccurrences s m (play (play (firstAfter s m wk t) entry) ⟨t,u,none⟩) < 2

def KingPoints (s : RawTrace.State) (m : Move) (g : Frame) (sk rs wk t : Square) : Prop :=
  ∃ i : Kind, Valid (g.f t) i ∧ Region (g.f t) i (g.f rs) ∧
    dInf (g.f sk) (king (g.f t) i) = 1 ∧
      OriginalEntryAfter s m wk t ⟨sk, g.r (king (g.f t) i), none⟩ (g.r (reply (g.f t) i))

def RookRays (s : RawTrace.State) (m : Move) (g : Frame) (sk rs wk t : Square) : Prop :=
  ∃ i : Kind, Valid (g.f t) i ∧ g.f sk = king (g.f t) i ∧
    ∃ a : Axis, ∃ v : Fin 8, KRKFramedHistory.AllowedRay (g.f t) (g.f rs) i a v ∧
      OriginalEntryAfter s m wk t ⟨rs, g.r (a.target (g.f rs) v), none⟩ (g.r (reply (g.f t) i))

def Clear (s : RawTrace.State) (m : Move) (g : Frame) (sk rs wk t : Square) : Prop :=
  KRKImmediate.MateNow (g.f sk) (g.f rs) (g.f t) ∨
    KingPoints s m g sk rs wk t ∨ RookRays s m g sk rs wk t

def WeakAfter (s : RawTrace.State) (m : Move) (sk rs wk : Square) : Prop :=
  SafeRook sk rs wk ∧ RawClock.clock s.trace < 98 ∧
    RawRepetition.occurrences s.trace (afterBoard s m) < 2 ∧
    ∀ t : Square, KRKCornerWeakBand.Guard sk rs wk t →
      afterOccurrences s m (firstAfter s m wk t) < 2 ∧
        KRKEdgeDepth.depth t = 0 ∧ Clear s m (normalize t) sk rs wk t

theorem occurrences_append {s : RawTrace.State} {m : Move}
    (legal : isLegal (RawTrace.erase s) m = true) (q : Position) :
    RawRepetition.occurrences (RawTrace.append s m legal).trace q = afterOccurrences s m q := by
  classical
  unfold RawRepetition.occurrences afterOccurrences
  rw [RawOccurrences.append_occurrences]
  rfl

theorem original_entry_append_iff {s : RawTrace.State} {σ : Colour} {sk rs wk t u : Square} {m entry : Move}
    (material : IsKRK (RawTrace.erase s) σ sk rs wk) (turn : (RawTrace.erase s).turn = σ)
    (legal : isLegal (RawTrace.erase s) m = true) :
    KRKSlotPrefix.OriginalEntry (RawTrace.append s m legal) wk t entry u ↔ OriginalEntryAfter s m wk t entry u := by
  have quiet := strong_quiet material turn legal
  unfold KRKSlotPrefix.OriginalEntry OriginalEntryAfter
  rw [RawClock.append_clock,quiet]
  simp only [Bool.false_eq_true,↓reduceIte]
  rw [occurrences_append legal,occurrences_append legal]
  have boards : firstBoard (RawTrace.append s m legal) wk t = firstAfter s m wk t := rfl
  rw [boards]
  change (RawClock.clock s.trace + 1 < 97 ∧ _) ↔ (RawClock.clock s.trace < 96 ∧ _)
  omega

theorem clear_append_iff {s : RawTrace.State} {σ : Colour} {sk rs wk ns nr t : Square} {m : Move} (g : Frame)
    (material : IsKRK (RawTrace.erase s) σ sk rs wk) (turn : (RawTrace.erase s).turn = σ)
    (legal : isLegal (RawTrace.erase s) m = true) :
    KRKFramedPrefix.Clear (RawTrace.append s m legal) g ns nr wk t ↔ Clear s m g ns nr wk t := by
  simp only [KRKFramedPrefix.Clear,Clear,KRKFramedPrefix.KingPoints,KingPoints,
    KRKFramedPrefix.RookRays,RookRays,original_entry_append_iff material turn legal]

theorem weak_append_iff {s : RawTrace.State} {σ : Colour} {sk rs wk ns nr : Square} {m : Move}
    (material : IsKRK (RawTrace.erase s) σ sk rs wk) (turn : (RawTrace.erase s).turn = σ)
    (legal : isLegal (RawTrace.erase s) m = true) :
    KRKGlobalWeakBand.Clear (RawTrace.append s m legal) ns nr wk ↔ WeakAfter s m ns nr wk := by
  have quiet := strong_quiet material turn legal
  unfold KRKGlobalWeakBand.Clear WeakAfter
  rw [RawClock.append_clock,quiet,RawRepetition.append_currentOccurrences]
  simp only [Bool.false_eq_true,↓reduceIte]
  simp only [occurrences_append legal,clear_append_iff _ material turn legal]
  change (SafeRook ns nr wk ∧ RawClock.clock s.trace + 1 < 99 ∧
    RawRepetition.occurrences s.trace (afterBoard s m) + 1 < 3 ∧ _) ↔ _
  constructor <;> rintro ⟨safe,time,count,branches⟩ <;> exact ⟨safe,by omega,by omega,branches⟩


/-- The evaluated weak tests plus an actual coordinate reply imply a live
state. The explicit reply requirement excludes vacuous stalemate entries. -/
theorem weak_clear_kernel {s : RawTrace.State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (RawTrace.erase s) σ sk rs wk)
    (turn : (RawTrace.erase s).turn = σ.opp)
    (clear : KRKGlobalWeakBand.Clear s sk rs wk)
    (reply : ∃ t, KRKCornerWeakBand.Guard sk rs wk t) : MateWithin σ 4 (RawTrace.erase s) := by
  have safe := clear.1
  obtain ⟨t,guard⟩ := reply
  have legal := KRKCornerWeakBand.guard_legal material turn guard
  have nonempty : ∃ r, Legal (RawTrace.erase s) r := ⟨_,⟨_,legal,rfl⟩⟩
  have board : MateWithin σ 4 (RawTrace.erase s) := by
    apply mateWithin_defend turn nonempty
    intro r edge
    obtain ⟨m,legal,rfl⟩ := edge
    have edge : Legal (RawTrace.erase s) (play (RawTrace.erase s) m) := ⟨m,legal,rfl⟩
    obtain ⟨u,next,step⟩ := krk_safe_reply material turn safe edge
    have canonical := weak_move_eq material turn legal next.1
    have guard := KRKCornerWeakBand.step_guard step
    have branch := clear.2.2.2 u guard
    have normal := normalize_spec branch.2.1
    have childLegal : isLegal (RawTrace.erase s) ⟨wk,u,none⟩ = true := by rwa [←canonical]
    have history := (KRKFramedPrefix.history_append_iff (normalize u) material turn safe childLegal normal.1 normal.2).mpr branch.2.2
    have geometry := KRKWeakBranch.history_geometry history
    obtain ⟨far,notCheck⟩ := krk_strong_arrival_geometry edge next.1 next.2
    exact (strong_three_iff next.1 next.2 far notCheck).mpr geometry
  exact board

theorem weak_clear_ongoing {s : RawHistoryLayer.State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (RawHistoryLayer.erase s) σ sk rs wk)
    (turn : (RawHistoryLayer.erase s).turn = σ.opp)
    (clear : KRKGlobalWeakBand.Clear s.val sk rs wk)
    (reply : ∃ t, KRKCornerWeakBand.Guard sk rs wk t) : RawHistoryLayer.Ongoing s := by
  have board := weak_clear_kernel material turn clear reply
  obtain ⟨t,guard⟩ := reply
  have legal := KRKCornerWeakBand.guard_legal material turn guard
  have nonempty : ∃ r, Legal (RawHistoryLayer.erase s) r := ⟨_,⟨_,legal,rfl⟩⟩
  apply (RawAdjudication.ongoing_iff s.val).mpr
  exact ⟨forceMate_not_dead ⟨4,board⟩,nonempty,by have h := clear.2.1; omega,
    by have h := clear.2.2.1; omega⟩

end EndgameChess.Rules.KRKStrongPrefix
