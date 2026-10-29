import EndgameChess.Rules.KRKSixGlobal
import EndgameChess.Rules.KRKSixPlyHistory

namespace EndgameChess.Rules.KRKSevenPrefix
open EndgameChess.KK KRKThreePly KRKLastReply KRKOppositionHistory KRKNativeFrame KRKCanonicalSlots
open KRKCornerSlotBarriers (Axis)
set_option maxHeartbeats 500000

/- These formulas retain the complete ORIGINAL trace. `root` is the first
strong move; the subsequent weak/strong prefix keys are added explicitly. -/

def weakBoard (s : RawTrace.State) (root : Move) (initial destination : Square) : Position :=
  play (KRKStrongPrefix.afterBoard s root) ⟨initial,destination,none⟩

noncomputable def firstOccurrences (s : RawTrace.State) (root : Move) (initial destination : Square) (q : Position) : Nat :=
  KRKStrongPrefix.afterOccurrences s root q +
    (by classical exact if RawRepetition.key (weakBoard s root initial destination) = RawRepetition.key q then 1 else 0)

def secondBoard (s : RawTrace.State) (root : Move) (initial destination : Square) (m : Move) : Position := play (weakBoard s root initial destination) m

noncomputable def secondOccurrences (s : RawTrace.State) (root : Move) (initial destination : Square) (m : Move) (q : Position) : Nat :=
  firstOccurrences s root initial destination q +
    (by classical exact if RawRepetition.key (secondBoard s root initial destination m) = RawRepetition.key q then 1 else 0)

def thirdBoard (s : RawTrace.State) (root : Move) (initial destination : Square) (m : Move) (wk t : Square) : Position :=
  play (secondBoard s root initial destination m) ⟨wk,t,none⟩

def FourthEntry (s : RawTrace.State) (root : Move) (initial destination : Square) (m : Move) (wk t : Square) (entry : Move) (u : Square) : Prop :=
  RawClock.clock s.trace < 94 ∧
    secondOccurrences s root initial destination m (play (thirdBoard s root initial destination m wk t) entry) < 2 ∧
    secondOccurrences s root initial destination m (play (play (thirdBoard s root initial destination m wk t) entry) ⟨t,u,none⟩) < 2

def InnerKingPoints (s : RawTrace.State) (root : Move) (initial destination : Square) (m : Move) (g : Frame) (sk rs wk t : Square) : Prop :=
  ∃ i : Kind, Valid (g.f t) i ∧ Region (g.f t) i (g.f rs) ∧
    dInf (g.f sk) (king (g.f t) i) = 1 ∧
      FourthEntry s root initial destination m wk t ⟨sk, g.r (king (g.f t) i), none⟩ (g.r (reply (g.f t) i))

def InnerRookRays (s : RawTrace.State) (root : Move) (initial destination : Square) (m : Move) (g : Frame) (sk rs wk t : Square) : Prop :=
  ∃ i : Kind, Valid (g.f t) i ∧ g.f sk = king (g.f t) i ∧
    ∃ a : Axis, ∃ v : Fin 8, KRKFramedHistory.AllowedRay (g.f t) (g.f rs) i a v ∧
      FourthEntry s root initial destination m wk t ⟨rs, g.r (a.target (g.f rs) v), none⟩ (g.r (reply (g.f t) i))

def InnerClear (s : RawTrace.State) (root : Move) (initial destination : Square) (m : Move) (g : Frame) (sk rs wk t : Square) : Prop :=
  KRKImmediate.MateNow (g.f sk) (g.f rs) (g.f t) ∨
    InnerKingPoints s root initial destination m g sk rs wk t ∨ InnerRookRays s root initial destination m g sk rs wk t

def WeakAfter (s : RawTrace.State) (root : Move) (initial destination : Square) (m : Move) (sk rs wk : Square) : Prop :=
  SafeRook sk rs wk ∧ RawClock.clock s.trace < 96 ∧
    firstOccurrences s root initial destination (secondBoard s root initial destination m) < 2 ∧
    ∀ t : Square, KRKCornerWeakBand.Guard sk rs wk t →
      secondOccurrences s root initial destination m (thirdBoard s root initial destination m wk t) < 2 ∧
        KRKEdgeDepth.depth t = 0 ∧ InnerClear s root initial destination m (normalize t) sk rs wk t

def OuterKingPoints (s : RawTrace.State) (root : Move) (initial destination : Square) (sk rs wk : Square) : Prop :=
  let g := normalize wk
  ∃ i : KRKFourSlots.Kind, KRKFourSlots.Valid (g.f wk) i ∧ KRKFourSlots.Region (g.f wk) (g.f rs) i ∧
    dInf (g.f sk) (KRKFourSlots.king (g.f wk) i) = 1 ∧ KRKFourSlots.king (g.f wk) i ≠ g.f rs ∧
      2 ≤ dInf (KRKFourSlots.king (g.f wk) i) (g.f wk) ∧
      KRKFivePlyHistory.Live (g.r (KRKFourSlots.king (g.f wk) i)) rs wk ∧
      WeakAfter s root initial destination ⟨sk,g.r (KRKFourSlots.king (g.f wk) i),none⟩ (g.r (KRKFourSlots.king (g.f wk) i)) rs wk

def OuterRookRays (s : RawTrace.State) (root : Move) (initial destination : Square) (sk rs wk : Square) : Prop :=
  let g := normalize wk
  ∃ i : KRKFourSlots.Kind, KRKFourSlots.Valid (g.f wk) i ∧ g.f sk = KRKFourSlots.king (g.f wk) i ∧
    ∃ a : KRKCornerSlotBarriers.Axis, ∃ v : Fin 8,
      RookSees (g.f rs) (a.target (g.f rs) v) (g.f sk) (g.f wk) ∧
      a.target (g.f rs) v ≠ g.f sk ∧ a.target (g.f rs) v ≠ g.f wk ∧
      KRKFourSlots.Region (g.f wk) (a.target (g.f rs) v) i ∧
      KRKFivePlyHistory.Live sk (g.r (a.target (g.f rs) v)) wk ∧
      WeakAfter s root initial destination ⟨rs,g.r (a.target (g.f rs) v),none⟩ sk (g.r (a.target (g.f rs) v)) wk

def StrongClear (s : RawTrace.State) (root : Move) (initial destination : Square) (sk rs wk : Square) : Prop :=
  KRKImmediate.MateNow sk rs wk ∨
    (KRKEdgeDepth.depth wk = 0 ∧ (OuterKingPoints s root initial destination sk rs wk ∨ OuterRookRays s root initial destination sk rs wk))

theorem first_occurrences_root {s : RawTrace.State} {root : Move} {initial destination : Square}
    (legal : isLegal (RawTrace.erase s) root = true) (q : Position) :
    KRKFiveWeakPrefix.firstOccurrences (RawTrace.append s root legal) initial destination q =
      firstOccurrences s root initial destination q := by
  classical
  unfold KRKFiveWeakPrefix.firstOccurrences firstOccurrences
  rw [KRKStrongPrefix.occurrences_append legal]
  rfl

theorem second_occurrences_root {s : RawTrace.State} {root m : Move} {initial destination : Square}
    (legal : isLegal (RawTrace.erase s) root = true) (q : Position) :
    KRKFiveWeakPrefix.secondOccurrences (RawTrace.append s root legal) initial destination m q =
      secondOccurrences s root initial destination m q := by
  classical
  unfold KRKFiveWeakPrefix.secondOccurrences secondOccurrences
  rw [first_occurrences_root legal]
  rfl

theorem fourth_entry_root_iff {s : RawTrace.State} {σ : Colour} {sk rs rootWeak initial destination wk t u : Square}
    {root m entry : Move} (material : IsKRK (RawTrace.erase s) σ sk rs rootWeak)
    (turn : (RawTrace.erase s).turn = σ) (legal : isLegal (RawTrace.erase s) root = true) :
    KRKFiveWeakPrefix.FourthEntry (RawTrace.append s root legal) initial destination m wk t entry u ↔
      FourthEntry s root initial destination m wk t entry u := by
  have quiet := KRKStrongPrefix.strong_quiet material turn legal
  unfold KRKFiveWeakPrefix.FourthEntry FourthEntry
  rw [RawClock.append_clock,quiet]
  simp only [Bool.false_eq_true,↓reduceIte,second_occurrences_root legal]
  have boards : KRKFiveWeakPrefix.thirdBoard (RawTrace.append s root legal) initial destination m wk t =
      thirdBoard s root initial destination m wk t := rfl
  rw [boards]
  change (RawClock.clock s.trace + 1 < 95 ∧ _) ↔ (RawClock.clock s.trace < 94 ∧ _)
  omega

theorem inner_clear_root_iff {s : RawTrace.State} {σ : Colour} {sk rs rootWeak initial destination ns nr wk t : Square}
    {root m : Move} (g : Frame) (material : IsKRK (RawTrace.erase s) σ sk rs rootWeak)
    (turn : (RawTrace.erase s).turn = σ) (legal : isLegal (RawTrace.erase s) root = true) :
    KRKFiveWeakPrefix.InnerClear (RawTrace.append s root legal) initial destination m g ns nr wk t ↔
      InnerClear s root initial destination m g ns nr wk t := by
  simp only [KRKFiveWeakPrefix.InnerClear,InnerClear,KRKFiveWeakPrefix.InnerKingPoints,InnerKingPoints,
    KRKFiveWeakPrefix.InnerRookRays,InnerRookRays,fourth_entry_root_iff material turn legal]

theorem weak_after_root_iff {s : RawTrace.State} {σ : Colour} {sk rs rootWeak initial destination ns nr wk : Square}
    {root m : Move} (material : IsKRK (RawTrace.erase s) σ sk rs rootWeak)
    (turn : (RawTrace.erase s).turn = σ) (legal : isLegal (RawTrace.erase s) root = true) :
    KRKFiveWeakPrefix.WeakAfter (RawTrace.append s root legal) initial destination m ns nr wk ↔
      WeakAfter s root initial destination m ns nr wk := by
  have quiet := KRKStrongPrefix.strong_quiet material turn legal
  unfold KRKFiveWeakPrefix.WeakAfter WeakAfter
  rw [RawClock.append_clock,quiet]
  simp only [Bool.false_eq_true,↓reduceIte,first_occurrences_root legal,second_occurrences_root legal,
    inner_clear_root_iff _ material turn legal]
  change (SafeRook ns nr wk ∧ RawClock.clock s.trace + 1 < 97 ∧ _) ↔
    (SafeRook ns nr wk ∧ RawClock.clock s.trace < 96 ∧ _)
  constructor <;> rintro ⟨safe,time,count,branches⟩ <;> exact ⟨safe,by omega,count,branches⟩

theorem strong_clear_root_iff {s : RawTrace.State} {σ : Colour} {sk rs initial destination ns nr wk : Square}
    {root : Move} (material : IsKRK (RawTrace.erase s) σ sk rs wk)
    (turn : (RawTrace.erase s).turn = σ) (legal : isLegal (RawTrace.erase s) root = true) :
    KRKFiveWeakPrefix.StrongClear (RawTrace.append s root legal) initial destination ns nr destination ↔
      StrongClear s root initial destination ns nr destination := by
  simp only [KRKFiveWeakPrefix.StrongClear,StrongClear,KRKFiveWeakPrefix.OuterKingPoints,OuterKingPoints,
    KRKFiveWeakPrefix.OuterRookRays,OuterRookRays,weak_after_root_iff material turn legal]

/-- Exact six-ply child-history test expressed entirely in the original
root trace and its explicit native prefix keys, without legal/outcome search. -/
def SixAfter (s : RawTrace.State) (root : Move) (sk rs wk : Square) : Prop :=
  SafeRook sk rs wk ∧ RawClock.clock s.trace < 98 ∧
    RawRepetition.occurrences s.trace (KRKStrongPrefix.afterBoard s root) < 2 ∧
    ∀ t, KRKCornerWeakBand.Guard sk rs wk t →
      KRKStrongPrefix.afterOccurrences s root (weakBoard s root wk t) < 2 ∧
        StrongClear s root wk t sk rs t

theorem six_append_iff {s : RawTrace.State} {σ : Colour} {sk rs ns nr wk : Square} {root : Move}
    (material : IsKRK (RawTrace.erase s) σ sk rs wk) (turn : (RawTrace.erase s).turn = σ)
    (legal : isLegal (RawTrace.erase s) root = true) :
    KRKSixPlyHistory.Clear (RawTrace.append s root legal) ns nr wk ↔ SixAfter s root ns nr wk := by
  have quiet := KRKStrongPrefix.strong_quiet material turn legal
  have current := RawRepetition.append_currentOccurrences s root legal
  change RawRepetition.currentOccurrences (RawTrace.append s root legal) =
    RawRepetition.occurrences s.trace (KRKStrongPrefix.afterBoard s root) + 1 at current
  unfold KRKSixPlyHistory.Clear SixAfter
  rw [RawClock.append_clock,quiet,current]
  simp only [Bool.false_eq_true,↓reduceIte,KRKStrongPrefix.occurrences_append legal,
    strong_clear_root_iff material turn legal]
  have boards : ∀ t, firstBoard (RawTrace.append s root legal) wk t = weakBoard s root wk t := fun _ => rfl
  simp only [boards]
  constructor <;> rintro ⟨safe,time,count,branches⟩ <;> exact ⟨safe,by omega,by omega,branches⟩

end EndgameChess.Rules.KRKSevenPrefix
