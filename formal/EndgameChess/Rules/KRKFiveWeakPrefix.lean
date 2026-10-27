import EndgameChess.Rules.KRKFivePlyHistory

namespace EndgameChess.Rules.KRKFiveWeakPrefix
open EndgameChess.KK KRKThreePly KRKLastReply KRKOppositionHistory KRKNativeFrame KRKCanonicalSlots
open KRKCornerSlotBarriers (Axis)
set_option maxHeartbeats 500000

def weakBoard (s : RawTrace.State) (initial destination : Square) : Position :=
  play (RawTrace.erase s) ⟨initial,destination,none⟩

noncomputable def firstOccurrences (s : RawTrace.State) (initial destination : Square) (q : Position) : Nat :=
  RawRepetition.occurrences s.trace q +
    (by classical exact if RawRepetition.key (weakBoard s initial destination) = RawRepetition.key q then 1 else 0)

def secondBoard (s : RawTrace.State) (initial destination : Square) (m : Move) : Position := play (weakBoard s initial destination) m

noncomputable def secondOccurrences (s : RawTrace.State) (initial destination : Square) (m : Move) (q : Position) : Nat :=
  firstOccurrences s initial destination q +
    (by classical exact if RawRepetition.key (secondBoard s initial destination m) = RawRepetition.key q then 1 else 0)

def thirdBoard (s : RawTrace.State) (initial destination : Square) (m : Move) (wk t : Square) : Position :=
  play (secondBoard s initial destination m) ⟨wk,t,none⟩

def FourthEntry (s : RawTrace.State) (initial destination : Square) (m : Move) (wk t : Square) (entry : Move) (u : Square) : Prop :=
  RawClock.clock s.trace < 95 ∧
    secondOccurrences s initial destination m (play (thirdBoard s initial destination m wk t) entry) < 2 ∧
    secondOccurrences s initial destination m (play (play (thirdBoard s initial destination m wk t) entry) ⟨t,u,none⟩) < 2

def InnerKingPoints (s : RawTrace.State) (initial destination : Square) (m : Move) (g : Frame) (sk rs wk t : Square) : Prop :=
  ∃ i : Kind, Valid (g.f t) i ∧ Region (g.f t) i (g.f rs) ∧
    dInf (g.f sk) (king (g.f t) i) = 1 ∧
      FourthEntry s initial destination m wk t ⟨sk, g.r (king (g.f t) i), none⟩ (g.r (reply (g.f t) i))

def InnerRookRays (s : RawTrace.State) (initial destination : Square) (m : Move) (g : Frame) (sk rs wk t : Square) : Prop :=
  ∃ i : Kind, Valid (g.f t) i ∧ g.f sk = king (g.f t) i ∧
    ∃ a : Axis, ∃ v : Fin 8, KRKFramedHistory.AllowedRay (g.f t) (g.f rs) i a v ∧
      FourthEntry s initial destination m wk t ⟨rs, g.r (a.target (g.f rs) v), none⟩ (g.r (reply (g.f t) i))

def InnerClear (s : RawTrace.State) (initial destination : Square) (m : Move) (g : Frame) (sk rs wk t : Square) : Prop :=
  KRKImmediate.MateNow (g.f sk) (g.f rs) (g.f t) ∨
    InnerKingPoints s initial destination m g sk rs wk t ∨ InnerRookRays s initial destination m g sk rs wk t

def WeakAfter (s : RawTrace.State) (initial destination : Square) (m : Move) (sk rs wk : Square) : Prop :=
  SafeRook sk rs wk ∧ RawClock.clock s.trace < 97 ∧
    firstOccurrences s initial destination (secondBoard s initial destination m) < 2 ∧
    ∀ t : Square, KRKCornerWeakBand.Guard sk rs wk t →
      secondOccurrences s initial destination m (thirdBoard s initial destination m wk t) < 2 ∧
        KRKEdgeDepth.depth t = 0 ∧ InnerClear s initial destination m (normalize t) sk rs wk t

def OuterKingPoints (s : RawTrace.State) (initial destination : Square) (sk rs wk : Square) : Prop :=
  let g := normalize wk
  ∃ i : KRKFourSlots.Kind, KRKFourSlots.Valid (g.f wk) i ∧ KRKFourSlots.Region (g.f wk) (g.f rs) i ∧
    dInf (g.f sk) (KRKFourSlots.king (g.f wk) i) = 1 ∧ KRKFourSlots.king (g.f wk) i ≠ g.f rs ∧
      2 ≤ dInf (KRKFourSlots.king (g.f wk) i) (g.f wk) ∧
      KRKFivePlyHistory.Live (g.r (KRKFourSlots.king (g.f wk) i)) rs wk ∧
      WeakAfter s initial destination ⟨sk,g.r (KRKFourSlots.king (g.f wk) i),none⟩ (g.r (KRKFourSlots.king (g.f wk) i)) rs wk

def OuterRookRays (s : RawTrace.State) (initial destination : Square) (sk rs wk : Square) : Prop :=
  let g := normalize wk
  ∃ i : KRKFourSlots.Kind, KRKFourSlots.Valid (g.f wk) i ∧ g.f sk = KRKFourSlots.king (g.f wk) i ∧
    ∃ a : KRKCornerSlotBarriers.Axis, ∃ v : Fin 8,
      RookSees (g.f rs) (a.target (g.f rs) v) (g.f sk) (g.f wk) ∧
      a.target (g.f rs) v ≠ g.f sk ∧ a.target (g.f rs) v ≠ g.f wk ∧
      KRKFourSlots.Region (g.f wk) (a.target (g.f rs) v) i ∧
      KRKFivePlyHistory.Live sk (g.r (a.target (g.f rs) v)) wk ∧
      WeakAfter s initial destination ⟨rs,g.r (a.target (g.f rs) v),none⟩ sk (g.r (a.target (g.f rs) v)) wk

def StrongClear (s : RawTrace.State) (initial destination : Square) (sk rs wk : Square) : Prop :=
  KRKImmediate.MateNow sk rs wk ∨
    (KRKEdgeDepth.depth wk = 0 ∧ (OuterKingPoints s initial destination sk rs wk ∨ OuterRookRays s initial destination sk rs wk))

theorem first_occurrences_eq {s : RawTrace.State} {initial destination : Square}
    (legal : isLegal (RawTrace.erase s) ⟨initial,destination,none⟩ = true) (q : Position) :
    RawRepetition.occurrences (RawTrace.append s ⟨initial,destination,none⟩ legal).trace q =
      firstOccurrences s initial destination q := by
  exact KRKStrongPrefix.occurrences_append legal q

theorem second_occurrences_eq {s : RawTrace.State} {initial destination : Square}
    (legal : isLegal (RawTrace.erase s) ⟨initial,destination,none⟩ = true) (m : Move) (q : Position) :
    KRKStrongPrefix.afterOccurrences (RawTrace.append s ⟨initial,destination,none⟩ legal) m q =
      secondOccurrences s initial destination m q := by
  classical
  unfold KRKStrongPrefix.afterOccurrences secondOccurrences
  rw [first_occurrences_eq legal]
  rfl

theorem fourth_entry_append_iff {s : RawTrace.State} {σ : Colour} {sk rs initial destination wk t u : Square}
    {m entry : Move} (material : IsKRK (RawTrace.erase s) σ sk rs initial)
    (turn : (RawTrace.erase s).turn = σ.opp) (safe : SafeRook sk rs initial)
    (legal : isLegal (RawTrace.erase s) ⟨initial,destination,none⟩ = true) :
    KRKStrongPrefix.OriginalEntryAfter (RawTrace.append s ⟨initial,destination,none⟩ legal) m wk t entry u ↔
      FourthEntry s initial destination m wk t entry u := by
  have quiet := weak_safe_quiet material turn safe legal
  unfold KRKStrongPrefix.OriginalEntryAfter FourthEntry
  rw [RawClock.append_clock,quiet]
  simp only [Bool.false_eq_true,↓reduceIte]
  rw [second_occurrences_eq legal,second_occurrences_eq legal]
  have boards : KRKStrongPrefix.firstAfter (RawTrace.append s ⟨initial,destination,none⟩ legal) m wk t =
      thirdBoard s initial destination m wk t := rfl
  rw [boards]
  change (RawClock.clock s.trace + 1 < 96 ∧ _) ↔ (RawClock.clock s.trace < 95 ∧ _)
  omega

theorem inner_clear_append_iff {s : RawTrace.State} {σ : Colour} {sk rs initial destination ns nr wk t : Square}
    {m : Move} (g : Frame) (material : IsKRK (RawTrace.erase s) σ sk rs initial)
    (turn : (RawTrace.erase s).turn = σ.opp) (safe : SafeRook sk rs initial)
    (legal : isLegal (RawTrace.erase s) ⟨initial,destination,none⟩ = true) :
    KRKStrongPrefix.Clear (RawTrace.append s ⟨initial,destination,none⟩ legal) m g ns nr wk t ↔
      InnerClear s initial destination m g ns nr wk t := by
  simp only [KRKStrongPrefix.Clear,InnerClear,KRKStrongPrefix.KingPoints,InnerKingPoints,
    KRKStrongPrefix.RookRays,InnerRookRays,fourth_entry_append_iff material turn safe legal]

theorem weak_after_append_iff {s : RawTrace.State} {σ : Colour} {sk rs initial destination ns nr wk : Square}
    {m : Move} (material : IsKRK (RawTrace.erase s) σ sk rs initial)
    (turn : (RawTrace.erase s).turn = σ.opp) (safe : SafeRook sk rs initial)
    (legal : isLegal (RawTrace.erase s) ⟨initial,destination,none⟩ = true) :
    KRKStrongPrefix.WeakAfter (RawTrace.append s ⟨initial,destination,none⟩ legal) m ns nr wk ↔
      WeakAfter s initial destination m ns nr wk := by
  have quiet := weak_safe_quiet material turn safe legal
  unfold KRKStrongPrefix.WeakAfter WeakAfter
  rw [RawClock.append_clock,quiet]
  simp only [Bool.false_eq_true,↓reduceIte]
  simp only [first_occurrences_eq legal,second_occurrences_eq legal,
    inner_clear_append_iff _ material turn safe legal]
  change (SafeRook ns nr wk ∧ RawClock.clock s.trace + 1 < 98 ∧ _ ∧ _) ↔ _
  constructor <;> rintro ⟨safe,time,count,branches⟩ <;> exact ⟨safe,by omega,count,branches⟩

theorem strong_clear_append_iff {s : RawTrace.State} {σ : Colour} {sk rs initial destination : Square}
    (material : IsKRK (RawTrace.erase s) σ sk rs initial)
    (turn : (RawTrace.erase s).turn = σ.opp) (safe : SafeRook sk rs initial)
    (legal : isLegal (RawTrace.erase s) ⟨initial,destination,none⟩ = true) :
    KRKFivePlyHistory.Clear (RawTrace.append s ⟨initial,destination,none⟩ legal) sk rs destination ↔
      StrongClear s initial destination sk rs destination := by
  simp only [KRKFivePlyHistory.Clear,StrongClear,KRKFivePlyHistory.KingPoints,OuterKingPoints,
    KRKFivePlyHistory.RookRays,OuterRookRays,weak_after_append_iff material turn safe legal]

end EndgameChess.Rules.KRKFiveWeakPrefix
