import EndgameChess.Rules.KRKSevenPlyHistory

namespace EndgameChess.Rules.KRKEightPrefix
open EndgameChess.KK KRKThreePly KRKLastReply KRKOppositionHistory KRKNativeFrame KRKCanonicalSlots
open KRKCornerSlotBarriers (Axis)
set_option maxHeartbeats 400000

def prefixBoard (s : RawTrace.State) (firstInitial firstDest : Square) : Position :=
  play (RawTrace.erase s) ⟨firstInitial,firstDest,none⟩

noncomputable def prefixOccurrences (s : RawTrace.State) (firstInitial firstDest : Square) (q : Position) : Nat :=
  RawRepetition.occurrences s.trace q +
    (by classical exact if RawRepetition.key (prefixBoard s firstInitial firstDest) = RawRepetition.key q then 1 else 0)

def rootBoard (s : RawTrace.State) (firstInitial firstDest : Square) (root : Move) : Position :=
  play (prefixBoard s firstInitial firstDest) root

noncomputable def rootOccurrences (s : RawTrace.State) (firstInitial firstDest : Square) (root : Move) (q : Position) : Nat :=
  prefixOccurrences s firstInitial firstDest q +
    (by classical exact if RawRepetition.key (rootBoard s firstInitial firstDest root) = RawRepetition.key q then 1 else 0)

def weakBoard (s : RawTrace.State) (firstInitial firstDest : Square) (root : Move) (initial destination : Square) : Position :=
  play (rootBoard s firstInitial firstDest root) ⟨initial,destination,none⟩

noncomputable def firstOccurrences (s : RawTrace.State) (firstInitial firstDest : Square) (root : Move) (initial destination : Square) (q : Position) : Nat :=
  rootOccurrences s firstInitial firstDest root q +
    (by classical exact if RawRepetition.key (weakBoard s firstInitial firstDest root initial destination) = RawRepetition.key q then 1 else 0)

def secondBoard (s : RawTrace.State) (firstInitial firstDest : Square) (root : Move) (initial destination : Square) (m : Move) : Position := play (weakBoard s firstInitial firstDest root initial destination) m

noncomputable def secondOccurrences (s : RawTrace.State) (firstInitial firstDest : Square) (root : Move) (initial destination : Square) (m : Move) (q : Position) : Nat :=
  firstOccurrences s firstInitial firstDest root initial destination q +
    (by classical exact if RawRepetition.key (secondBoard s firstInitial firstDest root initial destination m) = RawRepetition.key q then 1 else 0)

def thirdBoard (s : RawTrace.State) (firstInitial firstDest : Square) (root : Move) (initial destination : Square) (m : Move) (wk t : Square) : Position :=
  play (secondBoard s firstInitial firstDest root initial destination m) ⟨wk,t,none⟩

def FourthEntry (s : RawTrace.State) (firstInitial firstDest : Square) (root : Move) (initial destination : Square) (m : Move) (wk t : Square) (entry : Move) (u : Square) : Prop :=
  RawClock.clock s.trace < 93 ∧
    secondOccurrences s firstInitial firstDest root initial destination m (play (thirdBoard s firstInitial firstDest root initial destination m wk t) entry) < 2 ∧
    secondOccurrences s firstInitial firstDest root initial destination m (play (play (thirdBoard s firstInitial firstDest root initial destination m wk t) entry) ⟨t,u,none⟩) < 2

def InnerKingPoints (s : RawTrace.State) (firstInitial firstDest : Square) (root : Move) (initial destination : Square) (m : Move) (g : Frame) (sk rs wk t : Square) : Prop :=
  ∃ i : Kind, Valid (g.f t) i ∧ Region (g.f t) i (g.f rs) ∧
    dInf (g.f sk) (king (g.f t) i) = 1 ∧
      FourthEntry s firstInitial firstDest root initial destination m wk t ⟨sk, g.r (king (g.f t) i), none⟩ (g.r (reply (g.f t) i))

def InnerRookRays (s : RawTrace.State) (firstInitial firstDest : Square) (root : Move) (initial destination : Square) (m : Move) (g : Frame) (sk rs wk t : Square) : Prop :=
  ∃ i : Kind, Valid (g.f t) i ∧ g.f sk = king (g.f t) i ∧
    ∃ a : Axis, ∃ v : Fin 8, KRKFramedHistory.AllowedRay (g.f t) (g.f rs) i a v ∧
      FourthEntry s firstInitial firstDest root initial destination m wk t ⟨rs, g.r (a.target (g.f rs) v), none⟩ (g.r (reply (g.f t) i))

def InnerClear (s : RawTrace.State) (firstInitial firstDest : Square) (root : Move) (initial destination : Square) (m : Move) (g : Frame) (sk rs wk t : Square) : Prop :=
  KRKImmediate.MateNow (g.f sk) (g.f rs) (g.f t) ∨
    InnerKingPoints s firstInitial firstDest root initial destination m g sk rs wk t ∨ InnerRookRays s firstInitial firstDest root initial destination m g sk rs wk t

def WeakAfter (s : RawTrace.State) (firstInitial firstDest : Square) (root : Move) (initial destination : Square) (m : Move) (sk rs wk : Square) : Prop :=
  SafeRook sk rs wk ∧ RawClock.clock s.trace < 95 ∧
    firstOccurrences s firstInitial firstDest root initial destination (secondBoard s firstInitial firstDest root initial destination m) < 2 ∧
    ∀ t : Square, KRKCornerWeakBand.Guard sk rs wk t →
      secondOccurrences s firstInitial firstDest root initial destination m (thirdBoard s firstInitial firstDest root initial destination m wk t) < 2 ∧
        KRKEdgeDepth.depth t = 0 ∧ InnerClear s firstInitial firstDest root initial destination m (normalize t) sk rs wk t

def OuterKingPoints (s : RawTrace.State) (firstInitial firstDest : Square) (root : Move) (initial destination : Square) (sk rs wk : Square) : Prop :=
  let g := normalize wk
  ∃ i : KRKFourSlots.Kind, KRKFourSlots.Valid (g.f wk) i ∧ KRKFourSlots.Region (g.f wk) (g.f rs) i ∧
    dInf (g.f sk) (KRKFourSlots.king (g.f wk) i) = 1 ∧ KRKFourSlots.king (g.f wk) i ≠ g.f rs ∧
      2 ≤ dInf (KRKFourSlots.king (g.f wk) i) (g.f wk) ∧
      KRKFivePlyHistory.Live (g.r (KRKFourSlots.king (g.f wk) i)) rs wk ∧
      WeakAfter s firstInitial firstDest root initial destination ⟨sk,g.r (KRKFourSlots.king (g.f wk) i),none⟩ (g.r (KRKFourSlots.king (g.f wk) i)) rs wk

def OuterRookRays (s : RawTrace.State) (firstInitial firstDest : Square) (root : Move) (initial destination : Square) (sk rs wk : Square) : Prop :=
  let g := normalize wk
  ∃ i : KRKFourSlots.Kind, KRKFourSlots.Valid (g.f wk) i ∧ g.f sk = KRKFourSlots.king (g.f wk) i ∧
    ∃ a : KRKCornerSlotBarriers.Axis, ∃ v : Fin 8,
      RookSees (g.f rs) (a.target (g.f rs) v) (g.f sk) (g.f wk) ∧
      a.target (g.f rs) v ≠ g.f sk ∧ a.target (g.f rs) v ≠ g.f wk ∧
      KRKFourSlots.Region (g.f wk) (a.target (g.f rs) v) i ∧
      KRKFivePlyHistory.Live sk (g.r (a.target (g.f rs) v)) wk ∧
      WeakAfter s firstInitial firstDest root initial destination ⟨rs,g.r (a.target (g.f rs) v),none⟩ sk (g.r (a.target (g.f rs) v)) wk

def StrongClear (s : RawTrace.State) (firstInitial firstDest : Square) (root : Move) (initial destination : Square) (sk rs wk : Square) : Prop :=
  KRKImmediate.MateNow sk rs wk ∨
    (KRKEdgeDepth.depth wk = 0 ∧ (OuterKingPoints s firstInitial firstDest root initial destination sk rs wk ∨ OuterRookRays s firstInitial firstDest root initial destination sk rs wk))

def SixAfter (s : RawTrace.State) (firstInitial firstDest : Square) (root : Move) (sk rs wk : Square) : Prop :=
  SafeRook sk rs wk ∧ RawClock.clock s.trace < 97 ∧
    prefixOccurrences s firstInitial firstDest (rootBoard s firstInitial firstDest root) < 2 ∧
    ∀ t, KRKCornerWeakBand.Guard sk rs wk t →
      rootOccurrences s firstInitial firstDest root (weakBoard s firstInitial firstDest root wk t) < 2 ∧
        StrongClear s firstInitial firstDest root wk t sk rs t

theorem prefix_occurrences_eq {s : RawTrace.State} {firstInitial firstDest : Square}
    (legal : isLegal (RawTrace.erase s) ⟨firstInitial,firstDest,none⟩ = true) (q : Position) :
    RawRepetition.occurrences (RawTrace.append s ⟨firstInitial,firstDest,none⟩ legal).trace q =
      prefixOccurrences s firstInitial firstDest q := by
  exact KRKStrongPrefix.occurrences_append legal q

theorem root_occurrences_eq {s : RawTrace.State} {firstInitial firstDest : Square} {root : Move}
    (legal : isLegal (RawTrace.erase s) ⟨firstInitial,firstDest,none⟩ = true) (q : Position) :
    KRKStrongPrefix.afterOccurrences (RawTrace.append s ⟨firstInitial,firstDest,none⟩ legal) root q =
      rootOccurrences s firstInitial firstDest root q := by
  classical
  unfold KRKStrongPrefix.afterOccurrences rootOccurrences
  rw [prefix_occurrences_eq legal]
  rfl

theorem first_occurrences_eq {s : RawTrace.State} {firstInitial firstDest initial destination : Square} {root : Move}
    (legal : isLegal (RawTrace.erase s) ⟨firstInitial,firstDest,none⟩ = true) (q : Position) :
    KRKSevenPrefix.firstOccurrences (RawTrace.append s ⟨firstInitial,firstDest,none⟩ legal) root initial destination q =
      firstOccurrences s firstInitial firstDest root initial destination q := by
  classical
  unfold KRKSevenPrefix.firstOccurrences firstOccurrences
  rw [root_occurrences_eq legal]
  rfl

theorem second_occurrences_eq {s : RawTrace.State} {firstInitial firstDest initial destination : Square} {root m : Move}
    (legal : isLegal (RawTrace.erase s) ⟨firstInitial,firstDest,none⟩ = true) (q : Position) :
    KRKSevenPrefix.secondOccurrences (RawTrace.append s ⟨firstInitial,firstDest,none⟩ legal) root initial destination m q =
      secondOccurrences s firstInitial firstDest root initial destination m q := by
  classical
  unfold KRKSevenPrefix.secondOccurrences secondOccurrences
  rw [first_occurrences_eq legal]
  rfl

theorem fourth_entry_weak_iff {s : RawTrace.State} {σ : Colour}
    {sk rs rootWeak firstInitial firstDest initial destination wk t u : Square} {root m entry : Move}
    (material : IsKRK (RawTrace.erase s) σ sk rs rootWeak) (turn : (RawTrace.erase s).turn = σ.opp)
    (safe : SafeRook sk rs rootWeak) (legal : isLegal (RawTrace.erase s) ⟨firstInitial,firstDest,none⟩ = true) :
    KRKSevenPrefix.FourthEntry (RawTrace.append s ⟨firstInitial,firstDest,none⟩ legal) root initial destination m wk t entry u ↔
      FourthEntry s firstInitial firstDest root initial destination m wk t entry u := by
  have quiet := KRKLastReply.weak_safe_quiet material turn safe legal
  unfold KRKSevenPrefix.FourthEntry FourthEntry
  rw [RawClock.append_clock,quiet]
  simp only [Bool.false_eq_true,↓reduceIte,second_occurrences_eq legal]
  have boards : KRKSevenPrefix.thirdBoard (RawTrace.append s ⟨firstInitial,firstDest,none⟩ legal) root initial destination m wk t =
      thirdBoard s firstInitial firstDest root initial destination m wk t := rfl
  rw [boards]
  change (RawClock.clock s.trace + 1 < 94 ∧ _) ↔ (RawClock.clock s.trace < 93 ∧ _)
  omega

theorem inner_clear_weak_iff {s : RawTrace.State} {σ : Colour}
    {sk rs rootWeak firstInitial firstDest initial destination ns nr wk t : Square} {root m : Move}
    (g : Frame) (material : IsKRK (RawTrace.erase s) σ sk rs rootWeak) (turn : (RawTrace.erase s).turn = σ.opp)
    (safe : SafeRook sk rs rootWeak) (legal : isLegal (RawTrace.erase s) ⟨firstInitial,firstDest,none⟩ = true) :
    KRKSevenPrefix.InnerClear (RawTrace.append s ⟨firstInitial,firstDest,none⟩ legal) root initial destination m g ns nr wk t ↔
      InnerClear s firstInitial firstDest root initial destination m g ns nr wk t := by
  simp only [KRKSevenPrefix.InnerClear,InnerClear,KRKSevenPrefix.InnerKingPoints,InnerKingPoints,
    KRKSevenPrefix.InnerRookRays,InnerRookRays,fourth_entry_weak_iff material turn safe legal]

theorem weak_after_weak_iff {s : RawTrace.State} {σ : Colour}
    {sk rs rootWeak firstInitial firstDest initial destination ns nr wk : Square} {root m : Move}
    (material : IsKRK (RawTrace.erase s) σ sk rs rootWeak) (turn : (RawTrace.erase s).turn = σ.opp)
    (safe : SafeRook sk rs rootWeak) (legal : isLegal (RawTrace.erase s) ⟨firstInitial,firstDest,none⟩ = true) :
    KRKSevenPrefix.WeakAfter (RawTrace.append s ⟨firstInitial,firstDest,none⟩ legal) root initial destination m ns nr wk ↔
      WeakAfter s firstInitial firstDest root initial destination m ns nr wk := by
  have quiet := KRKLastReply.weak_safe_quiet material turn safe legal
  unfold KRKSevenPrefix.WeakAfter WeakAfter
  rw [RawClock.append_clock,quiet]
  simp only [Bool.false_eq_true,↓reduceIte,first_occurrences_eq legal,second_occurrences_eq legal,
    inner_clear_weak_iff _ material turn safe legal]
  change (SafeRook ns nr wk ∧ RawClock.clock s.trace + 1 < 96 ∧ _) ↔
    (SafeRook ns nr wk ∧ RawClock.clock s.trace < 95 ∧ _)
  constructor <;> rintro ⟨a,b,c,d⟩ <;> exact ⟨a,by omega,c,d⟩

theorem strong_clear_weak_iff {s : RawTrace.State} {σ : Colour}
    {sk rs rootWeak firstInitial firstDest initial destination ns nr : Square} {root : Move}
    (material : IsKRK (RawTrace.erase s) σ sk rs rootWeak) (turn : (RawTrace.erase s).turn = σ.opp)
    (safe : SafeRook sk rs rootWeak) (legal : isLegal (RawTrace.erase s) ⟨firstInitial,firstDest,none⟩ = true) :
    KRKSevenPrefix.StrongClear (RawTrace.append s ⟨firstInitial,firstDest,none⟩ legal) root initial destination ns nr destination ↔
      StrongClear s firstInitial firstDest root initial destination ns nr destination := by
  simp only [KRKSevenPrefix.StrongClear,StrongClear,KRKSevenPrefix.OuterKingPoints,OuterKingPoints,
    KRKSevenPrefix.OuterRookRays,OuterRookRays,weak_after_weak_iff material turn safe legal]

theorem six_after_weak_iff {s : RawTrace.State} {σ : Colour}
    {sk rs rootWeak firstInitial firstDest ns nr wk : Square} {root : Move}
    (material : IsKRK (RawTrace.erase s) σ sk rs rootWeak) (turn : (RawTrace.erase s).turn = σ.opp)
    (safe : SafeRook sk rs rootWeak) (legal : isLegal (RawTrace.erase s) ⟨firstInitial,firstDest,none⟩ = true) :
    KRKSevenPrefix.SixAfter (RawTrace.append s ⟨firstInitial,firstDest,none⟩ legal) root ns nr wk ↔
      SixAfter s firstInitial firstDest root ns nr wk := by
  have quiet := KRKLastReply.weak_safe_quiet material turn safe legal
  unfold KRKSevenPrefix.SixAfter SixAfter
  rw [RawClock.append_clock,quiet]
  simp only [Bool.false_eq_true,↓reduceIte,prefix_occurrences_eq legal,root_occurrences_eq legal,
    strong_clear_weak_iff material turn safe legal]
  have rootEq : KRKStrongPrefix.afterBoard (RawTrace.append s ⟨firstInitial,firstDest,none⟩ legal) root =
      rootBoard s firstInitial firstDest root := rfl
  have weakEq : ∀ t, KRKSevenPrefix.weakBoard (RawTrace.append s ⟨firstInitial,firstDest,none⟩ legal) root wk t =
      weakBoard s firstInitial firstDest root wk t := fun _ => rfl
  simp only [rootEq,weakEq]
  constructor <;> rintro ⟨a,b,c,d⟩ <;> exact ⟨a,by omega,c,d⟩

def KingEntries (s : RawTrace.State) (firstInitial firstDest : Square) (sk rs wk : Square) : Prop :=
  let g := KRKSevenSlots.frame wk
  ∃ i : KRKSevenSlots.Kind, dInf (g.f sk) (KRKSevenSlots.point i) = 1 ∧ KRKSevenSlots.point i ≠ g.f rs ∧
    2 ≤ dInf (KRKSevenSlots.point i) (g.f wk) ∧ KRKSixGlobal.Region (g.r (KRKSevenSlots.point i)) rs wk ∧
      KRKSevenPlyHistory.Live (g.r (KRKSevenSlots.point i)) rs wk ∧
      SixAfter s firstInitial firstDest ⟨sk,g.r (KRKSevenSlots.point i),none⟩ (g.r (KRKSevenSlots.point i)) rs wk

def RookEntries (s : RawTrace.State) (firstInitial firstDest : Square) (sk rs wk : Square) : Prop :=
  let g := KRKSevenSlots.frame wk
  ∃ i : KRKSevenSlots.Kind, g.f sk = KRKSevenSlots.point i ∧ ∃ a : Axis, ∃ v : Fin 8,
    RookSees (g.f rs) (a.target (g.f rs) v) (g.f sk) (g.f wk) ∧ a.target (g.f rs) v ≠ g.f sk ∧ a.target (g.f rs) v ≠ g.f wk ∧
    KRKSixGlobal.Region sk (g.r (a.target (g.f rs) v)) wk ∧ KRKSevenPlyHistory.Live sk (g.r (a.target (g.f rs) v)) wk ∧
    SixAfter s firstInitial firstDest ⟨rs,g.r (a.target (g.f rs) v),none⟩ sk (g.r (a.target (g.f rs) v)) wk

def SevenAfterWeak (s : RawTrace.State) (firstInitial firstDest : Square) (sk rs wk : Square) : Prop :=
  KRKImmediate.MateNow sk rs wk ∨ KingEntries s firstInitial firstDest sk rs wk ∨ RookEntries s firstInitial firstDest sk rs wk

theorem seven_append_iff {s : RawTrace.State} {σ : Colour} {sk rs initial destination : Square}
    (material : IsKRK (RawTrace.erase s) σ sk rs initial) (turn : (RawTrace.erase s).turn = σ.opp)
    (safe : SafeRook sk rs initial) (legal : isLegal (RawTrace.erase s) ⟨initial,destination,none⟩ = true) :
    KRKSevenPlyHistory.Clear (RawTrace.append s ⟨initial,destination,none⟩ legal) sk rs destination ↔
      SevenAfterWeak s initial destination sk rs destination := by
  simp only [KRKSevenPlyHistory.Clear,SevenAfterWeak,KRKSevenPlyHistory.KingPoints,KingEntries,
    KRKSevenPlyHistory.RookRays,RookEntries,six_after_weak_iff material turn safe legal]

end EndgameChess.Rules.KRKEightPrefix
