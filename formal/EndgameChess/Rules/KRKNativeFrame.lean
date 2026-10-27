import EndgameChess.Rules.KRKGeometricSymmetry
import EndgameChess.Rules.KRKEdgeDepth

namespace EndgameChess.Rules.KRKNativeFrame
open EndgameChess.KK KRKLastReply KRKImmediate
set_option maxHeartbeats 300000

/-- A geometric coordinate frame, with a separate inverse. No positions,
rights, clocks, traces or keys are transformed by this structure. -/
structure Frame where
  f : Square → Square
  r : Square → Square
  left_inv : ∀ s, r (f s) = s
  right_inv : ∀ s, f (r s) = s
  distance : ∀ s t, dInf (f s) (f t) = dInf s t
  sees : ∀ rs t sk wk, RookSees (f rs) (f t) (f sk) (f wk) ↔ RookSees rs t sk wk
  last : ∀ sk rs wk, LastReply (f sk) (f rs) (f wk) ↔ LastReply sk rs wk
  immediate : ∀ sk rs wk, MateNow (f sk) (f rs) (f wk) ↔ MateNow sk rs wk

def Frame.ofSym (g : BoardSym) : Frame where
  f := g.f
  r := g.f
  left_inv := g.invol
  right_inv := g.invol
  distance := g.dInf_eq
  sees := g.sees_iff
  last _ _ _ := KRKGeometricSymmetry.last_map_iff g
  immediate _ _ _ := KRKGeometricSymmetry.immediate_map_iff g

/-- Apply a first frame, then a second. The inverse order is reversed. -/
def Frame.comp (a b : Frame) : Frame where
  f s := b.f (a.f s)
  r s := a.r (b.r s)
  left_inv s := by simp only [b.left_inv, a.left_inv]
  right_inv s := by simp only [a.right_inv, b.right_inv]
  distance s t := by rw [b.distance, a.distance]
  sees _ _ _ _ := (b.sees _ _ _ _).trans (a.sees _ _ _ _)
  last _ _ _ := (b.last _ _ _).trans (a.last _ _ _)
  immediate _ _ _ := (b.immediate _ _ _).trans (a.immediate _ _ _)

theorem Frame.eq_iff (a : Frame) {s t : Square} : a.f s = a.f t ↔ s = t := by
  constructor
  · intro equal
    simpa only [a.left_inv] using congrArg a.r equal
  · intro equal; rw [equal]

theorem Frame.ne_iff (a : Frame) {s t : Square} : a.f s ≠ a.f t ↔ s ≠ t :=
  not_congr a.eq_iff

theorem Frame.preimage_eq (a : Frame) {s t : Square} (equal : a.f s = t) : s = a.r t := by
  simpa only [a.left_inv] using congrArg a.r equal

def Frame.inverse (a : Frame) : Frame where
  f := a.r
  r := a.f
  left_inv := a.right_inv
  right_inv := a.left_inv
  distance s t := by simpa only [a.right_inv] using (a.distance (a.r s) (a.r t)).symm
  sees rs t sk wk := by
    simpa only [a.right_inv] using (a.sees (a.r rs) (a.r t) (a.r sk) (a.r wk)).symm
  last sk rs wk := by
    simpa only [a.right_inv] using (a.last (a.r sk) (a.r rs) (a.r wk)).symm
  immediate sk rs wk := by
    simpa only [a.right_inv] using (a.immediate (a.r sk) (a.r rs) (a.r wk)).symm

def Frame.mapState (a : Frame) (s : KRKState) : KRKState :=
  ⟨a.f s.sk, a.f s.rs, a.f s.wk, s.strong⟩

theorem Frame.map_step (a : Frame) {s t : KRKState} (step : StepM s t) :
    StepM (a.mapState s) (a.mapState t) := by
  cases step with
  | rook line notKing notWeak apartKing apartWeak far =>
    have ray := (a.sees _ _ _ _).mpr ⟨line, notKing, notWeak⟩
    exact StepM.rook ray.1 ray.2.1 ray.2.2 (a.ne_iff.mpr apartKing) (a.ne_iff.mpr apartWeak)
      (by rwa [a.distance])
  | king distance apart far =>
    exact StepM.king (by rwa [a.distance]) (a.ne_iff.mpr apart) (by rwa [a.distance])
  | lone distance apart far notSeen =>
    exact StepM.lone (by rwa [a.distance]) (a.ne_iff.mpr apart) (by rwa [a.distance])
      (fun seen => notSeen ((a.sees _ _ _ _).mp seen))

theorem Frame.map_inverse (a : Frame) (s : KRKState) : a.inverse.mapState (a.mapState s) = s := by
  cases s
  simp only [Frame.mapState, Frame.inverse, a.left_inv]

def bottomFrame (wk : Square) : Frame :=
  if wk.2.val = 0 then Frame.ofSym symId
  else if wk.2.val = 7 then Frame.ofSym symY
  else if wk.1.val = 0 then Frame.ofSym symSwap
  else (Frame.ofSym symSwap).comp (Frame.ofSym symY)

theorem bottomFrame_spec {wk : Square} (edge : KRKEdgeDepth.depth wk = 0) :
    ((bottomFrame wk).f wk).2.val = 0 := by
  have boundary : wk.2.val = 0 ∨ wk.2.val = 7 ∨ wk.1.val = 0 ∨ wk.1.val = 7 := by
    simp only [KRKEdgeDepth.depth] at edge
    omega
  by_cases bottom : wk.2.val = 0
  · simp [bottomFrame, bottom, Frame.ofSym, symId]
  by_cases top : wk.2.val = 7
  · simp [bottomFrame, bottom, top, Frame.ofSym, symY]
  by_cases left : wk.1.val = 0
  · simp [bottomFrame, bottom, top, left, Frame.ofSym, symSwap]
  · have right : wk.1.val = 7 := by omega
    simp [bottomFrame, bottom, top, left, right, Frame.comp, Frame.ofSym, symSwap, symY]

/-- Deterministic normalization of an edge square to files zero through
three on rank zero. Only coordinates, never the incoming game, are mapped. -/
def normalize (wk : Square) : Frame :=
  let b := bottomFrame wk
  if (b.f wk).1.val ≤ 3 then b else b.comp (Frame.ofSym symX)

theorem normalize_spec {wk : Square} (edge : KRKEdgeDepth.depth wk = 0) :
    ((normalize wk).f wk).2.val = 0 ∧ ((normalize wk).f wk).1.val ≤ 3 := by
  have bottom := bottomFrame_spec edge
  dsimp only [normalize]
  split
  · rename_i small
    exact ⟨bottom, small⟩
  · rename_i large
    constructor
    · exact bottom
    · change 7 - ((bottomFrame wk).f wk).1.val ≤ 3
      omega

end EndgameChess.Rules.KRKNativeFrame
