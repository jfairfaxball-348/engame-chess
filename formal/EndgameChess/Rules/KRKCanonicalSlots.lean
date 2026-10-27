import EndgameChess.Rules.KRKNativeFrame
import EndgameChess.Rules.KRKThreePlyCorner

namespace EndgameChess.Rules.KRKCanonicalSlots
open EndgameChess.KK KRKThreePly KRKLastReply
set_option maxHeartbeats 500000

inductive Kind where
  | cornerRank | cornerFile | nearEast | nearWest | nearInner | middleEast | middleWest

def left (wk : Square) : Fin 8 := ⟨wk.1.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) wk.1.isLt⟩
def right (wk : Square) : Fin 8 := ⟨min (wk.1.val + 1) 7, by omega⟩

def Valid (wk : Square) (i : Kind) : Prop := wk.2.val = 0 ∧
  match i with
  | .cornerRank | .cornerFile => wk.1.val = 0
  | .nearEast | .nearWest | .nearInner => wk.1.val = 1
  | .middleEast | .middleWest => 2 ≤ wk.1.val ∧ wk.1.val ≤ 3

def king (wk : Square) : Kind → Square
  | .cornerRank => (1, 2)
  | .cornerFile => (2, 1)
  | .nearEast => (2, 2)
  | .nearWest => (0, 2)
  | .nearInner => (1, 2)
  | .middleEast => (right wk, 2)
  | .middleWest => (left wk, 2)

def rookFile (wk : Square) : Kind → Fin 8
  | .nearEast => 0
  | .nearWest | .nearInner => 2
  | .middleEast => left wk
  | .middleWest => right wk
  | _ => 0

def lower : Kind → Nat
  | .nearInner => 1
  | _ => 2

def Region (wk : Square) (i : Kind) (rs : Square) : Prop :=
  match i with
  | .cornerRank => 3 ≤ rs.1.val ∧ 1 ≤ rs.2.val
  | .cornerFile => 1 ≤ rs.1.val ∧ 3 ≤ rs.2.val
  | _ => rs.1.val = (rookFile wk i).val ∧ lower i ≤ rs.2.val

def reply (wk : Square) : Kind → Square
  | .cornerFile => (0, 1)
  | .nearInner => (0, 0)
  | i => ((king wk i).1, 0)

theorem valid_bounds {wk : Square} {i : Kind} (valid : Valid wk i) :
    wk.2.val = 0 ∧ wk.1.val ≤ 3 := by
  cases i <;> dsimp [Valid] at valid <;> omega

/-- Seven finite slot kinds cover every canonical edge LastReply. Middle
slots depend on the weak file; their coordinates never wrap. -/
theorem last_catalogue_iff {sk rs wk : Square} (rank : wk.2.val = 0) (high : wk.1.val ≤ 3) :
    LastReply sk rs wk ↔ ∃ i : Kind, Valid wk i ∧ sk = king wk i ∧ Region wk i rs := by
  constructor
  · intro last
    by_cases corner : wk.1.val = 0
    · rcases (last_corner_iff corner rank).mp last with ⟨sx, sy, rx, ry⟩ | ⟨sx, sy, ry, rx⟩
      · exact ⟨.cornerRank, ⟨rank, corner⟩, Prod.ext (Fin.ext sx) (Fin.ext sy), rx, ry⟩
      · exact ⟨.cornerFile, ⟨rank, corner⟩, Prod.ext (Fin.ext sx) (Fin.ext sy), rx, ry⟩
    by_cases near : wk.1.val = 1
    · obtain ⟨sy, ⟨sx, rx, ry⟩ | ⟨sx, rx, ry⟩ | ⟨sx, rx, ry⟩⟩ := (last_near_iff near rank).mp last
      · exact ⟨.nearEast, ⟨rank, near⟩, Prod.ext (Fin.ext sx) (Fin.ext sy), rx, ry⟩
      · exact ⟨.nearWest, ⟨rank, near⟩, Prod.ext (Fin.ext sx) (Fin.ext sy), rx, ry⟩
      · exact ⟨.nearInner, ⟨rank, near⟩, Prod.ext (Fin.ext sx) (Fin.ext sy), rx, ry⟩
    have low : 2 ≤ wk.1.val := by omega
    obtain ⟨sy, ry, ⟨sx, rx⟩ | ⟨sx, rx⟩⟩ := (last_middle_iff rank low (by omega)).mp last
    · refine ⟨.middleEast, ⟨rank, low, high⟩, ?_, ?_⟩
      · apply Prod.ext <;> apply Fin.ext <;> dsimp [king, right] <;> omega
      · dsimp [Region, rookFile, left, lower]; exact ⟨by omega, ry⟩
    · refine ⟨.middleWest, ⟨rank, low, high⟩, ?_, ?_⟩
      · apply Prod.ext <;> apply Fin.ext <;> dsimp [king, left] <;> omega
      · dsimp [Region, rookFile, right, lower]; exact ⟨by omega, ry⟩
  · rintro ⟨i, valid, equal, region⟩
    subst sk
    cases i with
    | cornerRank =>
      exact (last_corner_iff valid.2 rank).mpr (Or.inl ⟨rfl, rfl, region.1, region.2⟩)
    | cornerFile =>
      exact (last_corner_iff valid.2 rank).mpr (Or.inr ⟨rfl, rfl, region.2, region.1⟩)
    | nearEast =>
      exact (last_near_iff valid.2 rank).mpr ⟨rfl, Or.inl ⟨rfl, region.1, region.2⟩⟩
    | nearWest =>
      exact (last_near_iff valid.2 rank).mpr ⟨rfl, Or.inr (Or.inl ⟨rfl, region.1, region.2⟩)⟩
    | nearInner =>
      exact (last_near_iff valid.2 rank).mpr ⟨rfl, Or.inr (Or.inr ⟨rfl, region.1, region.2⟩)⟩
    | middleEast =>
      have low : 2 ≤ wk.1.val := valid.2.1
      have top : wk.1.val ≤ 3 := valid.2.2
      apply (last_middle_iff rank valid.2.1 (by omega)).mpr
      dsimp [king, right, Region, rookFile, left, lower] at region ⊢
      exact ⟨rfl, region.2, Or.inl ⟨by omega, by omega⟩⟩
    | middleWest =>
      have low : 2 ≤ wk.1.val := valid.2.1
      have top : wk.1.val ≤ 3 := valid.2.2
      apply (last_middle_iff rank valid.2.1 (by omega)).mpr
      dsimp [king, left, Region, rookFile, right, lower] at region ⊢
      exact ⟨rfl, region.2, Or.inr ⟨by omega, by omega⟩⟩

theorem slot_last {wk rs : Square} {i : Kind} (valid : Valid wk i) (region : Region wk i rs) :
    LastReply (king wk i) rs wk :=
  (last_catalogue_iff (valid_bounds valid).1 (valid_bounds valid).2).mpr ⟨i, valid, rfl, region⟩

theorem king_far {wk : Square} {i : Kind} (valid : Valid wk i) : 2 ≤ dInf (king wk i) wk := by
  cases i <;> dsimp [Valid, king, left, right] at valid ⊢ <;>
    simp only [dInf, absDiff] <;> omega

theorem reply_distance {wk : Square} {i : Kind} (valid : Valid wk i) : dInf wk (reply wk i) = 1 := by
  cases i <;> dsimp [Valid, reply, king, left, right] at valid ⊢ <;>
    simp only [dInf, absDiff] <;> omega

theorem reply_far {wk : Square} {i : Kind} (valid : Valid wk i) :
    2 ≤ dInf (king wk i) (reply wk i) := by
  cases i <;> dsimp [king, reply] <;> simp only [dInf, absDiff] <;> omega

theorem region_off_reply {wk rs : Square} {i : Kind} (valid : Valid wk i) (region : Region wk i rs) :
    rs.1.val ≠ (reply wk i).1.val ∧ rs.2.val ≠ (reply wk i).2.val := by
  cases i <;> dsimp [Valid, Region, reply, king, rookFile, lower, left, right] at valid region ⊢ <;> omega

theorem reply_step {wk rs : Square} {i : Kind} (valid : Valid wk i) (region : Region wk i rs) :
    StepM ⟨king wk i, rs, wk, false⟩ ⟨king wk i, rs, reply wk i, true⟩ := by
  have off := region_off_reply valid region
  refine StepM.lone (reply_distance valid) ?_ (reply_far valid) ?_
  · rw [ne_iff_coords]; omega
  · intro sees
    exact sees.1.2.elim off.1 off.2

theorem region_off_weak {wk rs : Square} {i : Kind} (valid : Valid wk i) (region : Region wk i rs) :
    rs.1.val ≠ wk.1.val ∧ 1 ≤ rs.2.val := by
  cases i <;> dsimp [Valid, Region, rookFile, lower, left, right] at valid region ⊢ <;> omega

end EndgameChess.Rules.KRKCanonicalSlots
