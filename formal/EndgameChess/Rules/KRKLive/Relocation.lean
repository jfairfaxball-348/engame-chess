import EndgameChess.Rules.KRKLive.Reply

/-!
# EC-C008 relocation — Lemma P1 (S022)

Formalisation of rule P1 (§3) and Lemma P1 (§4b) of `proofs/EC-C008_KRK_LIVE.md` in the KRK
move model of `Rules.KRKLive.Basic`, using the reply lemmas RL-h and RL-f of
`Rules.KRKLive.Reply` and the end-game half (Lemma S) of `Rules.KRKLive.Endgame`.

- `RookInv sk rs wk`: the invariant of a strong-to-move state during P1 — `S` normalised,
  the kings apart, the lone king not seen by the rook (prose facts (ii)/(iii)).
- `rook_move_ok`: a rook move whose segment and target avoid `S` avoids `L` too (prose (ii),
  via `shield_of_line` and `onSeg_trans`).
- `after_rook`: a rook move, then a free reply (or a mate); the route continues from **every**
  state satisfying `RookInv`, which every free reply restores (`rookInv_of_free`).
- The P1 branches: `krk_home` (rook on h8: Lemma S); `krk_hfile` (rook on the h-file);
  `krk_rankToH` (HV, and "direct" from rank 8); `krk_fs` (file shift F1/F2/F3); and the
  combined `krk_P1`.

**Reply choice.** The prose lets the lone king play *any* non-capturing legal reply. The
model is cooperative (`WinM` is existential), so one reply is chosen; since the
continuation is proved for every state satisfying `RookInv`, the choice does not matter.
-/

namespace EndgameChess.Rules

set_option linter.unusedSimpArgs false

open EndgameChess.KK

/-- Invariant of strong-to-move states in P1. -/
def RookInv (sk rs wk : Square) : Prop :=
  Normal sk ∧ sk ≠ rs ∧ 2 ≤ dInf sk wk ∧ rs ≠ wk ∧ ¬ RookSees rs wk sk wk

theorem rookInv_of_free {sk r wk t : Square} (hn : Normal sk) (hsr : sk ≠ r)
    (h : Free sk r wk t) : RookInv sk r t :=
  ⟨hn, hsr, h.2.2.1, Ne.symm h.2.1, h.2.2.2⟩

theorem onSeg_trans {r a b c : Square} (h1 : OnSeg r a b) (h2 : OnSeg r b c) :
    OnSeg r a c := by
  simp only [OnSeg] at *; omega

theorem rookLine_of_onSeg {r b c : Square} (h : OnSeg r b c) : RookLine r b := by
  simp only [OnSeg, RookLine] at *; omega

/-- Prose (ii): a lone king on a rook line, not seen by the rook, is shielded by `S`. -/
theorem shield_of_line {sk rs wk : Square} (hns : ¬ RookSees rs wk sk wk)
    (hl : RookLine rs wk) : OnSeg rs sk wk :=
  (Classical.em _).elim id fun hc => absurd ⟨hl, hc, not_onSeg_end _ _⟩ hns

/-- A rook move along a line whose segment and target avoid `S` also avoids the lone king,
when the rook does not see it. -/
theorem rook_move_ok {sk rs wk t : Square} (hns : ¬ RookSees rs wk sk wk)
    (hl : RookLine rs t) (hs : ¬ OnSeg rs sk t) : ¬ OnSeg rs wk t ∧ t ≠ wk := by
  refine ⟨fun h => hs (onSeg_trans (shield_of_line hns (rookLine_of_onSeg h)) h), ?_⟩
  rintro rfl
  exact hns ⟨hl, hs, not_onSeg_end _ _⟩

/-- A rook move followed by a free reply (or a mate), continued from every state satisfying
the invariant. -/
theorem after_rook {sk rs wk r : Square} (hI : RookInv sk rs wk) (hl : RookLine rs r)
    (hs : ¬ OnSeg rs sk r) (hrs : r ≠ sk) (hok : LoneOK sk r wk)
    (hk : ∀ t, RookInv sk r t → WinM ⟨sk, r, t, true⟩) : WinM ⟨sk, rs, wk, true⟩ := by
  obtain ⟨hn, _, hfar, _, hns⟩ := hI
  obtain ⟨hw1, hw2⟩ := rook_move_ok hns hl hs
  refine winM_of_step (StepM.rook hl hs hw1 hrs hw2 hfar) ?_
  rcases hok with ⟨t, ht⟩ | hm
  · exact winM_of_step (StepM.lone ht.1 ht.2.1 ht.2.2.1 ht.2.2.2)
      (hk t (rookInv_of_free hn (Ne.symm hrs) ht))
  · exact winM_of_mate hm

/-! ## The branches of P1 -/

/-- **Home:** the rook on h8 — Lemma S. -/
theorem krk_home {sk wk : Square} (hI : RookInv sk sqH8 wk) : WinM ⟨sk, sqH8, wk, true⟩ :=
  krk_lemmaS hI.1 hI.2.2.1 (Ne.symm hI.2.2.2.1) hI.2.2.2.2

/-- **The rook on the h-file:** `R → h8` (the h-file is clear: `L` is not on it, by (ii)),
a reply by RL-h (the exception needs the rook on h7, not h8), then home. -/
theorem krk_hfile {sk rs wk : Square} (hI : RookInv sk rs wk) (hr : rs.1.val = 7) :
    WinM ⟨sk, rs, wk, true⟩ := by
  by_cases h8 : rs.2.val = 7
  · have : rs = sqH8 := by rw [square_eq_iff]; exact ⟨hr, h8⟩
    subst this; exact krk_home hI
  have hI' := hI
  obtain ⟨hn, _, hfar, _, hns⟩ := hI
  have hn1 := hn.1
  have hl : RookLine rs sqH8 := by simp only [RookLine, sqH8]; omega
  have hs : ¬ OnSeg rs sk sqH8 := by simp only [OnSeg, sqH8]; omega
  have hsk : sqH8 ≠ sk := by rw [ne_iff_coords]; simp only [sqH8]; omega
  exact after_rook hI' hl hs hsk (krk_RLh hn rfl (rook_move_ok hns hl hs).2 hfar
    (by simp only [HExc, sqH8]; omega)) (fun t ht => krk_home ht)

/-- **HV and direct.** `S` is not on the rook's rank between the rook and the h-file, and the
position is not the exception: `R → (h, ry)`, a reply by RL-h, then the h-file case. -/
theorem krk_rankToH {sk rs wk : Square} (hI : RookInv sk rs wk)
    (hS : ¬ (sk.2.val = rs.2.val ∧ rs.1.val < sk.1.val)) (hE : ¬ HExc sk rs wk) :
    WinM ⟨sk, rs, wk, true⟩ := by
  by_cases h7 : rs.1.val = 7
  · exact krk_hfile hI h7
  have hI' := hI
  obtain ⟨hn, _, hfar, _, hns⟩ := hI
  have hn1 := hn.1
  obtain ⟨r, hr1, hr2⟩ : ∃ r : Square, r.1.val = 7 ∧ r.2.val = rs.2.val :=
    ⟨(⟨7, by decide⟩, rs.2), rfl, rfl⟩
  have hl : RookLine rs r := by simp only [RookLine]; omega
  have hs : ¬ OnSeg rs sk r := by simp only [OnSeg]; omega
  have hsk : r ≠ sk := by rw [ne_iff_coords]; omega
  have hx : ¬ HExc sk r wk := by simp only [HExc] at hE ⊢; omega
  exact after_rook hI' hl hs hsk (krk_RLh hn hr1 (rook_move_ok hns hl hs).2 hfar hx)
    (fun t ht => krk_hfile ht hr1)

/-- **File shift (FS).** `S` blocks the rook's rank towards the h-file (F1, F3), or the
position is the exception (F2): `R → (rx, y′)` with `y′` off `S`'s rank, off rank 7 and at
rank distance ≥ 2 from `L`; a reply by RL-f (F1, F3) or `Ka8–a7` (F2); then HV/direct. -/
theorem krk_fs {sk rs wk : Square} (hI : RookInv sk rs wk)
    (hF : (sk.2.val = rs.2.val ∧ rs.1.val < sk.1.val) ∨ HExc sk rs wk) (y' : Fin 8)
    (h1 : y'.val ≠ rs.2.val) (h2 : y'.val ≠ 6) (h3 : y'.val ≠ sk.2.val)
    (h4 : y'.val + 2 ≤ wk.2.val ∨ wk.2.val + 2 ≤ y'.val) : WinM ⟨sk, rs, wk, true⟩ := by
  have hI' := hI
  obtain ⟨hn, _, hfar, hrw, hns⟩ := hI
  have hn1 := hn.1
  obtain ⟨r, hr1, hr2⟩ : ∃ r : Square, r.1.val = rs.1.val ∧ r.2.val = y'.val :=
    ⟨(rs.1, y'), rfl, rfl⟩
  have hl : RookLine rs r := by simp only [RookLine]; omega
  have hs : ¬ OnSeg rs sk r := by simp only [OnSeg, HExc] at hF ⊢; omega
  have hsk : r ≠ sk := by rw [ne_iff_coords]; omega
  rw [ne_iff_coords] at hrw
  have hok : LoneOK sk r wk := by
    rcases hF with hF | hF
    · -- F1, F3: `L` is off the rook's file (`S`, to its right, cannot shield it there)
      have hf : wk.1.val ≠ rs.1.val := by
        intro he
        have h := shield_of_line hns (by simp only [RookLine]; omega)
        simp only [OnSeg] at h; omega
      exact Or.inl (krk_RLf hn1 (by omega) (by omega) (by omega) hfar)
    · -- F2: `L = a8` and the rook, now on `(rx, y′)`, is off the a-file: `Ka8–a7`
      simp only [HExc] at hF
      have hr0 : rs.1.val ≠ 0 := by
        intro he
        have h := shield_of_line hns (by simp only [RookLine]; omega)
        simp only [OnSeg] at h; omega
      refine Or.inl ⟨(⟨0, by decide⟩, ⟨6, by decide⟩), ?_⟩
      simp only [Free, RookSees, RookLine, OnSeg, ne_iff_coords, dInf, absDiff, true_and,
        and_true, true_or, or_true]
      omega
  exact after_rook hI' hl hs hsk hok (fun t ht => krk_rankToH ht (by omega)
    (by simp only [HExc]; omega))

/-- **Lemma P1, with the end-game half.** From every strong-to-move state with `S`
normalised, the kings apart and the lone king not seen by the rook, a model mate is
reachable. Classification: if `S` blocks the rook's rank towards the h-file, or the
position is the exception, file shift with `y′` = rank 1 if `L` is on rank 3 or higher,
else rank 8 (rank 5 if the rook is on rank 8); otherwise HV/direct/h-file/home. -/
theorem krk_P1 {sk rs wk : Square} (hI : RookInv sk rs wk) : WinM ⟨sk, rs, wk, true⟩ := by
  by_cases hF : (sk.2.val = rs.2.val ∧ rs.1.val < sk.1.val) ∨ HExc sk rs wk
  · have hn := hI.1
    have hF' := hF
    simp only [HExc, Normal] at hF' hn
    by_cases hw : 2 ≤ wk.2.val
    · obtain ⟨y', hy⟩ : ∃ y' : Fin 8, y'.val = 0 := ⟨⟨0, by decide⟩, rfl⟩
      exact krk_fs hI hF y' (by omega) (by omega) (by omega) (by omega)
    by_cases h7 : rs.2.val = 7
    · obtain ⟨y', hy⟩ : ∃ y' : Fin 8, y'.val = 4 := ⟨⟨4, by decide⟩, rfl⟩
      exact krk_fs hI hF y' (by omega) (by omega) (by omega) (by omega)
    · obtain ⟨y', hy⟩ : ∃ y' : Fin 8, y'.val = 7 := ⟨⟨7, by decide⟩, rfl⟩
      exact krk_fs hI hF y' (by omega) (by omega) (by omega) (by omega)
  · exact krk_rankToH hI (fun h => hF (Or.inl h)) (fun h => hF (Or.inr h))

end EndgameChess.Rules
