import EndgameChess.Rules.KRKLive.Relocation

/-!
# EC-C008 — K+R vs K with the strong side to move is never dead (main theorems, S022)

Formalisation of §1 and the main theorem of `proofs/EC-C008_KRK_LIVE.md`, over the general
FIDE 2023 rules kernel. Assembles the KRK move model (`Rules.KRKLive.Basic`), the end-game
half (`Rules.KRKLive.Endgame`), the reply lemmas (`Rules.KRKLive.Reply`) and P1
(`Rules.KRKLive.Relocation`).

- `krk_live_of_not_check`: a K+R vs K position (any flags) with the strong side to move and
  the lone king not in check is not dead. F4: a reflection normalises `S`
  (`exists_sym_normal`), P1 runs in the normal frame (`krk_P1`), and `winM_of_sym`,
  `not_deadK_of_winM` return to the kernel position.
- **EC-C008(a)** `krk_strong_to_move_live`: produced by a legal move ⇒ not dead (F1: the
  side that just moved is not in check).
- **EC-C008(b)** `krk_dead_iff`: with the lone king to move, dead ⇔ not checkmate and every
  legal move captures the rook. "⇐" is EC-T0006 (`krk_dead_of_forced_capture`); "⇒" uses
  (a) after a non-capturing lone-king move (`lone_move_cases`).
- Arisen forms and the Art. 5.2.2 rule encoding: `arisen_krk_strong_live`,
  `krk_drawn_by_rule_iff`.
- Non-vacuity by `decide`.
-/

namespace EndgameChess.Rules

open EndgameChess.KK

/-- K+R vs K, strong side to move, lone king not in check (any flags): not dead. -/
theorem krk_live_of_not_check {q : Position} {σ : Colour} {sk rs wk : Square}
    (hk : IsKRK q σ sk rs wk) (ht : q.turn = σ) (hc : inCheck q σ.opp = false) :
    ¬ DeadK q := by
  have hk' := hk
  obtain ⟨h12, h13, h23, hb⟩ := hk
  have hno : ¬ (dInf sk wk = 1 ∨ RookSees rs wk sk wk) := by
    intro h; rw [(inCheck_weak_krk h12 h13 h23 hb).2 h] at hc; cases hc
  have h0 : dInf sk wk ≠ 0 := fun h => h13 (dInf_eq_zero_iff.1 h)
  have hfar : 2 ≤ dInf sk wk := by
    have : dInf sk wk ≠ 1 := fun h => hno (Or.inl h)
    omega
  obtain ⟨g, hg⟩ := exists_sym_normal sk
  have hI : RookInv (g.f sk) (g.f rs) (g.f wk) :=
    ⟨hg, (g.ne_iff).2 h12, by rw [g.dInf_eq]; exact hfar, (g.ne_iff).2 h23,
      by rw [g.sees_iff]; exact fun h => hno (Or.inr h)⟩
  exact not_deadK_of_winM (a := ⟨sk, rs, wk, true⟩) ⟨hk', by simp [ht]⟩
    (winM_of_sym g (krk_P1 hI))

/-- **EC-C008(a).** A K+R vs K position (either orientation, any flags) produced by a legal
move, with the strong side to move, is not dead. -/
theorem krk_strong_to_move_live {p q : Position} {σ : Colour} {sk rs wk : Square}
    (hl : Legal p q) (hk : IsKRK q σ sk rs wk) (ht : q.turn = σ) : ¬ DeadK q := by
  have hp : p.turn = σ.opp := by
    rw [← ht, turn_of_legal hl, opp_opp]
  have hc := legal_mover_safe hl
  rw [hp] at hc
  exact krk_live_of_not_check hk ht hc

/-- Head extension of a series of legal moves. -/
theorem reachK_cons {q r m : Position} (hl : Legal q r) (h : ReachK r m) : ReachK q m := by
  induction h with
  | refl => exact ReachK.tail (ReachK.refl _) hl
  | tail _ hs ih => exact ReachK.tail ih hs

/-- A legal move of the lone king from K+R vs K either leaves K+R vs K with the strong side
to move, or captures the rook and leaves K vs K. -/
theorem lone_move_cases {q r : Position} {σ : Colour} {sk rs wk : Square}
    (hk : IsKRK q σ sk rs wk) (ht : q.turn = σ.opp) (hl : Legal q r) :
    (∃ t, IsKRK r σ sk rs t ∧ r.turn = σ) ∨ (∃ w b, IsKK r w b) := by
  obtain ⟨h12, h13, h23, hb⟩ := hk
  obtain ⟨m, hm, rfl⟩ := hl
  have hp : isPseudo q m = true := by
    unfold isLegal at hm; simp only [Bool.and_eq_true] at hm; exact hm.1
  obtain ⟨pc, hpc, hcol⟩ := own_of_isPseudo hp
  have hturn : (play q m).turn = σ := by rw [play_turn, ht, opp_opp]
  rw [hb] at hpc
  rcases krkBoard_some hpc with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨esrc, rfl⟩
  · rw [ht] at hcol; exact absurd hcol (opp_ne _)
  · rw [ht] at hcol; exact absurd hcol (opp_ne _)
  have hsrc : q.board m.src = some ⟨q.turn, .king⟩ := by
    rw [hb, ht, esrc]; exact krkBoard_wk h13 h23
  have hnc : canCastle q m = false := by
    apply canCastle_false_of_noRook
    intro s hs
    rw [hb, ht] at hs
    rcases krkBoard_some hs with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩
    · simp at h
    · simp only [Piece.mk.injEq] at h; exact opp_ne _ h.1.symm
    · simp at h
  rw [isPseudo_of_king hsrc, hnc] at hp
  simp only [Bool.or_false, Bool.and_eq_true, Option.isNone_iff_eq_none] at hp
  obtain ⟨htg, hpro, hg⟩ := hp
  have hd : dInf m.src m.dst = 1 := kingGeom_iff.1 hg
  rw [esrc] at hd
  have hdk : m.dst ≠ sk := by
    intro e
    have := (targetOK_some htg (by rw [hb, e]; exact krkBoard_sk)).2
    exact this rfl
  have hdw : m.dst ≠ wk := Ne.symm (ne_of_dInf_pos (s := wk) (t := m.dst) (by omega))
  have hbp := play_board_simple hsrc (by decide) hpro (fun _ => by rw [esrc]; exact hd)
  by_cases hcap : m.dst = rs
  · -- the rook is captured: K vs K
    right
    cases σ with
    | white =>
      refine ⟨sk, m.dst, Ne.symm hdk, ?_⟩
      rw [hbp]; funext x; rw [hb, ht, esrc, hcap]; unfold krkBoard kkBoard
      by_cases e1 : x = rs
      · subst e1; simp [Ne.symm h12, Colour.opp]
      · by_cases e2 : x = wk
        · subst e2; simp [e1, Ne.symm h13]
        · simp [e1, e2]
    | black =>
      refine ⟨m.dst, sk, hdk, ?_⟩
      rw [hbp]; funext x; rw [hb, ht, esrc, hcap]; unfold krkBoard kkBoard
      by_cases e1 : x = rs
      · subst e1; simp [Colour.opp]
      · by_cases e2 : x = wk
        · subst e2; simp [e1, Ne.symm h13]
        · by_cases e3 : x = sk
          · subst e3; simp [e1, e2]
          · simp [e1, e2, e3]
  · left
    refine ⟨m.dst, ⟨h12, Ne.symm hdk, Ne.symm hcap, ?_⟩, hturn⟩
    rw [hbp]; funext x; rw [hb, ht, esrc]; unfold krkBoard
    by_cases e1 : x = m.dst
    · subst e1; simp [hdk, hcap]
    · by_cases e2 : x = wk
      · subst e2; simp [e1, Ne.symm h13, Ne.symm h23]
      · simp [e1, e2]

/-- **EC-C008(b).** A K+R vs K position (either orientation, any flags) with the lone king
to move is dead iff it is not checkmate and every legal move captures the rook (leaving
K vs K). No hypothesis on how the position arose is needed. -/
theorem krk_dead_iff {q : Position} {σ : Colour} {sk rs wk : Square}
    (hk : IsKRK q σ sk rs wk) (ht : q.turn = σ.opp) :
    DeadK q ↔ ¬ MatedK q ∧ ∀ r, Legal q r → ∃ w b, IsKK r w b := by
  constructor
  · intro hd
    refine ⟨fun hm => hd ⟨q, ReachK.refl q, hm⟩, fun r hr => ?_⟩
    rcases lone_move_cases hk ht hr with ⟨t, hk', ht'⟩ | hkk
    · have hdr : DeadK r := fun ⟨m, hrm, hmm⟩ => hd ⟨m, reachK_cons hr hrm, hmm⟩
      exact absurd hdr (krk_strong_to_move_live hr hk' ht')
    · exact hkk
  · rintro ⟨hm, h⟩
    exact krk_dead_of_forced_capture hk ht hm h

theorem initial_not_KRK (σ : Colour) (sk rs wk : Square) : ¬ IsKRK initial σ sk rs wk := by
  rintro ⟨_, _, _, hb⟩
  have h := congrFun hb ((0 : Fin 8), (1 : Fin 8))
  rw [initial_a2] at h
  simp only [krkBoard] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp only [Option.some.injEq, Piece.mk.injEq] at h
        exact absurd h.2 (by decide)
      · simp at h

/-- **EC-C008(a), arisen form.** Every arisen K+R vs K position with the strong side to move
is not dead. -/
theorem arisen_krk_strong_live {q : Position} {σ : Colour} {sk rs wk : Square}
    (ha : Arisen q) (hk : IsKRK q σ sk rs wk) (ht : q.turn = σ) : ¬ DeadK q := by
  cases ha with
  | refl => exact absurd hk (initial_not_KRK σ sk rs wk)
  | tail _ hl => exact krk_strong_to_move_live hl hk ht

/-- **K+R vs K under the rule encoding `Rule5_2_2`.** An arisen K+R vs K position is an
immediate draw iff the lone king is to move, it is not checkmate, and every legal move
captures the rook. -/
theorem krk_drawn_by_rule_iff {q : Position} {σ : Colour} {sk rs wk : Square}
    (ha : Arisen q) (hk : IsKRK q σ sk rs wk) :
    Rule5_2_2 q .draw ↔
      q.turn = σ.opp ∧ ¬ MatedK q ∧ ∀ r, Legal q r → ∃ w b, IsKK r w b := by
  constructor
  · rintro ⟨_, hd, _⟩
    rcases colour_cases σ q.turn with e | e
    · exact absurd hd (arisen_krk_strong_live ha hk e)
    · exact ⟨e, (krk_dead_iff hk e).1 hd⟩
  · rintro ⟨ht, h⟩
    exact ⟨ha, (krk_dead_iff hk ht).2 h, rfl⟩

/-! ## Non-vacuity (kernel-checked by `decide`) -/

def sqC8 : Square := (⟨2, by decide⟩, ⟨7, by decide⟩)
def sqH7 : Square := (⟨7, by decide⟩, ⟨6, by decide⟩)
def sqA8 : Square := (⟨0, by decide⟩, ⟨7, by decide⟩)
def sqD7 : Square := (⟨3, by decide⟩, ⟨6, by decide⟩)

/-- White Kc8, Rh7, Black Ka8, Black to move: RL-h's exception. -/
def rlhExcPos : Position := krkPos .white sqC8 sqH7 sqA8 .black

set_option maxRecDepth 8192 in
/-- **RL-h's exception is a genuine stalemate**: Black is not in check and has no legal move,
so the position is dead (here through `krk_dead_iff`). -/
theorem rlh_exception_example :
    HExc sqC8 sqH7 sqA8 ∧ inCheck rlhExcPos .black = false ∧ legalMoves rlhExcPos = [] ∧
      DeadK rlhExcPos := by
  have hchk : inCheck rlhExcPos .black = false := by decide
  have hmoves : legalMoves rlhExcPos = [] := by decide
  have hm : ¬ MatedK rlhExcPos := by
    rintro ⟨hc, _⟩
    rw [show rlhExcPos.turn = .black from rfl, hchk] at hc
    cases hc
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, hchk, hmoves, ?_⟩
  refine (krk_dead_iff (σ := .white) ⟨by decide, by decide, by decide, rfl⟩ rfl).2
    ⟨hm, fun r hr => ?_⟩
  obtain ⟨m, hmem, _⟩ := legal_of_legalMoves_eq hmoves hr
  simp at hmem

/-- White Kc8, Rd7, Black Ka8, White to move: the file-shift exception F2 of P1. -/
def fsF2Pos : Position := krkPos .white sqC8 sqD7 sqA8 .white

theorem fsF2_example : inCheck fsF2Pos .black = false ∧ ¬ DeadK fsF2Pos :=
  ⟨by decide, krk_live_of_not_check ⟨by decide, by decide, by decide, rfl⟩ rfl (by decide)⟩

def sqD4 : Square := (⟨3, by decide⟩, ⟨3, by decide⟩)
def sqA1 : Square := (⟨0, by decide⟩, ⟨0, by decide⟩)
def sqF6 : Square := (⟨5, by decide⟩, ⟨5, by decide⟩)
def sqG7 : Square := (⟨6, by decide⟩, ⟨6, by decide⟩)

/-- White Kd4, Ra1, Black Kf6, Black to move. -/
def liveBefore : Position := krkPos .white sqD4 sqA1 sqF6 .black

def kf6g7 : Move := ⟨sqF6, sqG7, none⟩

/-- **EC-C008(a) applied:** after the legal move Kf6–g7 the position is K+R vs K with White
to move, so it is not dead. -/
theorem krk_strong_live_example :
    Legal liveBefore (play liveBefore kf6g7) ∧
    IsKRK (play liveBefore kf6g7) .white sqD4 sqA1 sqG7 ∧
    ¬ DeadK (play liveBefore kf6g7) := by
  have hleg : isLegal liveBefore kf6g7 = true := by decide
  have hall : ∀ s ∈ allSquares, (play liveBefore kf6g7).board s =
      krkBoard .white sqD4 sqA1 sqG7 s := by decide
  have hk : IsKRK (play liveBefore kf6g7) .white sqD4 sqA1 sqG7 :=
    ⟨by decide, by decide, by decide, funext fun s => hall s (mem_allSquares s)⟩
  have hl : Legal liveBefore (play liveBefore kf6g7) := ⟨kf6g7, hleg, rfl⟩
  exact ⟨hl, hk, krk_strong_to_move_live hl hk rfl⟩

end EndgameChess.Rules
