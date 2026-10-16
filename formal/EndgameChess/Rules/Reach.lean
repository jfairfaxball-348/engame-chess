import EndgameChess.Rules.Flags

/-!
# Rules kernel K3 — positions reached by any legal move (closes gap G2)

EC-T0001 and EC-T0002 (and their kernel forms in K2) cover the flag-free embeddings
`ofKK` / `ofKBK` and assume local legality. Here the hypothesis is only that the position
was produced by **some legal move from any position** (any material, so including the
capture of the last other piece), or that it **arose from the initial position**
(Art. 3.10.3). The conclusion is that it is dead. No invariant of game history is needed.
Legality of the last move (3.9.2) gives admissibility, and flag irrelevance
(`deadK_normFlags_iff`) removes whatever castling or en-passant flags the position carries.
-/

namespace EndgameChess.Rules

open EndgameChess.KK

/-- Art. 3.10.3: a position is legal (has arisen) iff it can be reached from the initial
position by a series of legal moves. -/
def Arisen (q : Position) : Prop := ReachK initial q

theorem initial_arisen : Arisen initial := ReachK.refl _

/-- Exactly two kings: White on `w`, Black on `b`, nothing else. -/
def IsKK (q : Position) (w b : Square) : Prop := w ≠ b ∧ q.board = kkBoard w b

/-- Exactly king + bishop of colour `σ` (on `sk`, `bs`) against the other colour's lone
king (on `wk`). -/
def IsKBK (q : Position) (σ : Colour) (sk bs wk : Square) : Prop :=
  sk ≠ bs ∧ sk ≠ wk ∧ bs ≠ wk ∧ q.board = kbkBoard σ sk bs wk

theorem turn_of_legal {p q : Position} (h : Legal p q) : q.turn = p.turn.opp := by
  obtain ⟨m, _, rfl⟩ := h; rfl

theorem nrp_kkBoard {q : Position} {w b : Square} (h : q.board = kkBoard w b) : NRP q := by
  intro s pc hs
  rw [h] at hs
  unfold kkBoard at hs
  split at hs
  · cases hs; decide
  · split at hs
    · cases hs; decide
    · cases hs

theorem nrp_kbkBoard {q : Position} {σ : Colour} {sk bs wk : Square}
    (h : q.board = kbkBoard σ sk bs wk) : NRP q := by
  intro s pc hs
  rw [h] at hs
  rcases kbkBoard_some hs with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp

/-- **G2, K vs K.** A two-king position produced by any legal move is dead, whatever the
predecessor's material (e.g. the capture of the last other piece) and whatever flags it
carries. -/
theorem dead_of_legal_into_KK {p q : Position} {w b : Square} (hl : Legal p q)
    (hk : IsKK q w b) : DeadK q := by
  obtain ⟨hne, hb⟩ := hk
  have hnrp : NRP q := nrp_kkBoard hb
  let a : KKState := ⟨w, b, q.turn⟩
  have hnorm : normFlags q = ofKK a :=
    Position.ext' (fun s => by show q.board s = kkBoard w b s; rw [hb]) rfl rfl rfl
  have ha : Admissible a := by
    have hsafe := legal_mover_safe hl
    have h0 : dInf w b ≠ 0 := fun h => hne (dInf_eq_zero_iff.1 h)
    have h1 : dInf w b ≠ 1 := by
      intro h1
      have hc : inCheck (ofKK a) p.turn = true := (inCheck_ofKK (a := a) hne p.turn).2 h1
      rw [← hnorm, inCheck_of_board (p := normFlags q) (q := q) rfl] at hc
      rw [hc] at hsafe; cases hsafe
    show 2 ≤ dInf w b
    omega
  rw [← deadK_normFlags_iff hnrp, hnorm]
  exact kernel_dead_KK ha

theorem sideColour_opp (σ : Colour) (s : KBK.Side) :
    sideColour σ s.opp = (sideColour σ s).opp := by
  cases s <;> simp [sideColour, KBK.Side.opp, opp_opp]

theorem exists_side (σ c : Colour) : ∃ s : KBK.Side, sideColour σ s = c := by
  cases σ <;> cases c
  · exact ⟨.strong, rfl⟩
  · exact ⟨.weak, rfl⟩
  · exact ⟨.weak, rfl⟩
  · exact ⟨.strong, rfl⟩

/-- **G2, K+B vs K.** A K+B vs K position (either orientation) produced by any legal move
is dead, whatever the predecessor and whatever flags it carries. -/
theorem dead_of_legal_into_KBK {p q : Position} {σ : Colour} {sk bs wk : Square}
    (hl : Legal p q) (hk : IsKBK q σ sk bs wk) : DeadK q := by
  obtain ⟨h12, h13, h23, hb⟩ := hk
  have hnrp : NRP q := nrp_kbkBoard hb
  obtain ⟨sd, hsd⟩ := exists_side σ q.turn
  let p' : KBK.KBKState := ⟨σ, sk, bs, wk, sd⟩
  have hnorm : normFlags q = ofKBK p' :=
    Position.ext' (fun s => by show q.board s = kbkBoard σ sk bs wk s; rw [hb]) hsd.symm rfl rfl
  have hmover : p.turn = sideColour σ sd.opp := by
    rw [sideColour_opp, hsd, turn_of_legal hl, opp_opp]
  have hl' : KBK.LKBK p' := by
    refine ⟨h12, h13, h23, fun hc => ?_⟩
    have hk := (inCheck_side (p := p') ⟨h12, h13, h23⟩ sd.opp).2 hc
    rw [← hnorm, inCheck_of_board (p := normFlags q) (q := q) rfl, ← hmover] at hk
    have hsafe := legal_mover_safe hl
    rw [hk] at hsafe; cases hsafe
  rw [← deadK_normFlags_iff hnrp, hnorm]
  exact kernel_dead_KBK hl'

theorem initial_a2 : initial.board ((0 : Fin 8), (1 : Fin 8)) = some ⟨.white, .pawn⟩ := by
  decide

theorem initial_not_KK (w b : Square) : ¬ IsKK initial w b := by
  rintro ⟨_, hb⟩
  have h := congrFun hb ((0 : Fin 8), (1 : Fin 8))
  rw [initial_a2] at h
  simp only [kkBoard] at h
  split at h
  · simp at h
  · split at h <;> simp at h

theorem initial_not_KBK (σ : Colour) (sk bs wk : Square) : ¬ IsKBK initial σ sk bs wk := by
  rintro ⟨_, _, _, hb⟩
  have h := congrFun hb ((0 : Fin 8), (1 : Fin 8))
  rw [initial_a2] at h
  simp only [kbkBoard] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp only [Option.some.injEq, Piece.mk.injEq] at h
        exact absurd h.2 (by decide)
      · simp at h

/-- **K vs K, arisen form.** Every two-king position that has arisen in a game is dead. -/
theorem arisen_KK_dead {q : Position} {w b : Square} (ha : Arisen q) (hk : IsKK q w b) :
    DeadK q := by
  cases ha with
  | refl => exact absurd hk (initial_not_KK w b)
  | tail _ hl => exact dead_of_legal_into_KK hl hk

/-- **K+B vs K, arisen form.** Every K+B vs K position (either orientation) that has arisen
in a game is dead. -/
theorem arisen_KBK_dead {q : Position} {σ : Colour} {sk bs wk : Square} (ha : Arisen q)
    (hk : IsKBK q σ sk bs wk) : DeadK q := by
  cases ha with
  | refl => exact absurd hk (initial_not_KBK σ sk bs wk)
  | tail _ hl => exact dead_of_legal_into_KBK hl hk

/-! ## Non-vacuity: a capture from larger material into K vs K -/

/-- White Kc1, Black Qd2 (checking), Black Kh8; White to move. -/
def kqkPos : Position :=
  { board := boardOf [(((2 : Fin 8), (0 : Fin 8)), ⟨.white, .king⟩),
                      (((3 : Fin 8), (1 : Fin 8)), ⟨.black, .queen⟩),
                      (((7 : Fin 8), (7 : Fin 8)), ⟨.black, .king⟩)],
    turn := .white, castling := noRights, ep := none }

def kxd2 : Move := ⟨((2 : Fin 8), (0 : Fin 8)), ((3 : Fin 8), (1 : Fin 8)), none⟩

/-- Kxd2 is legal from a position holding a queen, and it produces exactly K vs K. So the
G2 theorem genuinely applies to a capture out of larger material. -/
theorem capture_into_KK_example :
    kqkPos.board ((3 : Fin 8), (1 : Fin 8)) = some ⟨.black, .queen⟩ ∧
    Legal kqkPos (play kqkPos kxd2) ∧
    IsKK (play kqkPos kxd2) ((3 : Fin 8), (1 : Fin 8)) ((7 : Fin 8), (7 : Fin 8)) ∧
    DeadK (play kqkPos kxd2) := by
  have hleg : isLegal kqkPos kxd2 = true := by decide
  have hall : ∀ s ∈ allSquares, (play kqkPos kxd2).board s =
      kkBoard ((3 : Fin 8), (1 : Fin 8)) ((7 : Fin 8), (7 : Fin 8)) s := by decide
  have hkk : IsKK (play kqkPos kxd2) ((3 : Fin 8), (1 : Fin 8)) ((7 : Fin 8), (7 : Fin 8)) :=
    ⟨by decide, funext fun s => hall s (mem_allSquares s)⟩
  have hl : Legal kqkPos (play kqkPos kxd2) := ⟨kxd2, hleg, rfl⟩
  exact ⟨by decide, hl, hkk, dead_of_legal_into_KK hl hkk⟩

end EndgameChess.Rules
