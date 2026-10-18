import EndgameChess.Rules.KNK

/-!
# EC-C007 — Dead K+R vs K positions (forced rook capture or stalemate), over the rules kernel

Faithful formalisation of `proofs/EC-C007_KRK_DEAD.md` (S014, Gate L). Stated directly over
the general FIDE 2023 rules kernel; no bespoke move model.

- D1 `dead_of_succ_dead`: a position that is not checkmate and all of whose legal
  successors are dead is dead (material-agnostic).
- D2 `dead_of_succ_KK`: the same when every legal successor is K vs K (via the frozen
  EC-T0003 `dead_of_legal_into_KK`).
- EC-C007 `krk_dead_of_forced_capture`: a K+R vs K position with the lone king to move,
  not checkmate, whose every legal move captures the rook (vacuously: stalemate), is dead;
  `krk_forced_capture_drawn_by_rule`: if arisen, drawn under `Rule5_2_2`.
- Non-vacuity by `decide`: a forced capture produced by a legal move, a stalemate, and a
  live K+R vs K position (mate in one) for contrast.
-/

namespace EndgameChess.Rules

open EndgameChess.KK

/-! ## The K+R vs K board -/

/-- Colour-`σ` king on `sk`, colour-`σ` rook on `rs`, colour-`σ.opp` king on `wk`,
nothing else. -/
def krkBoard (σ : Colour) (sk rs wk : Square) : Board := fun s =>
  if s = sk then some ⟨σ, .king⟩
  else if s = rs then some ⟨σ, .rook⟩
  else if s = wk then some ⟨σ.opp, .king⟩
  else none

/-- Exactly king + rook of colour `σ` against the other colour's lone king. Turn,
castling rights and en-passant target are arbitrary. -/
def IsKRK (q : Position) (σ : Colour) (sk rs wk : Square) : Prop :=
  sk ≠ rs ∧ sk ≠ wk ∧ rs ≠ wk ∧ q.board = krkBoard σ sk rs wk

/-! ## D1, D2: one-step deadness -/

/-- Head decomposition of the tail-inductive `ReachK`. -/
theorem reachK_head {q t : Position} (h : ReachK q t) :
    t = q ∨ ∃ r, Legal q r ∧ ReachK r t := by
  induction h with
  | refl => exact Or.inl rfl
  | @tail t1 t2 _ hl ih =>
    rcases ih with rfl | ⟨r, hr, hrt⟩
    · exact Or.inr ⟨t2, hl, ReachK.refl _⟩
    · exact Or.inr ⟨r, hr, ReachK.tail hrt hl⟩

/-- **D1.** Not checkmate, and every legal successor dead, implies dead. -/
theorem dead_of_succ_dead {q : Position} (hm : ¬ MatedK q)
    (h : ∀ r, Legal q r → DeadK r) : DeadK q := by
  rintro ⟨t, ht, hmt⟩
  rcases reachK_head ht with rfl | ⟨r, hr, hrt⟩
  · exact hm hmt
  · exact h r hr ⟨t, hrt, hmt⟩

/-- **D2.** Not checkmate, and every legal successor a two-king position, implies dead. -/
theorem dead_of_succ_KK {q : Position} (hm : ¬ MatedK q)
    (h : ∀ r, Legal q r → ∃ w b, IsKK r w b) : DeadK q :=
  dead_of_succ_dead hm fun r hr => by
    obtain ⟨w, b, hk⟩ := h r hr
    exact dead_of_legal_into_KK hr hk

/-! ## EC-C007 -/

/-- **EC-C007.** A K+R vs K position (either orientation, any flags) with the lone king to
move, which is not checkmate and in which every legal move captures the rook (vacuously
true in stalemate), is dead. The material and turn hypotheses fix the reading of the
statement; the proof needs only D2. -/
theorem krk_dead_of_forced_capture {q : Position} {σ : Colour} {sk rs wk : Square}
    (_hk : IsKRK q σ sk rs wk) (_ht : q.turn = σ.opp) (hm : ¬ MatedK q)
    (h : ∀ r, Legal q r → ∃ w b, IsKK r w b) : DeadK q :=
  dead_of_succ_KK hm h

/-- Under the rule encoding `Rule5_2_2`, an arisen K+R vs K position of the EC-C007 kind is
an immediate draw, although a rook is on the board. -/
theorem krk_forced_capture_drawn_by_rule {q : Position} {σ : Colour} {sk rs wk : Square}
    (ha : Arisen q) (hk : IsKRK q σ sk rs wk) (ht : q.turn = σ.opp) (hm : ¬ MatedK q)
    (h : ∀ r, Legal q r → ∃ w b, IsKK r w b) : Rule5_2_2 q .draw :=
  ⟨ha, krk_dead_of_forced_capture hk ht hm h, rfl⟩

/-! ## Non-vacuity (kernel-checked by `decide`) -/

/-- A K+R vs K board as a concrete `Position` with no flags. -/
def krkPos (σ : Colour) (sk rs wk : Square) (t : Colour) : Position :=
  { board := krkBoard σ sk rs wk, turn := t, castling := noRights, ep := none }

theorem legal_of_legalMoves_eq {q : Position} {ms : List Move} (h : legalMoves q = ms)
    {r : Position} (hr : Legal q r) : ∃ m ∈ ms, r = play q m := by
  rw [← mem_legalPositions] at hr
  simp only [legalPositions, h, List.mem_map] at hr
  obtain ⟨m, hm, rfl⟩ := hr
  exact ⟨m, hm, rfl⟩

/-- White Kh8, Rb3, Black Ka1, White to move. -/
def krkPre : Position :=
  krkPos .white ((7 : Fin 8), (7 : Fin 8)) ((1 : Fin 8), (2 : Fin 8)) ((0 : Fin 8), (0 : Fin 8)) .white

def rb2 : Move := ⟨((1 : Fin 8), (2 : Fin 8)), ((1 : Fin 8), (1 : Fin 8)), none⟩

def kxb2 : Move := ⟨((0 : Fin 8), (0 : Fin 8)), ((1 : Fin 8), (1 : Fin 8)), none⟩

/-- **Forced capture.** After the legal move Rb3–b2, Black (Ka1) is not in check and its
only legal move is Kxb2, which leaves K vs K. The resulting K+R vs K position is dead. -/
theorem krk_forced_capture_example :
    Legal krkPre (play krkPre rb2) ∧
    IsKRK (play krkPre rb2) .white ((7 : Fin 8), (7 : Fin 8)) ((1 : Fin 8), (1 : Fin 8))
      ((0 : Fin 8), (0 : Fin 8)) ∧
    (play krkPre rb2).turn = Colour.white.opp ∧
    inCheck (play krkPre rb2) .black = false ∧
    legalMoves (play krkPre rb2) = [kxb2] ∧
    DeadK (play krkPre rb2) := by
  have hleg : isLegal krkPre rb2 = true := by decide
  have hall : ∀ s ∈ allSquares, (play krkPre rb2).board s =
      krkBoard .white ((7 : Fin 8), (7 : Fin 8)) ((1 : Fin 8), (1 : Fin 8))
        ((0 : Fin 8), (0 : Fin 8)) s := by decide
  have hk : IsKRK (play krkPre rb2) .white ((7 : Fin 8), (7 : Fin 8))
      ((1 : Fin 8), (1 : Fin 8)) ((0 : Fin 8), (0 : Fin 8)) :=
    ⟨by decide, by decide, by decide, funext fun s => hall s (mem_allSquares s)⟩
  have hchk : inCheck (play krkPre rb2) .black = false := by decide
  have hmoves : legalMoves (play krkPre rb2) = [kxb2] := by decide
  have hcap : ∀ s ∈ allSquares, (play (play krkPre rb2) kxb2).board s =
      kkBoard ((7 : Fin 8), (7 : Fin 8)) ((1 : Fin 8), (1 : Fin 8)) s := by decide
  have hturn : (play krkPre rb2).turn = Colour.white.opp := rfl
  have hm : ¬ MatedK (play krkPre rb2) := by
    rintro ⟨hc, _⟩
    rw [show (play krkPre rb2).turn = .black from rfl, hchk] at hc
    cases hc
  refine ⟨⟨rb2, hleg, rfl⟩, hk, hturn, hchk, hmoves, ?_⟩
  refine krk_dead_of_forced_capture hk hturn hm fun r hr => ?_
  obtain ⟨m, hmem, rfl⟩ := legal_of_legalMoves_eq hmoves hr
  simp only [List.mem_singleton] at hmem
  subst hmem
  exact ⟨_, _, by decide, funext fun s => hcap s (mem_allSquares s)⟩

/-- Black Ka1, White Rb2, White Kc3, Black to move. -/
def krkStale : Position :=
  krkPos .white ((2 : Fin 8), (2 : Fin 8)) ((1 : Fin 8), (1 : Fin 8)) ((0 : Fin 8), (0 : Fin 8)) .black

/-- **Stalemate.** Black is not in check and has no legal move; the position is dead. -/
theorem krk_stalemate_dead_example :
    inCheck krkStale .black = false ∧ legalMoves krkStale = [] ∧ DeadK krkStale := by
  have hchk : inCheck krkStale .black = false := by decide
  have hmoves : legalMoves krkStale = [] := by decide
  have hm : ¬ MatedK krkStale := by
    rintro ⟨hc, _⟩
    rw [show krkStale.turn = .black from rfl, hchk] at hc
    cases hc
  refine ⟨hchk, hmoves, dead_of_succ_KK hm fun r hr => ?_⟩
  obtain ⟨m, hmem, _⟩ := legal_of_legalMoves_eq hmoves hr
  simp at hmem

/-- White Kh6, Ra1, Black Kh8, White to move. -/
def krkLive : Position :=
  krkPos .white ((7 : Fin 8), (5 : Fin 8)) ((0 : Fin 8), (0 : Fin 8)) ((7 : Fin 8), (7 : Fin 8)) .white

def ra8 : Move := ⟨((0 : Fin 8), (0 : Fin 8)), ((0 : Fin 8), (7 : Fin 8)), none⟩

set_option maxRecDepth 8192 in
/-- **Contrast: a live K+R vs K position.** Ra1–a8 is legal and mates, so the position is
not dead. EC-C007 is therefore not a statement about all K+R vs K positions. -/
theorem krk_live_example : ¬ DeadK krkLive := by
  have hleg : isLegal krkLive ra8 = true := by decide
  have hchk : inCheck (play krkLive ra8) (play krkLive ra8).turn = true := by decide
  have hmoves : legalMoves (play krkLive ra8) = [] := by decide
  intro hd
  refine hd ⟨play krkLive ra8, ReachK.tail (ReachK.refl _) ⟨ra8, hleg, rfl⟩, hchk, ?_⟩
  rintro ⟨r, hr⟩
  obtain ⟨m, hmem, _⟩ := legal_of_legalMoves_eq hmoves hr
  simp at hmem

end EndgameChess.Rules
