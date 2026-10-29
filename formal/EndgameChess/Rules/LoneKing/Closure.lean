import EndgameChess.Rules.LoneKing.Moves
import EndgameChess.Rules.KRKForcing.OrdinaryMoves

/-! Reusable nonpawn material closure. Pawn promotion is handled by KPK. -/
namespace EndgameChess.Rules.LoneKing
open EndgameChess.KK

theorem strong_target_empty {k : PieceType} {q : Position} {σ : Colour}
    {sk xs wk t : Square} (h : Material k q σ sk xs wk) (ht : q.turn = σ)
    (ok : targetOK q t = true) : q.board t = none := by
  cases he : q.board t with
  | none => rfl
  | some pc =>
    have target := targetOK_some ok he
    rw [h.2.2.2] at he
    rcases board_some he with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact False.elim (target.1 ht.symm)
    · exact False.elim (target.1 ht.symm)
    · exact False.elim (target.2 rfl)

theorem king_play_material {k : PieceType} {q : Position} {σ : Colour}
    {sk xs wk : Square} {m : Move}
    (h : Material k q σ sk xs wk) (ht : q.turn = σ) (src : m.src = sk)
    (pro : m.promo = none) (step : dInf sk m.dst = 1) (empty : q.board m.dst = none) :
    Material k (play q m) σ m.dst xs wk := by
  have source : q.board m.src = some ⟨q.turn, .king⟩ := by
    rw [src, ht, h.2.2.2]; exact board_sk
  have hn := empty
  rw [h.2.2.2] at hn
  obtain ⟨_, nxs, nwk⟩ := board_none.mp hn
  refine ⟨nxs, nwk, h.2.2.1, ?_⟩
  rw [play_board_simple source (by decide) pro (fun _ => by rw [src]; exact step)]
  funext s
  rw [src, ht, h.2.2.2]
  unfold board
  by_cases dst : s = m.dst
  · subst s; simp
  · by_cases old : s = sk
    · subst s; simp [dst, h.1, h.2.1]
    · simp [dst, old]

theorem extra_play_material {k : PieceType} (nk : k ≠ .king) (np : k ≠ .pawn)
    {q : Position} {σ : Colour} {sk xs wk : Square} {m : Move}
    (h : Material k q σ sk xs wk) (ht : q.turn = σ) (src : m.src = xs)
    (pro : m.promo = none) (empty : q.board m.dst = none) :
    Material k (play q m) σ sk m.dst wk := by
  have source : q.board m.src = some ⟨q.turn, k⟩ := by
    rw [src, ht, h.2.2.2]; exact board_xs h.1
  have hn := empty
  rw [h.2.2.2] at hn
  obtain ⟨nsk, _, nwk⟩ := board_none.mp hn
  refine ⟨Ne.symm nsk, h.2.1, nwk, ?_⟩
  rw [play_board_simple source np pro (fun eq => False.elim (nk eq))]
  funext s
  rw [src, ht, h.2.2.2]
  unfold board
  by_cases dst : s = m.dst
  · subst s; simp [nsk]
  · by_cases old : s = xs
    · subst s; simp [dst, Ne.symm h.1, h.2.2.1]
    · simp [dst, old]

/-- Every strong move of a nonpawn K+X class preserves that class.
No movement symmetry or piece-specific forcing result is needed. -/
theorem strong_cases {k : PieceType} (nk : k ≠ .king) (np : k ≠ .pawn)
    {q r : Position} {σ : Colour} {sk xs wk : Square}
    (h : Material k q σ sk xs wk) (ht : q.turn = σ)
    (rights : q.castling = noRights) (legal : Legal q r) :
    (∃ t, Material k r σ t xs wk) ∨ (∃ t, Material k r σ sk t wk) := by
  obtain ⟨m, hm, rfl⟩ := legal
  have pseudo : isPseudo q m = true := by
    simp only [isLegal, Bool.and_eq_true] at hm
    exact hm.1
  have empty := strong_target_empty h ht (targetOK_of_isPseudo pseudo)
  obtain ⟨pc, source, colour⟩ := own_of_isPseudo pseudo
  rw [h.2.2.2] at source
  rcases board_some source with ⟨src, rfl⟩ | ⟨src, rfl⟩ | ⟨_, rfl⟩
  · have hs : q.board m.src = some ⟨q.turn, .king⟩ := by
      rw [ht, src, h.2.2.2]; exact board_sk
    rw [isPseudo_of_king hs, canCastle_noRights rights] at pseudo
    simp only [Bool.or_false, Bool.and_eq_true, Option.isNone_iff_eq_none] at pseudo
    have step : dInf sk m.dst = 1 := by
      simpa only [src] using kingGeom_iff.mp pseudo.2.2
    exact Or.inl ⟨m.dst, king_play_material h ht src pseudo.2.1 step empty⟩
  · have hs : q.board m.src = some ⟨q.turn, k⟩ := by
      rw [ht, src, h.2.2.2]; exact board_xs h.1
    have pro : m.promo = none := by
      cases k <;> simp_all [isPseudo, Option.isNone_iff_eq_none]
    exact Or.inr ⟨m.dst, extra_play_material nk np h ht src pro empty⟩
  · exact False.elim (opp_ne σ (colour.trans ht).symm)

/-- In any K+X board, safety of either moving king implies king separation. -/
theorem kings_apart_after {k : PieceType} (nk : k ≠ .king)
    {q r : Position} {σ : Colour} {sk xs wk : Square}
    (h : Material k r σ sk xs wk) (legal : Legal q r) : 2 ≤ dInf sk wk := by
  have zero : dInf sk wk ≠ 0 := fun e => h.2.1 (dInf_eq_zero_iff.mp e)
  have one : dInf sk wk ≠ 1 := by
    intro near
    have safe := legal_mover_safe legal
    rcases colour_cases σ q.turn with turn | turn
    · have check := (strong_check nk h).mpr (by simpa only [dInf_comm] using near)
      rw [turn, check] at safe
      cases safe
    · have check := (weak_check nk h).mpr (Or.inl near)
      rw [turn, check] at safe
      cases safe
  omega

end EndgameChess.Rules.LoneKing
