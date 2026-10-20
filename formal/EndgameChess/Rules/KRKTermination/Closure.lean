import EndgameChess.Rules.KRKTermination.Strong
namespace EndgameChess.Rules
open EndgameChess.KK

/-- All legal moves, either turn and all flags: quiet KRK or dead KK. -/
theorem krk_legal_material_clock {q : Position} {σ : Colour} {sk rs wk : Square}
    {m : Move} (hk : IsKRK q σ sk rs wk) (hm : isLegal q m = true) :
    (∃ ns nr nw, IsKRK (play q m) σ ns nr nw ∧ RawClock.zeroing q m = false) ∨
      (∃ w b, IsKK (play q m) w b ∧ DeadK (play q m)) := by
  have hp : isPseudo q m = true := by
    simp only [isLegal, Bool.and_eq_true] at hm
    exact hm.1
  obtain ⟨noPawn, target⟩ := krk_material_targets hk hp
  have pawnFalse : (q.board m.src == some ⟨q.turn, .pawn⟩) = false := by
    rw [Bool.eq_false_iff]
    simpa using noPawn
  have quiet : q.board m.dst = none → RawClock.zeroing q m = false := by
    intro empty
    simp [RawClock.zeroing, pawnFalse, empty]
  rcases colour_cases σ q.turn with ht | ht
  · obtain ⟨ns, nr, material⟩ := krk_strong_material hk ht hm
    refine Or.inl ⟨ns, nr, wk, material, quiet ?_⟩
    cases dest : q.board m.dst with
    | none => rfl
    | some pc => exact False.elim ((target pc dest).2.2 ht)
  · rcases lone_move_cases hk ht ⟨m, hm, rfl⟩ with ⟨nw, material, _⟩ | ⟨w,b,kk⟩
    · refine Or.inl ⟨sk, rs, nw, material, quiet ?_⟩
      cases dest : q.board m.dst with
      | none => rfl
      | some pc =>
        have dst := (target pc dest).1
        obtain ⟨piece, source, colour⟩ := own_of_isPseudo hp
        rw [hk.2.2.2] at source
        rcases krkBoard_some source with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
        · rw [ht] at colour
          exact False.elim (opp_ne _ colour)
        · rw [ht] at colour
          exact False.elim (opp_ne _ colour)
        · have hsrc : q.board m.src = some ⟨σ.opp, .king⟩ := by
            rw [hk.2.2.2]
            exact source
          have arrived : (play q m).board m.dst = some ⟨σ.opp, .king⟩ := by
            cases promo : m.promo <;> simp [play, hsrc, ht, promo]
          have retained : (play q m).board m.dst = some ⟨σ, .rook⟩ := by
            rw [dst, material.2.2.2]
            exact krkBoard_rs material.1
          rw [arrived] at retained
          have bad := congrArg (fun o => o.map Piece.kind) retained
          cases bad
    · exact Or.inr ⟨w,b,kk,dead_of_legal_into_KK ⟨m,hm,rfl⟩ kk⟩
end EndgameChess.Rules
