import EndgameChess.Rules.KRKDistanceParity
import EndgameChess.Rules.KRKFramedHistory

namespace EndgameChess.Rules.KRKThreePlyExact
open EndgameChess.KK RawHistoryLayer KRKHolding KRKHighClock KRKThreePly KRKLastReply KRKImmediate

/-- Exact three-ply history criterion at every clock, rather than only the
late-clock band in which it already evaluates the entire forced outcome. -/
theorem history_three_iff {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s) (turn : (erase s).turn = σ) :
    W σ 3 s ↔ ThreeHistory s.val sk rs wk := by
  constructor
  · intro win
    rcases win with goal | ⟨_, chosen | defended⟩
    · exact False.elim (opp_ne σ (turn.symm.trans goal.1))
    · obtain ⟨_, v, edge, child⟩ := chosen
      have childWin : F σ v := ⟨2, child⟩
      obtain ⟨_, clock⟩ := winning_child_quiet material edge childWin
      obtain ⟨m, legal, rawEq⟩ := edge
      have endpoint : erase v = play (erase s) m := congrArg RawTrace.erase rawEq
      obtain ⟨ns, nr, next⟩ := krk_strong_material material turn legal
      have nextV : IsKRK (erase v) σ ns nr wk := by rwa [endpoint]
      have nextTurn : (erase v).turn = σ.opp := by rw [endpoint, play_turn, turn]
      by_cases childOngoing : Ongoing v
      · obtain ⟨last, noClaim⟩ := (KRKLastReply.rule_two_iff nextV childOngoing nextTurn).mp child
        obtain ⟨u, reply, _⟩ := unique_legal_reply next
          (by rw [play_turn, turn]) (KRKEdgeDepth.arrival_far ⟨m, legal, rfl⟩ next) last
        have absent : ¬RawClaims.AvailableThreshold (RawTrace.append s.val m legal) := by
          change ¬RawClaims.AvailableThreshold v.val at noClaim
          rwa [rawEq] at noClaim
        have clear := (entry_no_claim_iff material turn legal next last reply).mp absent
        rcases last_entry_move material turn legal next last with
          ⟨src, promo, distance, moved, geometry⟩ | ⟨src, promo, sees, moved, geometry⟩
        · have canonical : m = ⟨sk, m.dst, none⟩ := by cases m; simp only [Move.mk.injEq]; exact ⟨src, True.intro, promo⟩
          right; left
          refine ⟨m.dst, u, distance, moved.1, KRKEdgeDepth.arrival_far ⟨m, legal, rfl⟩ moved, geometry, ?_, ?_, ?_⟩
          · rw [←canonical]; exact legal
          · rw [←canonical]; exact reply
          · rw [←canonical]; exact clear
        · have canonical : m = ⟨rs, m.dst, none⟩ := by cases m; simp only [Move.mk.injEq]; exact ⟨src, True.intro, promo⟩
          right; right
          refine ⟨m.dst, u, sees, Ne.symm moved.1, moved.2.2.1, geometry, ?_, ?_, ?_⟩
          · rw [←canonical]; exact legal
          · rw [←canonical]; exact reply
          · rw [←canonical]; exact clear
      · have goal := (terminal_force_iff_goal childOngoing).mp childWin
        exact Or.inl ((admitted_immediate_iff material ongoing turn).mp ⟨v, ⟨m, legal, rawEq⟩, goal⟩)
    · exact False.elim (opp_ne σ (turn.symm.trans defended.1))
  · intro criterion
    exact history_three_sufficient material ongoing turn criterion


theorem global_three_iff {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s) (turn : (erase s).turn = σ) :
    W σ 3 s ↔ KRKFramedHistory.GlobalClear s.val sk rs wk := by
  rw [history_three_iff material ongoing turn]
  constructor
  · intro history
    have depth := KRKFourPlyEscape.three_depth_zero (KRKWeakBranch.history_geometry history)
    have normal := KRKNativeFrame.normalize_spec depth
    exact ⟨depth,(KRKFramedHistory.history_iff (KRKNativeFrame.normalize wk) material turn normal.1 normal.2).mp history⟩
  · rintro ⟨depth,clear⟩
    have normal := KRKNativeFrame.normalize_spec depth
    exact (KRKFramedHistory.history_iff (KRKNativeFrame.normalize wk) material turn normal.1 normal.2).mpr clear

theorem not_immediate_not_two {s : State} {σ : Colour} {sk rs wk : Square}
    (material : IsKRK (erase s) σ sk rs wk) (ongoing : Ongoing s) (turn : (erase s).turn = σ) :
    ¬MateNow sk rs wk → ¬W σ 2 s := by
  intro notImmediate win
  have one := strong_two_to_one turn (raw_ruleMateWithin_project s σ 2 win)
  rcases one with goal | ⟨_, chosen | defended⟩
  · exact opp_ne σ (turn.symm.trans goal.1)
  · obtain ⟨_, r, legal, goal⟩ := chosen
    obtain ⟨v, edge, endpoint⟩ := layer.reply_complete ongoing legal
    change erase v = r at endpoint
    apply notImmediate
    apply (admitted_immediate_iff material ongoing turn).mp
    refine ⟨v, edge, ?_⟩
    change MateGoal σ (erase v)
    rwa [endpoint]
  · exact opp_ne σ (turn.symm.trans defended.1)
end EndgameChess.Rules.KRKThreePlyExact
