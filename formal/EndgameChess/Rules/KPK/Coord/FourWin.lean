import EndgameChess.Rules.KPK.Coord.Four6

/-! Fourth rank, the winning side: basic facts. A push from the fourth rank wins when the
lone king, to move on the fifth rank, can neither take the pawn nor step into the
fifth-rank guard: the proved fifth-rank cover then gives every reply a winning phase. A
position is outside the fourth-rank draw region when such a push is available, or when
some king step leaves the lone king no capture and no answer into the region. -/
namespace EndgameChess.Rules.KPK.Coord

/-- Lone king to move on the fifth rank, lost: no capture, and no step into the guard. -/
def Lost4 (a b c e f : Nat) : Prop :=
  ¬ Capture a b c 4 e f ∧ ∀ X Y, WeakStep a b c 4 e f X Y → ¬ S4 a b c X Y

/-- A winning push from the fourth rank. -/
def PushOK3 (a b c e f : Nat) : Prop := Free a b e f c 4 ∧ Lost4 a b c e f

/-- A lost fifth-rank position for the lone king is a fifth-rank winning position of the
plan, with phase at most 13. -/
theorem lost4_w4win {a b c e f : Nat} (D : Dom a b c 4 e f) (hc : 1 ≤ c) (h : Lost4 a b c e f) :
    W4win 13 a b c e f :=
  ⟨h.1, weak_reply D (Or.inr (Or.inl (Nat.le_refl 4))) h.1,
    fun X Y st => ⟨h.2 X Y st, five_cover (domS_reply D st) hc (h.2 X Y st)⟩⟩

theorem not_w4 {a b c e f : Nat} (h : Lost4 a b c e f) : ¬ W4 a b c e f := by
  rintro (cap | ⟨X, Y, st, s⟩)
  · exact h.1 cap
  · exact h.2 X Y st s

/-- A winning push puts a position outside the fourth-rank draw region. -/
theorem pushok3_not_r5 {a b c e f : Nat} (D : DomS a b c 3 e f) (hc : 1 ≤ c)
    (h : PushOK3 a b c e f) : ¬ R5 a b c e f :=
  fun r => not_w4 h.2 (r5_push D hc r h.1)

/-- A king step after which the lone king can neither take the pawn nor answer into the
region puts a position outside the region. -/
theorem step_not_r5 {a b c e f x y : Nat} (D : DomS a b c 3 e f) (hc : 1 ≤ c)
    (st : KingStep a b c 3 e f x y) (keep : ¬ Capture x y c 3 e f)
    (out : ∀ X Y, WeakStep x y c 3 e f X Y → ¬ R5 x y c X Y) : ¬ R5 a b c e f := by
  intro r
  rcases r5_king D hc r st with cap | ⟨X, Y, ws, q⟩
  · exact keep cap
  · exact out X Y ws q

/-- The same against the explicit part: a step whose replies all avoid it, from a tempo
position's slice, leaves the tempo slice. -/
theorem step_not_t5 {a b c e f x y : Nat} (st : KingStep a b c 3 e f x y)
    (keep : ¬ Capture x y c 3 e f) (out : ∀ X Y, WeakStep x y c 3 e f X Y → ¬ C5 x y c X Y) :
    ¬ T5 a b c e f := by
  rintro ⟨-, k, -⟩
  rcases k x y st with cap | ⟨X, Y, ws, q⟩
  · exact keep cap
  · exact out X Y ws q

theorem push_not_t5 {a b c e f : Nat} (h : PushOK3 a b c e f) : ¬ T5 a b c e f := by
  rintro ⟨-, -, p⟩
  exact not_w4 h.2 (p h.1)

end EndgameChess.Rules.KPK.Coord
