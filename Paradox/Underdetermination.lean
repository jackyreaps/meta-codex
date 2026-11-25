/-!
# Underdetermination: Uncoupled Existential Bounds & Violating Streams

Generalizes the boundary countermodel pattern (`Disproof.lean`): whenever an interface
existentially quantifies a lower bound `∃ C₀, C₀ ≤ mass` without coupling `C₀` to the
target `budget`, an infinite ascending stream of witnesses (`mass = budget + k + 1`)
satisfies the interface while strictly violating `mass ≤ budget`.
-/

namespace MetaCodex.Paradox

/-- Models an interface where an existential parameter `C₀` is coupled to `mass`
    (`∃ C₀, C₀ ≤ mass`) but left uncoupled from the target `budget`. -/
def UncoupledExistentialInterface (mass _budget : Nat) : Prop :=
  ∃ C₀ : Nat, C₀ ≤ mass

/-- **Infinite Violating Stream Theorem:**
    For every `budget : Nat` and every offset `k : Nat`, setting `mass := budget + k + 1`
    inhabits `UncoupledExistentialInterface` while strictly violating `mass ≤ budget`. -/
theorem infinite_violating_stream (budget k : Nat) :
    UncoupledExistentialInterface (budget + k + 1) budget ∧
    ¬ (budget + k + 1 ≤ budget) := by
  refine ⟨⟨budget + k + 1, Nat.le_refl _⟩, ?_⟩
  omega

/-- **General Interface Refutation Theorem:**
    No universal claim `∀ mass, UncoupledExistentialInterface mass budget → mass ≤ budget`
    can hold for any `budget : Nat`. -/
theorem uncoupled_interface_does_not_force_bound (budget : Nat) :
    ¬ (∀ mass : Nat, UncoupledExistentialInterface mass budget → mass ≤ budget) := by
  intro hAll
  have ⟨hSat, hViol⟩ := infinite_violating_stream budget 0
  exact hViol (hAll (budget + 0 + 1) hSat)

end MetaCodex.Paradox
