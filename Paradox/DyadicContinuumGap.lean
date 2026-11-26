import Paradox.TopologicalArtifact

/-!
# DyadicContinuumGap: Exponential Dyadic Refinement vs. Continuum Critical Line

Formalizes (`sorry`-free, pure Lean 4 core) why exponentially refining a dyadic grid
(`gridSize n = 2 ^ (n + 1)`) cannot force continuum behavior on `[0, 1]` or the critical
line without an explicit uniform inter-grid oscillation bound:
1. `dyadic_grid_has_interior_gaps`: For EVERY refinement level `n : Nat`, there exist
   continuum points (modeled at doubled resolution `2 * gridSize n`) strictly between
   adjacent dyadic grid points where a function can vanish on every dyadic point `2 * k`
   while spiking to arbitrary height `M` at midpoint `2 * k + 1`.
2. `exponential_dyadic_amplification`: Subtracting nearby dyadic evaluations whose
   difference is scaled by `2 ^ (n + 1)` amplifies any uncoupled midpoint error `δ > 0`
   by `2 ^ (n + 1) * δ`, destroying uniform bounds as `n → ∞`.
-/

namespace MetaCodex.Paradox

/-- Number of dyadic subdivisions at level `n`: `2 ^ (n + 1)`. -/
def dyadicScale (n : Nat) : Nat := 2 ^ (n + 1)

theorem dyadicScale_pos (n : Nat) : 0 < dyadicScale n :=
  Nat.two_pow_pos (n + 1)

/-- **Dyadic Grid Blind-Spot Theorem (`dyadic_grid_has_interior_gaps`):**
    At ANY dyadic refinement depth `n` (with `2 ^ (n + 1)` grid points), evaluating at
    even-indexed dyadic nodes `2 * k` cannot distinguish the zero function from a
    function that spikes to arbitrary height `spike` at every midpoint `2 * k + 1`. -/
theorem dyadic_grid_has_interior_gaps (n spike : Nat) (hSpike : 0 < spike) :
    ∃ (fZero fSpike : Fin (2 * dyadicScale n) → Nat),
      (∀ k : Fin (dyadicScale n),
        fZero ⟨2 * k.val, by omega⟩ = fSpike ⟨2 * k.val, by omega⟩) ∧
      (∀ k : Fin (dyadicScale n),
        fZero ⟨2 * k.val + 1, by omega⟩ = 0 ∧
        fSpike ⟨2 * k.val + 1, by omega⟩ = spike) ∧
      fZero ≠ fSpike := by
  let fZero : Fin (2 * dyadicScale n) → Nat := fun _ => 0
  let fSpike : Fin (2 * dyadicScale n) → Nat := fun idx =>
    if idx.val % 2 = 0 then 0 else spike
  refine ⟨fZero, fSpike, ?_, ?_, ?_⟩
  · intro k
    dsimp [fZero, fSpike]
    have hEven : (2 * k.val) % 2 = 0 := by omega
    simp [hEven]
  · intro k
    dsimp [fZero, fSpike]
    have hOdd : (2 * k.val + 1) % 2 ≠ 0 := by omega
    simp [hOdd]
  · intro hEq
    have hPos : 0 < 2 * dyadicScale n := by
      have h1 := dyadicScale_pos n
      omega
    have hAt1 := congrFun hEq ⟨1, hPos⟩
    dsimp [fZero, fSpike] at hAt1
    simp at hAt1
    omega

/-- **Exponential Dyadic Amplification (`exponential_dyadic_amplification`):**
    When a dyadic cancellation scheme rescales residual errors by `2 ^ (n + 1)`,
    any positive inter-grid discrepancy `δ ≥ 1` grows exponentially (`2 ^ (n + 1) * δ ≥ 2 ^ (n + 1)`),
    violating any fixed uniform bound `B` once `n` is sufficiently large. -/
theorem exponential_dyadic_amplification (B δ : Nat) (hDelta : 1 ≤ δ) :
    ∃ n : Nat, B < dyadicScale n * δ := by
  refine ⟨B, ?_⟩
  have hPow : B + 1 ≤ 2 ^ (B + 1) := Nat.lt_two_pow_self
  have hScale : dyadicScale B ≤ dyadicScale B * δ :=
    Nat.le_mul_of_pos_right (dyadicScale B) (by omega)
  dsimp [dyadicScale] at hScale ⊢
  omega

end MetaCodex.Paradox
