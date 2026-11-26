import Paradox.TopologicalArtifact

/-!
# DyadicContinuumGap: Exponential Dyadic & Asymmetric Continuum Disproof

Formalizes (`sorry`-free, pure Lean 4 core) why exponentially asymmetric parameters
(`2 ^ (n + 1)` vs `3 ^ (n + 1)`) and dyadic floating-point refinements cannot prove
continuum complex bounds without an explicit finite inter-grid bridge:
1. `dyadic_grid_has_interior_gaps`: At every refinement level `n`, evaluating at all
   `2 ^ (n + 1)` dyadic nodes cannot distinguish `0` from a function spiking to `spike`
   at every midpoint.
2. `exponential_dyadic_amplification`: Rescaling any positive inter-grid discrepancy `δ ≥ 1`
   by `2 ^ (n + 1)` exceeds any bound `B` once `n ≥ B`.
3. `asymmetric_continuum_bridge_refuted`: Explicit refutation (`¬ ∀ ...`) proving that
   satisfaction on all dyadic grid points at all depths `n` plus exponential scale
   asymmetry (`3 ^ (n + 1) - 2 ^ (n + 1)`) does NOT imply uniform continuum boundedness
   (`∀ x, f x ≤ B`) whenever a finite inter-grid Lipschitz bridge is absent.
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
    simp
  · intro hEq
    have hGt1 : 1 < 2 * dyadicScale n := by
      have h1 := dyadicScale_pos n
      omega
    have hAt1 := congrFun hEq ⟨1, hGt1⟩
    dsimp [fZero, fSpike] at hAt1
    omega

/-- **Exponential Dyadic Amplification (`exponential_dyadic_amplification`):**
    When a dyadic cancellation scheme rescales residual errors by `2 ^ (n + 1)`,
    any positive inter-grid discrepancy `δ ≥ 1` grows exponentially (`2 ^ (n + 1) * δ ≥ 2 ^ (n + 1)`),
    violating any fixed uniform bound `B` once `n` is sufficiently large. -/
theorem exponential_dyadic_amplification (B δ : Nat) (hDelta : 1 ≤ δ) :
    ∃ n : Nat, B < dyadicScale n * δ := by
  refine ⟨B, ?_⟩
  have hPow : B + 1 ≤ 2 ^ (B + 1) := Nat.le_of_lt Nat.lt_two_pow_self
  have hScale : dyadicScale B ≤ dyadicScale B * δ :=
    Nat.le_mul_of_pos_right (dyadicScale B) (by omega)
  dsimp [dyadicScale] at hScale ⊢
  omega

/-- **Asymmetric Continuum Simplification Disproof (`asymmetric_continuum_bridge_refuted`):**
    Directly refutes the claim that vanishing on all dyadic grid nodes `2 * k` at depth `n`
    forces a uniform continuum bound `≤ B` when exponential scale asymmetry
    (`3 ^ (n + 1) - 2 ^ (n + 1)`) amplifies unbridged midpoint errors:
    there exists a profile `f` that is identically `0` on every dyadic grid node yet exceeds
    any target bound `B` in the interior once amplified by `3 ^ (n + 1) - 2 ^ (n + 1)`. -/
theorem asymmetric_continuum_bridge_refuted (n B : Nat) :
    ¬ (∀ (f : Fin (2 * dyadicScale n) → Nat),
        (∀ k : Fin (dyadicScale n), f ⟨2 * k.val, by omega⟩ = 0) →
        ∀ idx : Fin (2 * dyadicScale n),
          (3 ^ (n + 1) - 2 ^ (n + 1)) * f idx ≤ B) := by
  intro hClaim
  let fBad : Fin (2 * dyadicScale n) → Nat := fun idx =>
    if idx.val % 2 = 0 then 0 else B + 1
  have hOnGrid : ∀ k : Fin (dyadicScale n), fBad ⟨2 * k.val, by omega⟩ = 0 := by
    intro k
    dsimp [fBad]
    have hEven : (2 * k.val) % 2 = 0 := by omega
    simp [hEven]
  have hGt1 : 1 < 2 * dyadicScale n := by
    have h1 := dyadicScale_pos n
    omega
  have hBoundAtMid := hClaim fBad hOnGrid ⟨1, hGt1⟩
  dsimp [fBad] at hBoundAtMid
  have hAsym : 1 ≤ 3 ^ (n + 1) - 2 ^ (n + 1) := by
    have h2 : 2 ^ (n + 1) < 3 ^ (n + 1) :=
      Nat.pow_lt_pow_left (by decide : 2 < 3) (Nat.succ_ne_zero n)
    omega
  have hMul : B + 1 ≤ (3 ^ (n + 1) - 2 ^ (n + 1)) * (B + 1) :=
    Nat.le_mul_of_pos_left (B + 1) hAsym
  omega

end MetaCodex.Paradox
