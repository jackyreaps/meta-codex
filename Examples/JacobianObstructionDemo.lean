import MetaCodex

/-!
# JacobianObstructionDemo: Explicit 3-Curve Isogeny Descent Obstruction

Instantiates `MetaCodex.Abstractions.GradedLocalHierarchy` on a concrete 3-curve
isogeny family (`k = 2` finite local reduction states, `3 = k + 1` curves sharing the
same isogeny-invariant Frobenius trace fingerprint while carrying distinct analytic
regulators). Proves (`sorry`-free, pure Lean 4 core) that no bottom-up gluing function
`F` can uniformly reconstruct the analytic regulator from invariant + finite-local data alone.
-/

namespace MetaCodex.Examples

open MetaCodex.Abstractions

/-- Model of an elliptic curve / Jacobian entry carrying:
    - `traceFingerprint`: isogeny-invariant Frobenius trace data `{a_p}`
    - `tamagawaFiber`: finite local reduction state (`Fin 2`)
    - `regulatorScale`: scaled continuous analytic regulator `R_E` -/
structure MockJacobian where
  traceFingerprint : Nat
  tamagawaFiber : Fin 2
  regulatorScale : Nat

/-- Concrete `GradedLocalHierarchy` projecting `MockJacobian` onto `(InvLayer = Nat, Fin 2, Analytic = Nat)`. -/
def jacobianHierarchy : GradedLocalHierarchy MockJacobian Nat 2 Nat where
  projectInvariant := MockJacobian.traceFingerprint
  projectFiniteLocal := MockJacobian.tamagawaFiber
  analyticInvariant := MockJacobian.regulatorScale

/-- Three isogenous curves sharing `traceFingerprint = 101` (`{a_p}` invariant)
    with `tamagawaFiber : Fin 2` and pairwise distinct regulators (`14`, `28`, `56`). -/
def isogenyClassFamily : Fin 3 → MockJacobian
  | ⟨0, _⟩ => { traceFingerprint := 101, tamagawaFiber := ⟨0, by decide⟩, regulatorScale := 14 }
  | ⟨1, _⟩ => { traceFingerprint := 101, tamagawaFiber := ⟨1, by decide⟩, regulatorScale := 28 }
  | ⟨2, _⟩ => { traceFingerprint := 101, tamagawaFiber := ⟨0, by decide⟩, regulatorScale := 56 }

/-- **Concrete Jacobian Descent Obstruction Theorem:**
    No reconstruction map `F : Nat → Fin 2 → Nat` can uniformly recover `regulatorScale`
    across `isogenyClassFamily`. -/
theorem jacobian_isogeny_cannot_glue_regulator :
    ¬ ∃ (F : Nat → Fin 2 → Nat),
      ∀ i : Fin 3,
        F (jacobianHierarchy.projectInvariant (isogenyClassFamily i))
          (jacobianHierarchy.projectFiniteLocal (isogenyClassFamily i)) =
          jacobianHierarchy.analyticInvariant (isogenyClassFamily i) := by
  apply graded_hierarchy_descent_obstruction jacobianHierarchy isogenyClassFamily
  · intro i j
    match i, j with

    | ⟨0, _⟩, ⟨0, _⟩ | ⟨0, _⟩, ⟨1, _⟩ | ⟨0, _⟩, ⟨2, _⟩
    | ⟨1, _⟩, ⟨0, _⟩ | ⟨1, _⟩, ⟨1, _⟩ | ⟨1, _⟩, ⟨2, _⟩
    | ⟨2, _⟩, ⟨0, _⟩ | ⟨2, _⟩, ⟨1, _⟩ | ⟨2, _⟩, ⟨2, _⟩ => rfl
  · intro i j hNeq
    match i, j with

    | ⟨0, _⟩, ⟨0, _⟩ | ⟨1, _⟩, ⟨1, _⟩ | ⟨2, _⟩, ⟨2, _⟩ => exact False.elim (hNeq rfl)
    | ⟨0, _⟩, ⟨1, _⟩ | ⟨0, _⟩, ⟨2, _⟩ | ⟨1, _⟩, ⟨0, _⟩
    | ⟨1, _⟩, ⟨2, _⟩ | ⟨2, _⟩, ⟨0, _⟩ | ⟨2, _⟩, ⟨1, _⟩ => decide

-- Audit the Jacobian obstruction theorem with MetaCodex's linters:
#audit_theorem MetaCodex.Examples.jacobian_isogeny_cannot_glue_regulator
#audit_fields jacobian_isogeny_cannot_glue_regulator MockJacobian
#audit_fibers jacobian_isogeny_cannot_glue_regulator

end MetaCodex.Examples
