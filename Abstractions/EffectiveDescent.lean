import Paradox.TopologicalArtifact

/-!
# EffectiveDescent: Top-Down / Bottom-Up Mirroring & Jacobian Descent Obstructions

Formalizes (`sorry`-free, pure Lean 4 core) both sides of global-to-local hierarchies:
1. **Effective Descent (`MirrorAdjunction`):** When top-down projection `Δ` and bottom-up
   gluing `Γ` form an adjoint equivalence (`unit : ∀ g, Γ (Δ g) = g`), `Δ` is injective and
   no `TopologicalArtifact` fiber ambiguity can exist (`descent_eliminates_fiber_ambiguity`).
2. **Graded Local Hierarchy Obstruction (`graded_hierarchy_descent_obstruction`):**
   Models a two-layer arithmetic/geometric projection (`inv : Global → InvLayer`,
   e.g., isogeny-invariant traces `{a_p}`, paired with `finLocal : Global → Fin k`,
   e.g., finite local reduction data `{c_p}`). Proves via pure-core pigeonhole on `Fin k`
   that if an isogeny class contains `k + 1` curves with pairwise distinct analytic
   invariants (e.g., regulators `R_E`), no function `F : InvLayer → Fin k → Analytic`
   can uniformly reconstruct the analytic invariant.
-/

namespace MetaCodex.Abstractions

open MetaCodex.Paradox

/-- Exact mirroring (adjoint equivalence at the object level) between a global space `Global`
    and a local patch space `Local` via top-down projection `Δ` and bottom-up gluing `Γ`. -/
structure MirrorAdjunction (Global : Type u) (Local : Type v) where
  project : Global → Local
  glue : Local → Global
  unit : ∀ g : Global, glue (project g) = g
  counit : ∀ l : Local, project (glue l) = l
  triangle_left : ∀ g : Global, congrArg project (unit g) = counit (project g)
  triangle_right : ∀ l : Local, congrArg glue (counit l) = unit (glue l)

/-- **Vanishing Obstruction Theorem (`descent_eliminates_fiber_ambiguity`):**
    Under a `MirrorAdjunction`, top-down projection `Δ` is injective. -/
theorem descent_eliminates_fiber_ambiguity {Global : Type u} {Local : Type v}
    (adj : MirrorAdjunction Global Local) {g₁ g₂ : Global}
    (hShadow : adj.project g₁ = adj.project g₂) :
    g₁ = g₂ := by
  calc
    g₁ = adj.glue (adj.project g₁) := (adj.unit g₁).symm
    _ = adj.glue (adj.project g₂) := congrArg adj.glue hShadow
    _ = g₂ := adj.unit g₂

/-- **No Topological Artifacts Under Effective Descent:**
    When a `ProjectedSystem` is governed by a `MirrorAdjunction`, no two distinct
    `TopologicalArtifact`s can share the same target shadow. -/
theorem no_hidden_artifacts_under_descent {Global : Type u} {Local : Type v}
    (adj : MirrorAdjunction Global Local)
    (isValid : Global → Prop) (target : Local) :
    ¬ SharesShadowWithDistinctCarrier
      { isValid := isValid, project := adj.project } target := by
  rintro ⟨a₁, a₂, hNeq⟩
  have hProj : adj.project a₁.carrier = adj.project a₂.carrier :=
    a₁.projectsTo.trans a₂.projectsTo.symm
  exact hNeq (descent_eliminates_fiber_ambiguity adj hProj)

/-- **Round-Trip Collapse Theorem:**
    Every iterated global → local → global round-trip collapses to a single step. -/
theorem mirror_roundtrip_collapses {Global : Type u} {Local : Type v}
    (adj : MirrorAdjunction Global Local) (g : Global) :
    adj.glue (adj.project (adj.glue (adj.project g))) = g := by
  rw [adj.unit, adj.unit]

/-! ### Graded Local-to-Global Hierarchy & Jacobian Obstruction -/

/-- Pure Lean 4 core pigeonhole principle: no map `Fin (k + 1) → Fin k` is injective. -/
private theorem exists_collision_fin :
    ∀ {k : Nat} (f : Fin (k + 1) → Fin k),
      ∃ i j : Fin (k + 1), i ≠ j ∧ f i = f j
  | 0, f => Fin.elim0 (f ⟨0, Nat.zero_lt_succ 0⟩)
  | k + 1, f => by
    let last : Fin (k + 2) := ⟨k + 1, Nat.lt_succ_self (k + 1)⟩
    by_cases hHit : ∃ i : Fin (k + 1), f i.castSucc = f last
    · rcases hHit with ⟨i, hi⟩
      refine ⟨i.castSucc, last, ?_, hi⟩
      intro hEq
      have hVal := congrArg Fin.val hEq
      simp [last] at hVal
      omega
    · let g : Fin (k + 1) → Fin (k + 1) := fun i =>
        let y := f i.castSucc
        let z := f last
        if hLt : y.val < z.val then
          ⟨y.val, Nat.lt_of_lt_of_le hLt (Nat.le_of_lt_succ z.isLt)⟩
        else
          ⟨y.val - 1, by
            have hNe : y.val ≠ z.val := fun h => hHit ⟨i, Fin.ext h⟩
            have hy : y.val < k + 2 := y.isLt
            omega⟩
      rcases exists_collision_fin g with ⟨i, j, hNeq, hEqG⟩
      refine ⟨i.castSucc, j.castSucc, fun h => hNeq (Fin.castSucc_inj.mp h), ?_⟩
      dsimp [g] at hEqG
      split at hEqG <;> split at hEqG
      · exact Fin.ext (congrArg Fin.val hEqG)
      · rename_i h1 h2
        have hVal := congrArg Fin.val hEqG
        simp at hVal
        have hNe2 : (f j.castSucc).val ≠ (f last).val := fun h => hHit ⟨j, Fin.ext h⟩
        omega
      · rename_i h1 h2
        have hVal := congrArg Fin.val hEqG
        simp at hVal
        have hNe1 : (f i.castSucc).val ≠ (f last).val := fun h => hHit ⟨i, Fin.ext h⟩
        omega
      · rename_i h1 h2
        have hVal := congrArg Fin.val hEqG
        simp at hVal
        have hNe1 : (f i.castSucc).val ≠ (f last).val := fun h => hHit ⟨i, Fin.ext h⟩
        have hNe2 : (f j.castSucc).val ≠ (f last).val := fun h => hHit ⟨j, Fin.ext h⟩
        exact Fin.ext (by omega)

/-- A two-tier global-to-local hierarchy separating an invariant layer (`InvLayer`,
    such as isogeny-invariant `{a_p}` traces) from a finite local layer (`Fin k`,
    such as discrete Tamagawa/reduction data `{c_p}`) and a continuous analytic target
    (`Analytic`, such as the real regulator `R_E`). -/
structure GradedLocalHierarchy (Global : Type u) (InvLayer : Type v)
    (k : Nat) (Analytic : Type w) where
  projectInvariant : Global → InvLayer
  projectFiniteLocal : Global → Fin k
  analyticInvariant : Global → Analytic

/-- **Finite-to-Continuum Descent Obstruction (Jacobian Isogeny Theorem):**
    If `k + 1` global objects share the same `projectInvariant` layer (`{a_p}`)
    while having pairwise distinct `analyticInvariant` values (`R_E`), then by
    pigeonhole on `Fin k`, two distinct objects share both `projectInvariant` and
    `projectFiniteLocal`, so NO reconstruction map `F : InvLayer → Fin k → Analytic`
    can uniformly recover `analyticInvariant`. -/
theorem graded_hierarchy_descent_obstruction
    {Global : Type u} {InvLayer : Type v} {k : Nat} {Analytic : Type w}
    (H : GradedLocalHierarchy Global InvLayer k Analytic)
    (family : Fin (k + 1) → Global)
    (hSameInv : ∀ i j : Fin (k + 1),
      H.projectInvariant (family i) = H.projectInvariant (family j))
    (hDistinctAnalytic : ∀ i j : Fin (k + 1), i ≠ j →
      H.analyticInvariant (family i) ≠ H.analyticInvariant (family j)) :
    ¬ ∃ (F : InvLayer → Fin k → Analytic),
      ∀ i : Fin (k + 1),
        F (H.projectInvariant (family i)) (H.projectFiniteLocal (family i)) =
          H.analyticInvariant (family i) := by
  rintro ⟨F, hF⟩
  rcases exists_collision_fin (fun i => H.projectFiniteLocal (family i)) with
    ⟨i, j, hNeq, hSameFin⟩
  have hEqAnalytic : H.analyticInvariant (family i) = H.analyticInvariant (family j) := by
    calc
      H.analyticInvariant (family i)
        = F (H.projectInvariant (family i)) (H.projectFiniteLocal (family i)) := (hF i).symm
      _ = F (H.projectInvariant (family j)) (H.projectFiniteLocal (family j)) := by
        rw [hSameInv i j, hSameFin]
      _ = H.analyticInvariant (family j) := hF j
  exact hDistinctAnalytic i j hNeq hEqAnalytic

end MetaCodex.Abstractions
