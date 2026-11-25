import Paradox.TopologicalArtifact

/-!
# EffectiveDescent: Top-Down / Bottom-Up Mirroring & Jacobian Descent Obstructions

Formalizes (`sorry`-free, pure Lean 4 core) both sides of global-to-local hierarchies:

1. **Effective Descent (`MirrorAdjunction`):** When top-down projection `Δ` and
   bottom-up gluing `Γ` form an object-level equivalence, `Δ` is injective and no
   `TopologicalArtifact` fiber ambiguity can exist.

2. **Graded Local Hierarchy Obstruction (`graded_hierarchy_descent_obstruction`):**
   Models a two-layer projection (invariant layer + finite local layer). Proves via
   pure-core pigeonhole on `Fin k` that if an isogeny class contains `k + 1` curves
   with pairwise distinct analytic invariants, no function
   `F : InvLayer → Fin k → Analytic` can uniformly reconstruct the analytic invariant.

3. **Partial Descent Fiber Refinement (`partial_descent_fiber_refinement`):**
   Adjoining any finite auxiliary invariant `auxLocal : Global → Fin m` still cannot
   recover `analyticInvariant` on any invariant family of size `k * m + 1`.
-/

namespace MetaCodex.Abstractions

open MetaCodex.Paradox

/-- Strict object-level equivalence between a global space and a local patch space. -/
structure MirrorAdjunction (Global : Type u) (Local : Type v) where
  project : Global → Local
  glue : Local → Global
  unit : ∀ g : Global, glue (project g) = g
  counit : ∀ l : Local, project (glue l) = l
  triangle_left : ∀ g : Global, congrArg project (unit g) = counit (project g)
  triangle_right : ∀ l : Local, congrArg glue (counit l) = unit (glue l)

/-- Under a MirrorAdjunction, top-down projection is injective. -/
theorem descent_eliminates_fiber_ambiguity {Global : Type u} {Local : Type v}
    (adj : MirrorAdjunction Global Local) {g₁ g₂ : Global}
    (hShadow : adj.project g₁ = adj.project g₂) :
    g₁ = g₂ := by
  calc
    g₁ = adj.glue (adj.project g₁) := (adj.unit g₁).symm
    _  = adj.glue (adj.project g₂) := congrArg adj.glue hShadow
    _  = g₂ := adj.unit g₂

/-- No two distinct TopologicalArtifacts can share the same target shadow under descent. -/
theorem no_hidden_artifacts_under_descent {Global : Type u} {Local : Type v}
    (adj : MirrorAdjunction Global Local)
    (isValid : Global → Prop) (target : Local) :
    ¬ SharesShadowWithDistinctCarrier
      { isValid := isValid, project := adj.project } target := by
  rintro ⟨a₁, a₂, hNeq⟩
  have hProj : adj.project a₁.carrier = adj.project a₂.carrier :=
    a₁.projectsTo.trans a₂.projectsTo.symm
  exact hNeq (descent_eliminates_fiber_ambiguity adj hProj)

/-- Every iterated global → local → global round-trip collapses to a single step. -/
theorem mirror_roundtrip_collapses {Global : Type u} {Local : Type v}
    (adj : MirrorAdjunction Global Local) (g : Global) :
    adj.glue (adj.project (adj.glue (adj.project g))) = g := by
  rw [adj.unit, adj.unit]

/-! ### Graded Local-to-Global Hierarchy & Jacobian Obstruction -/

/-- Pure Lean 4 core pigeonhole: no map `Fin (k + 1) → Fin k` is injective. -/
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
    · let g : Fin (k + 1) → Fin k := fun i =>
        let y := f i.castSucc
        let z := f last
        if hLt : y.val < z.val then
          ⟨y.val, by
            have hz : z.val < k + 1 := z.isLt
            omega⟩
        else
          ⟨y.val - 1, by
            have hNe : y.val ≠ z.val := fun h => hHit ⟨i, Fin.ext h⟩
            have hy : y.val < k + 1 := y.isLt
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

/-- Two-tier hierarchy: invariant layer, finite local layer, continuous analytic target. -/
structure GradedLocalHierarchy (Global : Type u) (InvLayer : Type v)
    (k : Nat) (Analytic : Type w) where
  projectInvariant : Global → InvLayer
  projectFiniteLocal : Global → Fin k
  analyticInvariant : Global → Analytic

/-- Distinct analytic invariants force distinct global objects in the family. -/
theorem family_injective_of_distinct_analytic
    {Global : Type u} {InvLayer : Type v} {k : Nat} {Analytic : Type w}
    (H : GradedLocalHierarchy Global InvLayer k Analytic)
    (family : Fin (k + 1) → Global)
    (hDistinctAnalytic : ∀ i j : Fin (k + 1), i ≠ j →
      H.analyticInvariant (family i) ≠ H.analyticInvariant (family j)) :
    ∀ i j : Fin (k + 1), i ≠ j → family i ≠ family j := by
  intro i j hNeq hEqObj
  exact hDistinctAnalytic i j hNeq (congrArg H.analyticInvariant hEqObj)

/-- Finite-to-continuum descent obstruction (Jacobian isogeny shape). -/
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

/-- Partial descent: adjoining Fin m still fails on a family of size k * m + 1. -/
theorem partial_descent_fiber_refinement
    {Global : Type u} {InvLayer : Type v} {k m : Nat} {Analytic : Type w}
    (H : GradedLocalHierarchy Global InvLayer k Analytic)
    (auxLocal : Global → Fin m)
    (family : Fin (k * m + 1) → Global)
    (hSameInv : ∀ i j : Fin (k * m + 1),
      H.projectInvariant (family i) = H.projectInvariant (family j))
    (hDistinctAnalytic : ∀ i j : Fin (k * m + 1), i ≠ j →
      H.analyticInvariant (family i) ≠ H.analyticInvariant (family j)) :
    ¬ ∃ (F : InvLayer → Fin k → Fin m → Analytic),
      ∀ i : Fin (k * m + 1),
        F (H.projectInvariant (family i))
          (H.projectFiniteLocal (family i))
          (auxLocal (family i)) =
          H.analyticInvariant (family i) := by
  rintro ⟨F, hF⟩
  let combined : GradedLocalHierarchy Global InvLayer (k * m) Analytic :=
    { projectInvariant := H.projectInvariant
      projectFiniteLocal := fun g =>
        ⟨(H.projectFiniteLocal g).val * m + (auxLocal g).val, by
          have hk : (H.projectFiniteLocal g).val < k := (H.projectFiniteLocal g).isLt
          have hm : (auxLocal g).val < m := (auxLocal g).isLt
          have h1 : ((H.projectFiniteLocal g).val + 1) * m ≤ k * m :=
            Nat.mul_le_mul_right m hk
          rw [Nat.add_mul, Nat.one_mul] at h1
          omega⟩
      analyticInvariant := H.analyticInvariant }
  apply graded_hierarchy_descent_obstruction combined family hSameInv hDistinctAnalytic
  refine ⟨fun inv idx =>
    F inv ⟨idx.val / m, by
        have hIdx : idx.val < k * m := idx.isLt
        have hmPos : 0 < m := by
          cases m with
          | zero => simp at hIdx
          | succ m' => exact Nat.zero_lt_succ m'
        exact (Nat.div_lt_iff_lt_mul hmPos).mpr hIdx⟩
      ⟨idx.val % m, by
        have hIdx : idx.val < k * m := idx.isLt
        have hmPos : 0 < m := by
          cases m with
          | zero => simp at hIdx
          | succ m' => exact Nat.zero_lt_succ m'
        exact Nat.mod_lt idx.val hmPos⟩, ?_⟩
  intro i
  have hm : (auxLocal (family i)).val < m := (auxLocal (family i)).isLt
  have hmPos : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le _) hm
  have hDiv :
      ((H.projectFiniteLocal (family i)).val * m + (auxLocal (family i)).val) / m =
        (H.projectFiniteLocal (family i)).val := by
    rw [Nat.mul_comm, Nat.mul_add_div hmPos, Nat.div_eq_of_lt hm, Nat.add_zero]
  have hMod :
      ((H.projectFiniteLocal (family i)).val * m + (auxLocal (family i)).val) % m =
        (auxLocal (family i)).val := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hm]
  have hIdxFst :
      (⟨(combined.projectFiniteLocal (family i)).val / m, by
        have hIdx := (combined.projectFiniteLocal (family i)).isLt
        exact (Nat.div_lt_iff_lt_mul hmPos).mpr hIdx⟩ : Fin k) =
        H.projectFiniteLocal (family i) :=
    Fin.ext hDiv
  have hIdxSnd :
      (⟨(combined.projectFiniteLocal (family i)).val % m, by
        exact Nat.mod_lt _ hmPos⟩ : Fin m) =
        auxLocal (family i) :=
    Fin.ext hMod
  dsimp [combined]
  rw [hIdxFst, hIdxSnd]
  exact hF i

end MetaCodex.Abstractions
