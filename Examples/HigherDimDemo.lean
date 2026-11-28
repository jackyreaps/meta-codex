import MetaCodex

namespace MetaCodex.Examples

/-- A vacuous predicate disguised behind higher-dimensional parameters. -/
def vacuousManifoldTag (_dim : Nat) (_order : Nat) : Prop := True

/-- An `opaque` vacuous tag verifying that `allowOpaque := true` still catches it. -/
opaque opaqueVacuousTag : True := trivial

/-- A layered `Type`-valued structure carrying both an active bound and a passive tag. -/
structure LayeredManifold where
  activeBound : Nat
  passiveTag : vacuousManifoldTag 24 120

def transportManifold (h : vacuousManifoldTag 24 120) : LayeredManifold :=
  { activeBound := 4, passiveTag := h }

def existentialFiberHypothesis : Prop :=
  ∃ (ambientDim : Nat), 8 ≤ ambientDim

/-- Notice `_hf` is accepted as a `Prop` hypothesis and never referenced in the proof body
    (`#audit_passthrough` flags this automatically). -/
theorem demoHeadlineTheorem (_hf : existentialFiberHypothesis) : 2 ≤ 4 := by
  let m := transportManifold trivial
  have hBound : m.activeBound = 4 := rfl
  omega

/-- Helper theorem referencing `opaqueVacuousTag` to verify `allowOpaque := true` detection. -/
theorem opaqueTagTheorem : 1 ≤ 2 := by
  let _ := opaqueVacuousTag
  omega

-- Run all five MetaCodex audits (including opaque-safe vacuity detection):
#audit_theorem MetaCodex.Examples.demoHeadlineTheorem
#audit_theorem MetaCodex.Examples.opaqueTagTheorem
#audit_fields demoHeadlineTheorem LayeredManifold
#audit_passthrough demoHeadlineTheorem
#audit_fibers demoHeadlineTheorem
#audit_inductives demoHeadlineTheorem

/-- Uses a core lemma: no cone walk should enter the core library to reach `Nat.add_comm`. -/
theorem demoUsesCoreLemma (a b : Nat) : a + b = b + a := Nat.add_comm a b

#audit_theorem MetaCodex.Examples.demoUsesCoreLemma

-- Fails the build if either cone walk (ConeAudit's or FieldProjection's) contains `Nat.add_comm`.
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  if (MetaCodex.Core.collectOpaqueSafeCone env ``demoUsesCoreLemma).1.contains ``Nat.add_comm ||
      (MetaCodex.Core.collectActiveCone env ``demoUsesCoreLemma).contains ``Nat.add_comm then
    throwError "a cone walk entered the core library (Nat.add_comm)"
  IO.println "ok: neither cone walk contains Nat.add_comm"

end MetaCodex.Examples
