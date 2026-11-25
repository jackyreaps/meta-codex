import MetaCodex

namespace MetaCodex.Examples

/-- A vacuous predicate disguised behind higher-dimensional parameters. -/
def vacuousManifoldTag (_dim : Nat) (_order : Nat) : Prop := True

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

-- Run all five MetaCodex audits:
#audit_theorem MetaCodex.Examples.demoHeadlineTheorem
#audit_fields demoHeadlineTheorem LayeredManifold
#audit_passthrough demoHeadlineTheorem
#audit_fibers demoHeadlineTheorem
#audit_inductives demoHeadlineTheorem

end MetaCodex.Examples
