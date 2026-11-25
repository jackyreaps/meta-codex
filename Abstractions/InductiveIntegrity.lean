import Core.FieldProjection

/-!
# InductiveIntegrity: Recursive & Mutual Inductive Metadata Audit

Provides `#audit_inductives <theoremName>`, verifying that mutual and nested inductive
types reachable from `<theoremName>` maintain consistent `numParams` metadata across
all sibling declarations.
-/

namespace MetaCodex.Abstractions

open Lean Elab Command
open MetaCodex.Core

/-- `#audit_inductives <theoremName>` checks mutual inductive parameter consistency
    across all inductive types in `<theoremName>`'s transitive dependency cone. -/
elab "#audit_inductives " thmId:ident : command => do
  let thmName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo thmId
  let env ← getEnv
  let cone := collectActiveCone env thmName
  let mut checked : Nat := 0
  let mut anomalies : Array Name := #[]
  for c in cone do
    if let some (.inductInfo ival) := env.find? c then
      checked := checked + 1
      for sib in ival.all do
        if let some (.inductInfo sival) := env.find? sib then
          if sival.numParams != ival.numParams then
            anomalies := anomalies.push c
  logInfo m!"=== Inductive Metadata Audit: `{thmName}` ({checked} inductive types checked) ==="
  if anomalies.isEmpty then
    logInfo m!"  [CONSISTENT] All mutual inductive parameter counts match across active cone."
  else
    for a in anomalies do
      logError m!"  [ANOMALY] `{a}` has mismatched mutual inductive `numParams` metadata."

end MetaCodex.Abstractions
