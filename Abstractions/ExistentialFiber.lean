import MetaCodex.Core.FieldProjection

/-!
# ExistentialFiber: Structural Fiber Unidentifiability Audit

Provides `#audit_fibers <theoremName>`, scanning `<theoremName>`'s active dependency
cone for `Exists`-quantified signatures (`∃ x : α, P x`) that may project out
higher-dimensional structural parameters before reaching the conclusion.
-/

namespace MetaCodex.Abstractions

open Lean Elab Command
open MetaCodex.Core

private partial def containsExists (e : Expr) : Bool :=
  match e with
  | .const ``Exists _ => true

  | .app fn arg => containsExists fn || containsExists arg
  | .lam _ ty body _ | .forallE _ ty body _ => containsExists ty || containsExists body
  | .letE _ ty val body _ => containsExists ty || containsExists val || containsExists body
  | .mdata _ inner | .proj _ _ inner => containsExists inner
  | _ => false

/-- `#audit_fibers <theoremName>` reports intermediate declarations in `<theoremName>`'s
    transitive cone that introduce `Exists` quantifiers in their signatures. -/
elab "#audit_fibers " thmId:ident : command => do
  let thmName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo thmId
  let env ← getEnv
  let cone := collectActiveCone env thmName
  let mut hits : Array Name := #[]
  for c in cone do
    if let some cinfo := env.find? c then
      if containsExists cinfo.type then
        hits := hits.push c
  logInfo m!"=== Existential Fiber Audit: `{thmName}` ({cone.size} active constants) ==="
  if hits.isEmpty then
    logInfo m!"  [IDENTIFIABLE] No `Exists`-quantified intermediate signatures in active cone."
  else
    for h in hits do
      logWarning m!"  [FIBER] `{h}` introduces an `Exists` fiber (review whether structural parameters are recoverable)."

end MetaCodex.Abstractions
