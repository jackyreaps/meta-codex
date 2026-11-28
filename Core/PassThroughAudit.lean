import Core.FieldProjection

/-!
# PassThroughAudit: Unused & Bypassed Hypothesis Scanner

Provides `#audit_passthrough <theoremName>`, inspecting every declaration in
`<theoremName>`'s transitive dependency cone to detect `Prop`-typed binder arguments
that are accepted in the signature but never referenced in the proof term.
-/

namespace MetaCodex.Core

open Lean Elab Command Meta

private partial def usesFVar (target : FVarId) : Expr → Bool
  | .fvar id => id == target

  | .app fn arg => usesFVar target fn || usesFVar target arg
  | .lam _ ty body _ | .forallE _ ty body _ => usesFVar target ty || usesFVar target body
  | .letE _ ty val body _ => usesFVar target ty || usesFVar target val || usesFVar target body
  | .mdata _ inner | .proj _ _ inner => usesFVar target inner
  | _ => false

/-- Check a single constant's `lambdaTelescope` for `Prop` hypotheses never used in its body. -/
private def checkUnusedPropBinders (cName : Name) : MetaM (Array Name) := do
  let env ← getEnv
  let some cinfo := env.find? cName | return #[]
  let some val := cinfo.value? (allowOpaque := true) | return #[]
  lambdaTelescope val fun xs body => do
    let mut unused : Array Name := #[]
    for x in xs do
      let ldecl ← x.fvarId!.getDecl
      if !ldecl.binderInfo.isInstImplicit then
        if ← isProp ldecl.type then
          if !usesFVar x.fvarId! body then
            unused := unused.push ldecl.userName
    return unused

/-- `#audit_passthrough <theoremName>` reports declarations in `<theoremName>`'s active cone
    that accept `Prop` hypotheses without ever referencing them in the proof body. -/
elab "#audit_passthrough " thmId:ident : command => do
  let thmName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo thmId
  let env ← getEnv
  let cone := collectActiveCone env thmName
  let mut findings : Array (Name × Array Name) := #[]
  for c in cone do
    let unused ← liftTermElabM <| checkUnusedPropBinders c
    if !unused.isEmpty then
      findings := findings.push (c, unused)
  logInfo m!"=== Hypothesis Pass-Through Audit: `{thmName}` ({cone.size} active constants) ==="
  if findings.isEmpty then
    logInfo m!"  [CLEAN] Every `Prop` hypothesis in the active cone is referenced in its proof body."
  else
    for (c, vars) in findings do
      logWarning m!"  [UNUSED HYP] `{c}` never references `Prop` binder(s): {vars.toList}"

end MetaCodex.Core
