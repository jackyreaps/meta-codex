import Lean
import Core.ConeAudit

/-!
# FieldProjection: Structure Field Opening & Passive Transport Audit

Provides `#audit_fields <theoremName> <StructureName>`, walking `<theoremName>`'s
transitive dependency cone to check whether each field of `<StructureName>` is
actually projected (`Expr.proj`) or eliminated (`casesOn` / `rec`), rather than
merely carried along as passive type-level payload.
-/

namespace MetaCodex.Core

open Lean Elab Command

/-- Collect all non-library transitive constants reachable from `root`. Library constants are
    skipped by the module they come from (`isExternalLibraryConst`, shared with `ConeAudit`), so
    core lemmas outside the `Lean.*`/`Init.*` namespaces (e.g. `Nat.add_comm`, `Exists.intro`)
    are not walked either. -/
def collectActiveCone (env : Environment) (root : Name) : Array Name := Id.run do
  let mut visited : NameSet := {}
  let mut queue : List Name := [root]
  let mut ordered : Array Name := #[]
  while !queue.isEmpty do
    let curr :: rest := queue | break
    queue := rest
    if visited.contains curr then continue
    visited := visited.insert curr
    if isExternalLibraryConst env curr then
      continue
    ordered := ordered.push curr
    if let some cinfo := env.find? curr then
      let deps := cinfo.type.getUsedConstants.toList ++
        (match cinfo.value? (allowOpaque := true) with | some v => v.getUsedConstants.toList | none => [])
      queue := queue ++ deps.eraseDups
  return ordered

private partial def scanExprForStruct (structName : Name) (recNames : List Name)
    (projConstMap : Std.HashMap Name Nat) :
    Expr → StateM (ExprSet × Std.HashSet Nat × Bool) Unit
  | e => do
    let (seen, openedIdx, usedRec) ← get
    if seen.contains e then return
    set (seen.insert e, openedIdx, usedRec)
    match e with
    | .proj sName idx inner =>
      if sName == structName then
        let (s, o, r) ← get
        set (s, o.insert idx, r)
      scanExprForStruct structName recNames projConstMap inner
    | .const cName _ =>
      if recNames.contains cName then
        let (s, o, _) ← get
        set (s, o, true)
      else if let some idx := projConstMap[cName]? then
        let (s, o, r) ← get
        set (s, o.insert idx, r)
    | .app fn arg =>
      scanExprForStruct structName recNames projConstMap fn
      scanExprForStruct structName recNames projConstMap arg

    | .lam _ ty body _ | .forallE _ ty body _ =>
      scanExprForStruct structName recNames projConstMap ty
      scanExprForStruct structName recNames projConstMap body
    | .letE _ ty val body _ =>
      scanExprForStruct structName recNames projConstMap ty
      scanExprForStruct structName recNames projConstMap val
      scanExprForStruct structName recNames projConstMap body
    | .mdata _ inner =>
      scanExprForStruct structName recNames projConstMap inner
    | _ => pure ()

/-- `#audit_fields <theoremName> <StructureName>` reports whether each field of `<StructureName>`
    is projected or eliminated anywhere in `<theoremName>`'s transitive cone. -/
elab "#audit_fields " thmId:ident structId:ident : command => do
  let thmName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo thmId
  let structName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo structId
  let env ← getEnv
  let some sinfo := getStructureInfo? env structName
    | throwError "'{structName}' is not a Lean 4 structure."
  let mut projConstMap : Std.HashMap Name Nat := {}
  for i in [:sinfo.fieldNames.size] do
    projConstMap := projConstMap.insert (structName ++ sinfo.fieldNames[i]!) i
  let recNames := [structName ++ `rec, structName ++ `casesOn, structName ++ `recOn]
  let cone := collectActiveCone env thmName
  let mut exprState : ExprSet × Std.HashSet Nat × Bool := ({}, {}, false)
  for c in cone do
    if let some cinfo := env.find? c then
      let (_, st) := (do
        scanExprForStruct structName recNames projConstMap cinfo.type
        if let some v := cinfo.value? (allowOpaque := true) then
          scanExprForStruct structName recNames projConstMap v).run exprState
      exprState := st
  let (_, openedIdx, usedRec) := exprState
  logInfo m!"=== Field Projection Audit: `{thmName}` on `{structName}` ==="
  if usedRec then
    logInfo m!"  [eliminator] `{structName}.rec` / `casesOn` invoked in cone (all fields destructured)."
  for i in [:sinfo.fieldNames.size] do
    let fname := sinfo.fieldNames[i]!
    if usedRec || openedIdx.contains i then
      logInfo m!"  [OPENED]   {structName}.{fname}"
    else
      logWarning m!"  [UNOPENED] {structName}.{fname} (carried in cone but never projected or eliminated)"

end MetaCodex.Core
