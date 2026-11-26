import Lean

/-!
# ConeAudit: Opaque-Safe & Module-Filtered Transitive Dependency Cone Scanner

Walks a theorem's transitive dependency cone using:
1. `allowOpaque := true` (and explicit `.opaqueInfo` inspection) so `opaque` wrappers
   cannot sever the dependency graph or hide `True`-peeling bodies.
2. Module-origin filtering (`env.getModuleIdxFor?`) so imported Mathlib / stdlib
   declarations (even those outside the `Mathlib.*` namespace, like `Complex.*` or `Nat.*`)
   are skipped in O(1) without walking thousands of library lemmas.
-/

namespace MetaCodex.Core

open Lean Elab Command Meta

private def isLibraryModuleName (modName : Name) : Bool :=
  match modName.getRoot with

  | `Lean | `Init | `Std | `Batteries | `Qq | `Aesop | `Mathlib | `ProofWidgets | `Plausible | `ImportGraph => true
  | _ => false

/-- Returns `true` if `n` originates from an imported standard library or Mathlib module
    (or carries a standard library root namespace). -/
def isExternalLibraryConst (env : Environment) (n : Name) : Bool :=
  match n.getRoot with

  | `Lean | `Init | `Std | `Batteries | `Qq | `Aesop | `Mathlib => true
  | _ =>
    match env.getModuleIdxFor? n with
    | some idx =>
      if h : idx.toNat < env.header.moduleNames.size then
        isLibraryModuleName env.header.moduleNames[idx.toNat]
      else
        false
    | none => false

private def isStandardAxiom (n : Name) : Bool :=
  n == ``propext || n == ``Quot.sound || n == ``Classical.choice

/-- Peel nested `∀` and `λ` binders to check if the core body is syntactically `True`. -/
private partial def peelsToTrue : Expr → Bool
  | .const ``True _ => true
  | .forallE _ _ body _ => peelsToTrue body
  | .lam _ _ body _ => peelsToTrue body
  | .mdata _ inner => peelsToTrue inner
  | _ => false

/-- Collect all constant names referenced in an `Expr`. -/
private partial def collectExprConsts (e : Expr) (acc : NameSet := {}) : NameSet :=
  match e with
  | .const n _ => acc.insert n
  | .app fn arg => collectExprConsts arg (collectExprConsts fn acc)

  | .lam _ ty body _ | .forallE _ ty body _ =>
      collectExprConsts body (collectExprConsts ty acc)
  | .letE _ ty val body _ =>
      collectExprConsts body (collectExprConsts val (collectExprConsts ty acc))

  | .mdata _ inner | .proj _ _ inner => collectExprConsts inner acc
  | _ => acc

/-- Walk the transitive dependency cone with `allowOpaque := true` and O(1) module filtering. -/
partial def collectOpaqueSafeCone (env : Environment) (root : Name) :
    NameSet × Array Name × Array Name :=
  let rec visit (worklist : List Name) (visited : NameSet)
      (opaqueBounds : Array Name) (customAxioms : Array Name) :
      NameSet × Array Name × Array Name :=
    match worklist with
    | [] => (visited, opaqueBounds, customAxioms)
    | n :: rest =>
      if visited.contains n || isExternalLibraryConst env n then
        visit rest visited opaqueBounds customAxioms
      else
        let visited' := visited.insert n
        match env.find? n with
        | none => visit rest visited' opaqueBounds customAxioms
        | some cinfo =>
          let typeConsts := collectExprConsts cinfo.type
          let (valConsts, opaqueBounds', customAxioms') :=
            match cinfo with
            | .opaqueInfo v =>
                (collectExprConsts v.value, opaqueBounds.push n, customAxioms)
            | .axiomInfo _ =>
                let ax := if isStandardAxiom n then customAxioms else customAxioms.push n
                ({}, opaqueBounds, ax)
            | _ =>
                match cinfo.value? (allowOpaque := true) with
                | some val => (collectExprConsts val, opaqueBounds, customAxioms)
                | none => ({}, opaqueBounds, customAxioms)
          let next := (typeConsts.union valConsts).toList.filter (!visited'.contains ·)
          visit (next ++ rest) visited' opaqueBounds' customAxioms'
  visit [root] {} #[] #[]

/-- `#audit_theorem <theoremName>` walks the full opaque-safe transitive cone and flags
    vacuous (`True`-peeling) definitions, `opaque` boundaries, and custom axioms. -/
elab "#audit_theorem " thmId:ident : command => do
  let thmName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo thmId
  let env ← getEnv
  let (cone, opaqueBounds, customAxioms) := collectOpaqueSafeCone env thmName
  let mut vacuous : Array Name := #[]
  for c in cone do
    if c != thmName then
      if let some cinfo := env.find? c then
        if let some val := cinfo.value? (allowOpaque := true) then
          if peelsToTrue val || peelsToTrue cinfo.type then
            vacuous := vacuous.push c
  logInfo m!"Auditing opaque-safe dependency cone for: `{thmName}` ({cone.size} active constants)"
  for op in opaqueBounds do
    logWarning m!"  [OPAQUE BOUNDARY] `{op}` is declared `opaque` (body inspected via `allowOpaque := true`)."
  for ax in customAxioms do
    logWarning m!"  [CUSTOM AXIOM] `{ax}` is an unproved axiom in the active cone."
  if vacuous.isEmpty then
    logInfo m!"Audit complete: 0 vacuous definitions found."
  else
    for v in vacuous do
      logError m!"  [VACUOUS] `{v}` reduces syntactically to `True`."

end MetaCodex.Core
