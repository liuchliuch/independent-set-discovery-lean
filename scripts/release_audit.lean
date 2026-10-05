import IndependentSetDiscovery
import StatementContracts
import Lean.Util.CollectAxioms

/-!
Release-only trust audit and independent body rechecking.

The release driver prepends an import of EVERY owned project module to a copy of
this file. Module provenance, not the public declaration namespace, selects the
constants; private helpers and generated declarations are included.

Axiom collection traverses declaration types and values using Lean's standard
CollectAxioms API. No declared project axioms are permitted. The only permitted
transitive axioms are propext, Classical.choice, and Quot.sound.

Each safe theorem, definition, or opaque body is re-submitted under a fresh name
to the standard kernel addDeclCore API with doCheck=true. This is a contextual
kernel body recheck using the imported environment, not a second kernel
implementation or a rebuild/reproof of mathlib. Inductive declarations and
kernel-generated constructors/recursors are covered by the clean source build
and trust audit, not recreated by this additional body pass.
-/

set_option maxHeartbeats 0

open Lean in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked := 0
  let mut replayed := 0
  let mut primitive := 0
  let mut unsafeAux := 0
  for (name, info) in env.constants.toList do
    let owned := match env.getModuleIdxFor? name with
      | some idx => (env.header.modules[idx.toNat]?).any (fun (m : EffectiveImport) =>
          (`IndependentSetDiscovery).isPrefixOf m.module || (`StatementContracts).isPrefixOf m.module)
      | none => false
    if owned then
      let moduleName := ((env.header.modules[(env.getModuleIdxFor? name).get!.toNat]?).map (fun (m : EffectiveImport) => m.module)).getD Name.anonymous
      if let .axiomInfo _ := info then
        throwError "Project-declared axiom: {name}"
      let axioms ← collectAxioms name
      let unexpected := axioms.filter (fun a => !allowed.contains a)
      unless unexpected.isEmpty do
        throwError "Unexpected transitive axioms in {name}: {unexpected}"
      logInfo m!"AXIOMS {moduleName} {name}: {axioms}"
      checked := checked + 1
      let fresh := Name.num `_releaseKernelReplay checked
      let decl? := match info with
        | .thmInfo v => some <| Declaration.thmDecl { v with name := fresh, all := [fresh] }
        | .defnInfo v =>
          if v.safety == DefinitionSafety.safe then
            some <| Declaration.defnDecl { v with name := fresh, all := [fresh] }
          else none
        | .opaqueInfo v =>
          if !v.isUnsafe then
            some <| Declaration.opaqueDecl { v with name := fresh, all := [fresh] }
          else none
        | _ => none
      match decl? with
      | some decl =>
        match env.addDeclCore 0 decl none (doCheck := true) with
        | .error err => throwError "Kernel body replay failed for {name}: {err.toMessageData (← getOptions)}"
        | .ok _ =>
          replayed := replayed + 1
          logInfo m!"KERNEL_BODY_PASS {name}"
      | none =>
        if info.isUnsafe then
          unsafeAux := unsafeAux + 1
          logInfo m!"COMPILER_AUX_UNSAFE {name}"
        else
          primitive := primitive + 1
  unless checked > 0 ∧ replayed > 0 do
    throwError "Empty release audit: checked={checked}, replayed={replayed}"
  unless unsafeAux == 0 do
    throwError "Found {unsafeAux} unsafe owned declarations; release requires explicit review"
  logInfo m!"RELEASE_AUDIT_PASS declarations={checked} kernelBodies={replayed} inductiveAndPrimitive={primitive} unsafe={unsafeAux}"
