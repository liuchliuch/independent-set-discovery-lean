import Lean
import Lean.Util.CollectAxioms

/-!
Local, same-process contract check. This is NOT leanprover/comparator and does
not sandbox untrusted Lean source. Its inputs must be trusted project builds.
It independently loads the frozen challenge and solution environments, compares
full theorem types and every referenced definition, audits solution axioms,
and resubmits the sixteen wrapper proof bodies to Lean's kernel.
-/
open Lean

set_option maxRecDepth 8192

deriving instance BEq for Lean.QuotKind
deriving instance BEq for Lean.QuotVal
deriving instance BEq for Lean.InductiveVal
deriving instance BEq for Lean.ConstantInfo

def requireConst (env : Environment) (name : Name) : IO ConstantInfo := do
  match env.find? name with
  | some c => pure c
  | none => throw <| IO.userError s!"Missing contract/dependency: {name}"

/-- All type/value dependencies, including inductive and recursor families. -/
def references (c : ConstantInfo) : Array Name :=
  c.getUsedConstantsAsSet.toArray

partial def compareContext (challenge solution : Environment) (targets : Array Name)
    (pending : Array Name) (seen : NameSet := {}) : IO Nat := do
  if pending.isEmpty then return seen.size
  let name := pending.back!
  let rest := pending.pop
  if seen.contains name then return ← compareContext challenge solution targets rest seen
  let a ← requireConst challenge name
  let b ← requireConst solution name
  let deps ← if targets.contains name then do
    unless a.toConstantVal == b.toConstantVal do
      throw <| IO.userError s!"STATEMENT_MISMATCH {name}"
    pure a.type.getUsedConstants
  else do
    unless a == b do
      throw <| IO.userError s!"CONTEXT_MISMATCH {name}"
    pure (references a)
  compareContext challenge solution targets (rest ++ deps) (seen.insert name)

def check (challenge solution : Environment) (targets allowed : Array Name) : IO Unit := do
  unless targets.size == 16 && targets.toList.eraseDups.length == 16 do
    throw <| IO.userError "Expected precisely 16 distinct paper contracts"
  let mut dependencies := #[]
  for name in targets do
    let .thmInfo a ← requireConst challenge name
      | throw <| IO.userError s!"Challenge is not a theorem: {name}"
    let .thmInfo b ← requireConst solution name
      | throw <| IO.userError s!"Solution is not a theorem: {name}"
    unless a.toConstantVal == b.toConstantVal do
      throw <| IO.userError s!"STATEMENT_MISMATCH {name}"
    dependencies := dependencies ++ a.type.getUsedConstants
    let (_, state) := ((CollectAxioms.collect name).run solution).run {}
    let unexpected := state.axioms.filter fun ax => !allowed.contains ax
    unless unexpected.isEmpty do
      throw <| IO.userError s!"UNEXPECTED_AXIOMS {name}: {unexpected}"
    let fresh := Name.str `_localContractKernelReplay name.toString
    let decl := Declaration.thmDecl { b with name := fresh, all := [fresh] }
    match solution.addDeclCore 0 decl none (doCheck := true) with
    | .error _ => throw <| IO.userError s!"KERNEL_REPLAY_FAILED {name}"
    | .ok _ => IO.println s!"LOCAL_CONTRACT_PASS {name}; axioms={state.axioms}"
  let count ← compareContext challenge solution targets dependencies
  IO.println s!"LOCAL_STATEMENT_CONTEXT_PASS {count} dependency declarations"
  IO.println "LOCAL_CONTRACT_SUMMARY 16 explicit paper contracts; exact types, context, axioms, kernel bodies passed"
  IO.println "This local check is not an official sandboxed Comparator run."

def main (args : List String) : IO Unit := do
  let [configPath, challengeName, solutionName] := args
    | throw <| IO.userError "usage: lean --run scripts/CompareStatements.lean CONFIG CHALLENGE_MODULE SOLUTION_MODULE"
  let json ← match Json.parse (← IO.FS.readFile configPath) with
    | .ok value => pure value
    | .error err => throw <| IO.userError err
  let readNames (key : String) : IO (Array Name) := do
    let items ← match json.getObjValAs? (Array String) key with
      | .ok value => pure value
      | .error err => throw <| IO.userError err
    pure <| items.map String.toName
  let targets ← readNames "theorem_names"
  let allowed ← readNames "permitted_axioms"
  unless allowed == #[`propext, `Quot.sound, `Classical.choice] do
    throw <| IO.userError "Unexpected permitted-axiom policy"
  initSearchPath (← findSysroot)
  let challenge ← importModules #[{ module := challengeName.toName }] {}
  let solution ← importModules #[{ module := solutionName.toName }] {}
  check challenge solution targets allowed
