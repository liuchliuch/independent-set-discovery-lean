import IndependentSetDiscovery
import StatementContracts.Solution
import Lean.Util.CollectAxioms
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let roots : Array Name := #[ `IndependentSetDiscovery, `StatementContracts.Solution ]
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut state : CollectAxioms.State := {}
  let mut count := 0
  let mut modules : NameSet := {}
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let origin := env.header.moduleNames[idx.toNat]!
      if roots.any (·.isPrefixOf origin) then
        if let .axiomInfo _ := info then throwError "Project-declared axiom: {name}"
        let (_, next) := ((CollectAxioms.collect name).run env).run state
        state := next
        count := count + 1
        modules := modules.insert origin
  unless count > 0 do throwError "Empty originating-declaration audit"
  for ax in state.axioms do
    unless allowed.contains ax do throwError "Unexpected transitive axiom: {ax}"
  logInfo m!"PROJECT_AXIOM_AUDIT_PASS declarations={count} modules={modules.size} axioms={state.axioms}"
