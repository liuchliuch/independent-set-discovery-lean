import IndependentSetDiscovery.Algorithms.EagerMachine
import IndependentSetDiscovery.Algorithms.CostModel

namespace IndependentSetDiscovery.Algorithms

/-- Single-pass execution of measured instructions. The node is constructed
once, and each child is executed once; answers and work travel together. -/
def execute (step : σ → Instruction σ × ℕ) : ℕ → σ → Bool × ℕ
  | 0, s =>
    let node := step s
    match node.1 with
    | .yes => (true, node.2)
    | .no => (false, node.2)
    | .branch _ => (false, node.2)
  | fuel + 1, s =>
    let node := step s
    match node.1 with
    | .yes => (true, node.2)
    | .no => (false, node.2)
    | .branch children =>
      let answers := children.map (execute step fuel)
      (answers.any Prod.fst, node.2 + (answers.map Prod.snd).sum)

/-- Value refinement and exact compositional work accounting of the same pass. -/
theorem execute_spec (step : σ → Instruction σ × ℕ) : ∀ fuel s,
    (execute step fuel s).1 = (run (fun t => (step t).1) fuel s).1 ∧
    (execute step fuel s).2 = runWork (fun t => (step t).1) (fun t => (step t).2) fuel s := by
  intro fuel
  induction fuel with
  | zero =>
    intro s
    cases h : step s with
    | mk ins charge => cases ins <;> simp [execute, run, runWork, h]
  | succ fuel ih =>
    intro s
    have hv : ∀ t, (execute step fuel t).1 = (run (fun t => (step t).1) fuel t).1 := fun t => (ih t).1
    have hw : ∀ t, (execute step fuel t).2 = runWork (fun t => (step t).1) (fun t => (step t).2) fuel t := fun t => (ih t).2
    cases h : step s with
    | mk ins charge =>
      cases ins <;> simp [execute, run, runWork, h, List.any_map, List.map_map, Function.comp_def, hv, hw]

/-- Value and node-count refinement along an exact map of finite instructions. -/
theorem run_map_refinement (stepA : α → Instruction α) (stepB : β → Instruction β)
    (f : α → β) (hrefine : ∀ a, (stepA a).map f = stepB (f a)) :
    ∀ fuel a, run stepA fuel a = run stepB fuel (f a) := by
  intro fuel
  induction fuel with
  | zero =>
    intro a
    have h := (hrefine a).symm
    cases ha : stepA a <;> simp [ha, Instruction.map] at h <;> simp [run, ha, h]
  | succ fuel ih =>
    intro a
    have h := (hrefine a).symm
    cases ha : stepA a with
    | yes => simp [ha, Instruction.map] at h; simp [run, ha, h]
    | no => simp [ha, Instruction.map] at h; simp [run, ha, h]
    | branch children =>
      simp only [ha, Instruction.map] at h
      simp only [run, ha, h, List.map_map, Function.comp_def]
      have heq : children.map (run stepA fuel) = children.map (fun x => run stepB fuel (f x)) := by
        apply List.map_congr_left
        intro x hx
        exact ih x
      rw [heq]
      simp only [ih]

variable (R : Fin n → Fin n → Prop) [DecidableRel R] (cost : Fin k → Fin n → ℚ)

def eagerDecide (threshold : ℕ → ℕ) (s : EagerState k n) : Bool × ℕ :=
  execute (eagerStepCounted R cost threshold) s.labels.card s

theorem eagerDecide_refinement (threshold : ℕ → ℕ) (s : EagerState k n) :
    (eagerDecide R cost threshold s).1 = decidePrefix R cost costPrefixOperations threshold s.toState := by
  rw [eagerDecide, (execute_spec _ _ _).1]
  have h := run_map_refinement (eagerStep R cost threshold)
    (prefixStep R cost costPrefixOperations threshold) EagerState.toState
    (eagerStep_refinement R cost threshold) s.labels.card s
  exact congrArg Prod.fst h

end IndependentSetDiscovery.Algorithms
