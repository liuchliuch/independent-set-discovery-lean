import IndependentSetDiscovery.Algorithms.EagerOptimization
import IndependentSetDiscovery.Algorithms.MeasuredPreprocessing

namespace IndependentSetDiscovery.Algorithms

variable (R : Fin n → Fin n → Prop) [DecidableRel R] (cost : Fin k → Fin n → ℚ)

/-- Full measured optimization after a threshold table has been prepared.
Denominator clearing and upper-budget construction are measured concrete folds.
Every division used to construct an oracle budget is charged separately. -/
def optimizeEagerComplete [Inhabited (Fin n)] (threshold : ℕ → ℕ)
    (L : Finset (Fin k)) (rows : Vector (Finset (Fin n)) k) : Option (Fin k → Fin n) × ℕ :=
  let prep := prepareMeasured cost L rows
  let D := prep.1.1
  let U := prep.1.2
  let initial := fun b : ℕ => EagerState.mk L rows ((b : ℚ)/D)
  let oracle := eagerDecide R cost threshold
  let search := leastBudgetMeasured (fun b =>
    let answer := oracle (initial b)
    (answer.1, answer.2+1)) U
  match search.1 with
  | none => (none, prep.2+search.2)
  | some b =>
    let witness := recoverMeasured R cost oracle L.card (initial b)
    (witness.1, prep.2+search.2+1+witness.2)

theorem optimizeEagerComplete_refinement [Inhabited (Fin n)] (threshold : ℕ → ℕ)
    (L : Finset (Fin k)) (rows : Vector (Finset (Fin n)) k) :
    (optimizeEagerComplete R cost threshold L rows).1 =
      optimize R cost costPrefixOperations threshold L (fun i => rows[i]) := by
  have hp := prepareMeasured_value cost L rows
  have ho := eagerDecide_refinement R cost threshold
  unfold optimizeEagerComplete optimize
  dsimp only
  rw [hp]
  rw [leastBudgetMeasured_value]
  simp only [ho, EagerState.toState, budgetState]
  split
  · rename_i hcase
    simp only [hcase]
  · rename_i b hcase
    simp only [hcase]
    exact recoverMeasured_refinement R cost _ _ ho _ _

end IndependentSetDiscovery.Algorithms
