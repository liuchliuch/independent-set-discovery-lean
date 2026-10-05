import IndependentSetDiscovery.Algorithms.WeightedSolver
import IndependentSetDiscovery.Movement.Reduction

/-!
# Main discovery specification

This module connects the concrete weighted solver to the graph-metric problem.
The graph-metric instance here is a mathematical specification. Executable
shortest-path preprocessing and executable slide reconstruction are separate
implementation obligations; these theorems alone do not assert a running time.
-/

namespace IndependentSetDiscovery

open Movement

variable {V : Type*} [Fintype V] [LinearOrder V] [Inhabited V]

/-- The exact discovery result required of the final implementation. -/
def OptimalDiscovery (G : SimpleGraph V) (S T : Finset V) (n : ℕ) : Prop :=
  T.card = S.card ∧ Independent G T ∧ SlideSequence G S T n ∧
    ∀ T' n', Independent G T' → SlideSequence G S T' n' → n ≤ n'

/-- A returned weighted optimum gives a globally shortest collision-free
discovery sequence, with its explicit polynomial output-length bound. -/
theorem weighted_solution_gives_optimal_discovery
    (G : SimpleGraph V) (S : Finset V) {d : ℕ}
    (hd : 2 ≤ d) (hG : BicliqueFree G d d) (x : S → V)
    [DecidableRel (movementInstance G S).graph.Adj]
    (hx : (movementInstance G S).solveBicliqueFree d = some x) :
    ∃ T n, OptimalDiscovery G S T n ∧
      (n : ℚ) = (movementInstance G S).selectionCost x ∧
      n ≤ S.card * (Fintype.card V - 1) := by
  have hgraph : BicliqueFree (movementInstance G S).graph d d := by
    simpa [movementInstance] using hG
  have hopt := (movementInstance G S).solveBicliqueFree_some hd hgraph hx
  obtain ⟨T, n, hT, hs, hcost, hbound, hmin⟩ :=
    optimal_selection_realizes_discovery hopt
  exact ⟨T, n, ⟨hs.card_eq, hT, hs, hmin⟩, hcost, hbound⟩

/-- Reporting failure is equivalent to actual discovery nonreachability. -/
theorem weighted_failure_iff_no_discovery
    (G : SimpleGraph V) (S : Finset V) {d : ℕ}
    (hd : 2 ≤ d) (hG : BicliqueFree G d d)
    [DecidableRel (movementInstance G S).graph.Adj] :
    (movementInstance G S).solveBicliqueFree d = none ↔
      ¬ ∃ T n, Independent G T ∧ SlideSequence G S T n := by
  have hgraph : BicliqueFree (movementInstance G S).graph d d := by
    simpa [movementInstance] using hG
  exact ((movementInstance G S).solveBicliqueFree_none_iff hd hgraph).trans
    (no_selection_iff_unreachable G S)

end IndependentSetDiscovery
