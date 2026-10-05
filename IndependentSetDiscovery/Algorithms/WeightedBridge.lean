import IndependentSetDiscovery.Weighted
import IndependentSetDiscovery.Algorithms.State

/-! The concrete graph problem is an instance of the generic residual-state
semantics. This bridge preserves overlapping candidate lists, label-dependent
costs, distinctness, nonadjacency, and the exact rational budget. -/

namespace IndependentSetDiscovery
namespace WeightedInstance

variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq V]
variable (I : WeightedInstance ι V)

/-- Initial, unfiltered state of the generic search. -/
def toState (B : ℚ) : Algorithms.State ι V where
  labels := Finset.univ
  candidates := I.candidates
  budget := B

theorem completion_iff_selection (B : ℚ) (x : ι → V) :
    Algorithms.Completion (Compatible I.graph) I.normalizedCost (I.toState B) x ↔
      I.Selection x ∧ I.selectionCost x ≤ B := by
  constructor
  · rintro ⟨hmem, hpair, hcost⟩
    have hx : I.Selection x := (I.selection_iff_compatible x).mpr
      ⟨fun i => hmem i (Finset.mem_univ i),
       fun i j hij => hpair i (Finset.mem_univ i) j (Finset.mem_univ j) hij⟩
    refine ⟨hx, ?_⟩
    change (∑ i, I.normalizedCost i (x i)) ≤ B at hcost
    rwa [I.sum_normalizedCost hx] at hcost
  · rintro ⟨hx, hcost⟩
    have hc := (I.selection_iff_compatible x).mp hx
    refine ⟨fun i _ => hx.1 i, fun i _ j _ hij => hc.2 i j hij, ?_⟩
    change (∑ i, I.normalizedCost i (x i)) ≤ B
    rwa [I.sum_normalizedCost hx]

theorem feasible_iff_within (B : ℚ) :
    Algorithms.Feasible (Compatible I.graph) I.normalizedCost (I.toState B) ↔
      I.Within B := by
  exact exists_congr fun x => I.completion_iff_selection B x

end WeightedInstance
end IndependentSetDiscovery
