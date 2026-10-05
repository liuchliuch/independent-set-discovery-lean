import IndependentSetDiscovery.Extensions.SparseGraphs
import IndependentSetDiscovery.Transversal.Independent

/-! # Concrete transversal certificates for the edge and degeneracy extensions -/

namespace IndependentSetDiscovery

open Finset

variable {ι V : Type*} [Fintype ι] [Fintype V] [DecidableEq ι] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The compatible-prefix certificate underlying Theorem 5.2. -/
theorem independent_representatives_of_edge_count
    (A : ι → Finset V)
    (hsize : ∀ i, (A i).card = edgePrefixThreshold G.edgeFinset.card (Fintype.card ι)) :
    ∃ x : ι → V, (∀ i, x i ∈ A i) ∧
      Pairwise (fun i j => x i ≠ x j ∧ ¬ G.Adj (x i) (x j)) := by
  let t := edgePrefixThreshold G.edgeFinset.card (Fintype.card ι)
  apply independent_representatives_of_crossing_bound G A t
    (edgePrefixThreshold_pos _ _) hsize
  intro i
  have hsum : (∑ j ∈ univ.erase i, (conflictPairs G (A i) (A j)).card) ≤
      (Fintype.card ι - 1) * (2 * G.edgeFinset.card + t) := by
    calc
      (∑ j ∈ univ.erase i, (conflictPairs G (A i) (A j)).card) ≤
          ∑ j ∈ univ.erase i, (2 * G.edgeFinset.card + t) := by
        apply sum_le_sum
        intro j hj
        simpa only [hsize i] using card_conflictPairs_le_twice_edges_add G (A i) (A j)
      _ = _ := by simp
  have hcert := edgePrefixThreshold_nat_certificate G.edgeFinset.card (Fintype.card ι)
  change 4 * (Fintype.card ι - 1) * (2 * G.edgeFinset.card + t) < t ^ 2 at hcert
  nlinarith

/-- The compatible-prefix certificate underlying Theorem 5.3. -/
theorem independent_representatives_of_degeneracy {a : ℕ} (hG : Degenerate G a)
    (A : ι → Finset V)
    (hsize : ∀ i, (A i).card = degeneracyPrefixThreshold a (Fintype.card ι)) :
    ∃ x : ι → V, (∀ i, x i ∈ A i) ∧
      Pairwise (fun i j => x i ≠ x j ∧ ¬ G.Adj (x i) (x j)) := by
  let t := degeneracyPrefixThreshold a (Fintype.card ι)
  apply independent_representatives_of_crossing_bound G A t
    (degeneracyPrefixThreshold_pos _ _) hsize
  intro i
  have hpair (j : ι) : (conflictPairs G (A i) (A j)).card ≤ 4 * a * t + t := by
    have hc := card_conflictPairs_le G (A i) (A j)
    have ha := hG.card_adjacencyPairs_two_sets_le G (A i) (A j) (hsize i) (hsize j)
    rw [hsize i] at hc
    exact hc.trans (Nat.add_le_add_right ha _)
  have hsum : (∑ j ∈ univ.erase i, (conflictPairs G (A i) (A j)).card) ≤
      (Fintype.card ι - 1) * (4 * a * t + t) := by
    calc
      (∑ j ∈ univ.erase i, (conflictPairs G (A i) (A j)).card) ≤
          ∑ j ∈ univ.erase i, (4 * a * t + t) := by
        exact sum_le_sum (fun j _ => hpair j)
      _ = _ := by simp
  have hcert := degeneracyPrefixThreshold_nat_certificate a (Fintype.card ι)
  change 4 * (Fintype.card ι - 1) * (4 * a * t + t) < t ^ 2 at hcert
  nlinarith

end IndependentSetDiscovery
