import IndependentSetDiscovery.Extremal.Basic
import IndependentSetDiscovery.Extensions.Arithmetic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Edge-count and degeneracy conflict estimates

The elementary graph estimates underlying Theorems 5.2 and 5.3.  Adjacency
pairs are ordered and the candidate sets may overlap.
-/

namespace IndependentSetDiscovery

open Finset

variable {V : Type*} [DecidableEq V] [Fintype V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem adjacencyPairs_mono {U U' W W' : Finset V}
    (hU : U ⊆ U') (hW : W ⊆ W') :
    adjacencyPairs G U W ⊆ adjacencyPairs G U' W' := by
  intro p hp
  simp only [adjacencyPairs, mem_filter, mem_product] at hp ⊢
  exact ⟨⟨hU hp.1.1, hW hp.1.2⟩, hp.2⟩

/-- Every undirected edge supplies at most two ordered adjacency conflicts. -/
theorem card_adjacencyPairs_le_twice_edges (U W : Finset V) :
    (adjacencyPairs G U W).card ≤ 2 * G.edgeFinset.card := by
  rw [G.two_mul_card_edgeFinset]
  apply card_le_card
  intro p hp
  simpa only [mem_filter, mem_univ, true_and] using (mem_filter.mp hp).2

theorem card_conflictPairs_le_twice_edges_add (U W : Finset V) :
    (conflictPairs G U W).card ≤ 2 * G.edgeFinset.card + U.card := by
  exact (card_conflictPairs_le G U W).trans
    (Nat.add_le_add_right (card_adjacencyPairs_le_twice_edges G U W) _)

/-- The hereditary minimum-degree definition of graph degeneracy. -/
def Degenerate (a : ℕ) : Prop :=
  ∀ W : Finset V, W.Nonempty →
    ∃ v ∈ W, (W.filter fun u => G.Adj u v).card ≤ a

theorem card_leftNeighbors_insert (W : Finset V) {v : V} (hv : v ∉ W) (u : V) :
    (leftNeighbors G (insert v W) u).card =
      (leftNeighbors G W u).card + if G.Adj v u then 1 else 0 := by
  simp only [leftNeighbors, filter_insert]
  split_ifs with h
  · have hv' : v ∉ W.filter (fun x => G.Adj x u) := by simp [hv]
    simp [hv', Nat.add_comm]
  · simp

/-- Adding a vertex contributes its incident pairs in the two orientations. -/
theorem card_adjacencyPairs_insert (W : Finset V) {v : V} (hv : v ∉ W) :
    (adjacencyPairs G (insert v W) (insert v W)).card =
      (adjacencyPairs G W W).card + 2 * (leftNeighbors G W v).card := by
  rw [card_adjacencyPairs, sum_insert hv]
  simp_rw [card_leftNeighbors_insert G W hv]
  have hl : ¬ G.Adj v v := G.loopless v
  simp only [hl, ↓reduceIte, Nat.add_zero, sum_add_distrib]
  have hs : (∑ u ∈ W, if G.Adj v u then 1 else 0) =
      (leftNeighbors G W v).card := by
    simp only [leftNeighbors, card_eq_sum_ones, sum_filter]
    apply sum_congr rfl
    intro u hu
    by_cases h : G.Adj v u
    · simp [h, G.adj_symm h]
    · have h' : ¬ G.Adj u v := fun hu => h (G.adj_symm hu)
      simp [h, h']
  rw [hs, ← card_adjacencyPairs]
  omega

/-- Every finite induced subgraph of an `a`-degenerate graph has at most
`a * |W|` edges, expressed as twice as many ordered adjacency pairs. -/
theorem Degenerate.card_adjacencyPairs_le {a : ℕ} (hG : Degenerate G a)
    (W : Finset V) : (adjacencyPairs G W W).card ≤ 2 * a * W.card := by
  induction W using Finset.strongInductionOn
  rename_i W ih
  by_cases hW : W.Nonempty
  · obtain ⟨v, hv, hdeg⟩ := hG W hW
    have hv' : v ∉ W.erase v := notMem_erase v W
    have hs : W.erase v ⊂ W := erase_ssubset hv
    have hi := ih (W.erase v) hs
    have hcard : (W.erase v).card + 1 = W.card := card_erase_add_one hv
    have hn : leftNeighbors G (W.erase v) v = leftNeighbors G W v := by
      ext u
      simp only [leftNeighbors, mem_filter, mem_erase]
      constructor
      · exact fun h => ⟨h.1.2, h.2⟩
      · intro h
        exact ⟨⟨G.ne_of_adj h.2, h.1⟩, h.2⟩
    have he := card_adjacencyPairs_insert G (W.erase v) hv'
    rw [insert_erase hv, hn] at he
    change (leftNeighbors G W v).card ≤ a at hdeg
    nlinarith
  · have : W = ∅ := not_nonempty_iff_eq_empty.mp hW
    subst W
    simp [adjacencyPairs]

/-- The two-set estimate `4*a*ℓ` in Section 5.2. -/
theorem Degenerate.card_adjacencyPairs_two_sets_le {a ℓ : ℕ}
    (hG : Degenerate G a) (U W : Finset V) (hU : U.card = ℓ) (hW : W.card = ℓ) :
    (adjacencyPairs G U W).card ≤ 4 * a * ℓ := by
  have hsub := card_le_card (adjacencyPairs_mono G
    (show U ⊆ U ∪ W from subset_union_left)
    (show W ⊆ U ∪ W from subset_union_right))
  have hbound := hG.card_adjacencyPairs_le G (U ∪ W)
  have hcard : (U ∪ W).card ≤ 2 * ℓ := by
    have := card_union_le U W
    omega
  have hmul := Nat.mul_le_mul_left (2 * a) hcard
  calc
    (adjacencyPairs G U W).card ≤ (adjacencyPairs G (U ∪ W) (U ∪ W)).card := hsub
    _ ≤ 2 * a * (U ∪ W).card := hbound
    _ ≤ 4 * a * ℓ := by nlinarith

end IndependentSetDiscovery
