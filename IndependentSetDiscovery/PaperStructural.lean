import IndependentSetDiscovery.Extremal.RealBounds
import IndependentSetDiscovery.Transversal.Independent

/-! # Paper-facing sparse-prefix certificates

These statements make the arbitrary-threshold form of Lemma 4.2 and the
structural premise of Lemma 5.1 explicit. Algorithmic transfer uses the
separately verified cheap-prefix solver and its operation bounds.
-/

namespace IndependentSetDiscovery

variable {ι V : Type*} [Fintype ι] [Fintype V]
  [DecidableEq ι] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Lemma 4.2 at any positive threshold satisfying the paper's density test. -/
theorem biclique_free_transversal_arbitrary_threshold
    {d t : ℕ} (hd : 2 ≤ d) (ht : 0 < t) (hr : 2 ≤ Fintype.card ι)
    (hG : BicliqueFree G d d) (A : ι → Finset V)
    (hsize : ∀ i, (A i).card = t)
    (hthreshold : 4 * ((Fintype.card ι - 1 : ℕ) : ℝ) *
      codegreeDensity d (d - 1) t < 1) :
    ∃ x : ι → V, (∀ i, x i ∈ A i) ∧
      Pairwise (fun i j => x i ≠ x j ∧ ¬G.Adj (x i) (x j)) := by
  apply independent_representatives_of_density G A t ht hr hsize
    (codegreeDensity d (d - 1) t) _ hthreshold.le
  intro i j hij
  rw [codegreeDensity_mul_square d (d - 1) ht]
  exact asymmetric_conflict_bound G (by omega)
    ((bicliqueFree_iff_codegreeBound G d d (by omega)).mp hG)
    (A i) (A j) (hsize i) (hsize j)

/-- The generic local sparsity certificate used in Lemma 5.1. Equality
conflicts add precisely the extra `t` term to the adjacency-pair bound. -/
theorem sparse_prefix_transversal
    (γ : ℕ → ℝ) (t : ℕ) (ht : 0 < t) (hr : 2 ≤ Fintype.card ι)
    (hlocal : ∀ U W : Finset V, U.card = t → W.card = t →
      ((adjacencyPairs G U W).card : ℝ) ≤ γ t)
    (hthreshold : 4 * ((Fintype.card ι - 1 : ℕ) : ℝ) *
      (γ t + t) < (t : ℝ)^2)
    (A : ι → Finset V) (hsize : ∀ i, (A i).card = t) :
    ∃ x : ι → V, (∀ i, x i ∈ A i) ∧
      Pairwise (fun i j => x i ≠ x j ∧ ¬G.Adj (x i) (x j)) := by
  apply independent_representatives_of_pair_bound G A t ht hr hsize
  intro i j hij
  have hc := card_conflictPairs_le G (A i) (A j)
  rw [hsize i] at hc
  have hc' : ((conflictPairs G (A i) (A j)).card : ℝ) ≤
      ((adjacencyPairs G (A i) (A j)).card : ℝ) + t := by exact_mod_cast hc
  have ha := hlocal (A i) (A j) (hsize i) (hsize j)
  have hfactor : (0 : ℝ) ≤ 4 * ((Fintype.card ι - 1 : ℕ) : ℝ) := by positivity
  have hh := mul_le_mul_of_nonneg_left (hc'.trans (add_le_add_right ha _)) hfactor
  have hresult : (4 : ℝ) * ((Fintype.card ι - 1 : ℕ) : ℝ) *
      (conflictPairs G (A i) (A j)).card ≤ (t : ℝ)^2 := hh.trans hthreshold.le
  exact_mod_cast hresult

end IndependentSetDiscovery
