import IndependentSetDiscovery.Transversal.Counting
import IndependentSetDiscovery.Extremal.Threshold

/-! # Independent representatives from block-average conflict counts -/
namespace IndependentSetDiscovery

open Finset

variable {ι V : Type*} [Fintype ι] [Fintype V] [DecidableEq ι] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Equal candidate lists admit independent, distinct representatives whenever
the total crossing conflict count at each list is at most one quarter of its
squared size. Candidate sets are allowed to overlap. -/
theorem independent_representatives_of_crossing_bound
    (A : ι → Finset V) (t : ℕ) (ht : 0 < t)
    (hsize : ∀ i, (A i).card = t)
    (hcross : ∀ i, 4 * (∑ j ∈ univ.erase i, (conflictPairs G (A i) (A j)).card) ≤ t^2) :
    ∃ x : ι → V, (∀ i, x i ∈ A i) ∧
      Pairwise (fun i j => x i ≠ x j ∧ ¬ G.Adj (x i) (x j)) := by
  classical
  have hR : Symmetric (fun u v : V => u = v ∨ G.Adj u v) := by
    intro u v h
    exact h.elim (fun h => Or.inl h.symm) (fun h => Or.inr (G.symm h))
  have hp (i j : ι) :
      Transversal.pairs A (fun u v => u = v ∨ G.Adj u v) i j =
        conflictPairs G (A i) (A j) := by
    ext p
    simp [Transversal.pairs, conflictPairs]
  obtain ⟨x, hx, hgood⟩ := Transversal.wanlessWood_equal A
    (fun u v => u = v ∨ G.Adj u v) hR t ht hsize (by simpa only [hp] using hcross)
  exact ⟨x, hx, fun i j hij => not_or.mp (hgood hij)⟩

/-- Pairwise sparse conflicts imply the block-average hypothesis. -/
theorem independent_representatives_of_pair_bound
    (A : ι → Finset V) (t : ℕ) (ht : 0 < t)
    (hr : 2 ≤ Fintype.card ι) (hsize : ∀ i, (A i).card = t)
    (hpair : ∀ i j, i ≠ j →
      4 * (Fintype.card ι - 1) * (conflictPairs G (A i) (A j)).card ≤ t^2) :
    ∃ x : ι → V, (∀ i, x i ∈ A i) ∧
      Pairwise (fun i j => x i ≠ x j ∧ ¬ G.Adj (x i) (x j)) := by
  apply independent_representatives_of_crossing_bound G A t ht hsize
  intro i
  have hsum := Finset.sum_le_sum (s := univ.erase i)
    (fun j hj => hpair i j (Ne.symm (mem_erase.mp hj).1))
  have heq : (univ.erase i : Finset ι).card = Fintype.card ι - 1 := by simp
  simp only [← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, heq] at hsum
  have hpos : 0 < Fintype.card ι - 1 := by omega
  nlinarith

/-- Real-valued sparse-prefix transfer criterion: equality conflicts are
already included in the pair-density estimate. -/
theorem independent_representatives_of_density
    (A : ι → Finset V) (t : ℕ) (ht : 0 < t) (hr : 2 ≤ Fintype.card ι)
    (hsize : ∀ i, (A i).card = t) (ρ : ℝ)
    (hpair : ∀ i j, i ≠ j →
      ((conflictPairs G (A i) (A j)).card : ℝ) ≤ ρ * (t : ℝ)^2)
    (hρ : 4 * ((Fintype.card ι - 1 : ℕ) : ℝ) * ρ ≤ 1) :
    ∃ x : ι → V, (∀ i, x i ∈ A i) ∧
      Pairwise (fun i j => x i ≠ x j ∧ ¬ G.Adj (x i) (x j)) := by
  apply independent_representatives_of_pair_bound G A t ht hr hsize
  intro i j hij
  have hp := mul_le_mul_of_nonneg_left (hpair i j hij)
    (show (0 : ℝ) ≤ 4 * ((Fintype.card ι - 1 : ℕ) : ℝ) by positivity)
  have hs := mul_le_mul_of_nonneg_right hρ (sq_nonneg (t : ℝ))
  have hresult : (4 : ℝ) * ((Fintype.card ι - 1 : ℕ) : ℝ) *
      (conflictPairs G (A i) (A j)).card ≤ (t : ℝ)^2 := by nlinarith
  exact_mod_cast hresult

/-- Lemmas 4.2 and 4.3 combined, with the paper's exact `M(d,r)`. -/
theorem biclique_free_independent_representatives
    {d : ℕ} (hd : 2 ≤ d) (hG : BicliqueFree G d d)
    (hr : 2 ≤ Fintype.card ι) (A : ι → Finset V)
    (hsize : ∀ i, (A i).card = balancedThreshold d (Fintype.card ι)) :
    ∃ x : ι → V, (∀ i, x i ∈ A i) ∧
      Pairwise (fun i j => x i ≠ x j ∧ ¬ G.Adj (x i) (x j)) := by
  refine independent_representatives_of_pair_bound G A
    (balancedThreshold d (Fintype.card ι)) ?_ hr hsize ?_
  · have hr' : 0 < Fintype.card ι - 1 := by omega
    unfold balancedThreshold
    positivity
  · intro i j _
    exact (balancedThreshold_certificate G hd hr hG (A i) (A j) (hsize i) (hsize j)).le

/-- The bounded-codegree transfer certificate from Section 5. -/
theorem codegree_independent_representatives
    {s q : ℕ} (hs : 1 ≤ s) (hG : CodegreeBound G s q)
    (hr : 2 ≤ Fintype.card ι) (A : ι → Finset V)
    (hsize : ∀ i, (A i).card = codegreeThreshold s q (Fintype.card ι - 1)) :
    ∃ x : ι → V, (∀ i, x i ∈ A i) ∧
      Pairwise (fun i j => x i ≠ x j ∧ ¬ G.Adj (x i) (x j)) := by
  refine independent_representatives_of_pair_bound G A
    (codegreeThreshold s q (Fintype.card ι - 1)) (codegreeThreshold_pos _ _ _) hr hsize ?_
  intro i j _
  exact (codegreeThreshold_certificate G hs hG (A i) (A j) (hsize i) (hsize j)).le

end IndependentSetDiscovery
