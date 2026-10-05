import IndependentSetDiscovery.Transversal.Independent
import IndependentSetDiscovery.Transversal.CheapPrefix

/-! # Lemma 4.5: the complete cheap-prefix dichotomy -/
namespace IndependentSetDiscovery

variable {ι V : Type*} [Fintype ι] [Fintype V] [DecidableEq ι] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Lemma 4.5(a): collectively affordable full cheap prefixes contain an
independent affordable choice, with the exact balanced threshold. -/
theorem cheap_prefix_affordable {d : ℕ} (hd : 2 ≤ d) (hG : BicliqueFree G d d)
    (hr : 2 ≤ Fintype.card ι) (A : ι → Finset V) (c : ι → V → ℚ) (B : ℚ)
    (hsize : ∀ i, balancedThreshold d (Fintype.card ι) ≤ (A i).card)
    (hB : (∑ i, prefixMax (c i)
      (cheapPrefix (c i) (A i) (balancedThreshold d (Fintype.card ι)))) ≤ B) :
    ∃ x : ι → V,
      (∀ i, x i ∈ cheapPrefix (c i) (A i) (balancedThreshold d (Fintype.card ι))) ∧
      Pairwise (fun i j => x i ≠ x j ∧ ¬ G.Adj (x i) (x j)) ∧
      (∑ i, c i (x i)) ≤ B := by
  obtain ⟨x, hx, hpair⟩ := biclique_free_independent_representatives G hd hG hr
    (fun i => cheapPrefix (c i) (A i) (balancedThreshold d (Fintype.card ι)))
    (fun i => by simp [Nat.min_eq_left (hsize i)])
  exact ⟨x, hx, hpair, affordable_prefix_selection c _ B hB x hx⟩

/-- Lemma 4.5(b): every affordable completion meets an over-budget prefix.
No sparsity assumption is necessary for this direction. -/
theorem cheap_prefix_overbudget (A : ι → Finset V) (c : ι → V → ℚ) (t : ℕ) (B : ℚ)
    (hc : ∀ i v, v ∈ A i → 0 ≤ c i v)
    (hB : B < ∑ i, prefixMax (c i) (cheapPrefix (c i) (A i) t))
    (x : ι → V) (hx : ∀ i, x i ∈ A i) (hcost : (∑ i, c i (x i)) ≤ B) :
    ∃ i, x i ∈ cheapPrefix (c i) (A i) t :=
  expensive_prefix_selection_meets c A t B hc hB x hx hcost

end IndependentSetDiscovery
