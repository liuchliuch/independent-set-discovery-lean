import IndependentSetDiscovery.Algorithms.MeasuredPreprocessing
import IndependentSetDiscovery.Algorithms.RationalArithmeticBits

/-!
# Bit bounds on measured preprocessing intermediates

A partially evaluated nested denominator fold multiplies a subset of the
original distinct label/candidate pairs. Positivity makes its value no larger
than the final clearing denominator. Scaled maxima and their partial sums are
similarly bounded by the exact optimization upper endpoint.
-/
namespace IndependentSetDiscovery.Algorithms

open Finset
variable {ι V : Type*} [DecidableEq ι] [DecidableEq V]

/-- Every partial product, including prefixes within an input row and prefixes
of completed rows, is bounded by the final common denominator. -/
theorem denominator_partial_product_le (L : Finset ι) (A : ι → Finset V)
    (c : ι → V → ℚ) (K : Finset (Σ _ : ι, V)) (hK : K ⊆ L.sigma A) :
    (∏ p ∈ K, (c p.1 p.2).den) ≤ commonDenominator L A c := by
  calc
    _ ≤ ∏ p ∈ L.sigma A, (c p.1 p.2).den := by
      apply Finset.prod_le_prod_of_subset_of_one_le' hK
      intro p hp hn
      exact (c p.1 p.2).pos
    _ = _ := by rw [Finset.prod_sigma]; rfl

theorem denominator_partial_product_bits (L : Finset ι) (A : ι → Finset V)
    (c : ι → V → ℚ) (K : Finset (Σ _ : ι, V)) (hK : K ⊆ L.sigma A) :
    binaryLength (∏ p ∈ K, (c p.1 p.2).den) ≤ numericSize L A c + 1 :=
  (binaryLength_mono (denominator_partial_product_le L A c K hK)).trans
    (commonDenominator_binaryLength L A c)

/-- Prefix maxima from any scanned subrow, summed over any subset of labels. -/
theorem scaled_partial_maxima_sum_le (L J : Finset ι) (A P : ι → Finset V)
    (c : ι → V → ℚ) (hJ : J ⊆ L) (hP : ∀ i ∈ J, P i ⊆ A i) :
    (∑ i ∈ J, (P i).sup (scaledCosts L A c i)) ≤ upperBudget L A (scaledCosts L A c) := by
  calc
    _ ≤ ∑ i ∈ J, (A i).sup (scaledCosts L A c i) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sup_le
      intro v hv
      exact Finset.le_sup (hP i hi hv)
    _ ≤ _ := Finset.sum_le_sum_of_subset hJ

theorem scaled_partial_maxima_sum_bits (L J : Finset ι) (A P : ι → Finset V)
    (c : ι → V → ℚ) (hJ : J ⊆ L) (hP : ∀ i ∈ J, P i ⊆ A i) :
    binaryLength (∑ i ∈ J, (P i).sup (scaledCosts L A c i)) ≤ 3 * numericSize L A c + 1 :=
  (binaryLength_mono (scaled_partial_maxima_sum_le L J A P c hJ hP)).trans
    (upperBudget_binaryLength L A c)

/-- Individual row maxima never exceed their contribution to the final sum. -/
theorem scaled_partial_maximum_bits (L : Finset ι) (A : ι → Finset V)
    (c : ι → V → ℚ) (i : ι) (hi : i ∈ L) (P : Finset V) (hP : P ⊆ A i) :
    binaryLength (P.sup (scaledCosts L A c i)) ≤ 3 * numericSize L A c + 1 := by
  have h := scaled_partial_maxima_sum_bits L {i} A
    (fun j => if j = i then P else ∅) c (by simpa)
    (by intro j hj; simp only [Finset.mem_singleton] at hj; subst j; simpa using hP)
  simpa using h

/-- Every scalar operand and output in the measured integer cost conversion
has linear bit length. This includes the division quotient before multiplication. -/
theorem scaleCost_intermediate_bits (L : Finset ι) (A : ι → Finset V)
    (c : ι → V → ℚ) (i : ι) (hi : i ∈ L) (v : V) (hv : v ∈ A i) :
    binaryLength (c i v).num.toNat ≤ numericSize L A c + 1 ∧
    binaryLength (c i v).den ≤ numericSize L A c + 1 ∧
    binaryLength (commonDenominator L A c / (c i v).den) ≤ numericSize L A c + 1 ∧
    binaryLength (scaleCost (commonDenominator L A c) (c i v)) ≤ 2 * numericSize L A c + 1 := by
  have hnum : (c i v).num.toNat ≤ (c i v).num.natAbs := by
    have := Int.toNat_add_toNat_neg_eq_natAbs (c i v).num
    omega
  have hden : (c i v).den ≤ 2 ^ numericSize L A c := by
    exact (rational_den_le_pow (c i v)).trans
      (Nat.pow_le_pow_right (by omega) (rationalBits_le_numericSize L A c i hi v hv))
  exact ⟨binaryLength_le_of_le_pow (hnum.trans (numerator_le_numeric_pow L A c i hi v hv)),
    binaryLength_le_of_le_pow hden,
    (binaryLength_mono (Nat.div_le_self _ _)).trans (commonDenominator_binaryLength L A c),
    scaledCosts_binaryLength L A c i hi v hv⟩

/-- A concrete prefix of the flattened measured denominator enumeration.
This is the list-fold form of the subset-product bound. -/
theorem denominator_listAccumulator_bits (L : Finset ι) (A : ι → Finset V)
    (c : ι → V → ℚ) (xs : List (Σ _ : ι, V)) (hn : xs.Nodup)
    (hx : ∀ p ∈ xs, p ∈ L.sigma A) (j : ℕ) :
    binaryLength (((xs.take j).map fun p => (c p.1 p.2).den).prod) ≤ numericSize L A c + 1 := by
  rw [← List.prod_toFinset _ hn.take]
  apply denominator_partial_product_bits L A c
  intro p hp
  exact hx p (List.mem_of_mem_take (List.mem_toFinset.mp hp))

/-- The measured upper-endpoint summation's accumulator after any prefix of
its distinct sorted label enumeration. -/
theorem scaledMaxima_listAccumulator_bits (L : Finset ι) (A P : ι → Finset V)
    (c : ι → V → ℚ) (xs : List ι) (hn : xs.Nodup)
    (hx : ∀ i ∈ xs, i ∈ L) (hP : ∀ i ∈ xs, P i ⊆ A i) (j : ℕ) :
    binaryLength (((xs.take j).map fun i => (P i).sup (scaledCosts L A c i)).sum) ≤
      3 * numericSize L A c + 1 := by
  rw [← List.sum_toFinset _ hn.take]
  apply scaled_partial_maxima_sum_bits L _ A P c
  · intro i hi
    exact hx i (List.mem_of_mem_take (List.mem_toFinset.mp hi))
  · intro i hi
    exact hP i (List.mem_of_mem_take (List.mem_toFinset.mp hi))

end IndependentSetDiscovery.Algorithms
