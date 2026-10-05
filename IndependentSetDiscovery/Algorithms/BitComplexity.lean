import IndependentSetDiscovery.Algorithms.Scaling
import IndependentSetDiscovery.Algorithms.BinarySearch

/-!
# Explicit bit-length bounds for exact rational optimization

The clearing denominator and all scaled optimization budgets have binary
length linear in the numerical encoding length. Thus optimization uses a
linear number of decision-oracle calls in the input's numerical bit length.
-/
namespace IndependentSetDiscovery.Algorithms

open Finset

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V]

/-- A concrete upper bound on the numeric part of the input encoding length.
A zero numerator still occupies one bit. The label count is included to bound
the sum of the coordinate-wise maximum costs. -/
def numericSize (L : Finset ι) (A : ι → Finset V) (c : ι → V → ℚ) : ℕ :=
  L.card + 1 + ∑ i ∈ L, ∑ v ∈ A i, rationalBits (c i v)

/-- Binary digits, using one digit for zero. -/
def binaryLength (n : ℕ) : ℕ := Nat.log2 n + 1

theorem numericSize_pos (L : Finset ι) (A : ι → Finset V) (c : ι → V → ℚ) :
    0 < numericSize L A c := by unfold numericSize; omega

theorem card_le_numericSize (L : Finset ι) (A : ι → Finset V) (c : ι → V → ℚ) :
    L.card ≤ numericSize L A c := by unfold numericSize; omega

theorem denominatorBits_le_numericSize (L : Finset ι) (A : ι → Finset V) (c : ι → V → ℚ) :
    denominatorBits L A c ≤ numericSize L A c := by
  have hs : denominatorBits L A c ≤ ∑ i ∈ L, ∑ v ∈ A i, rationalBits (c i v) := by
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro v hv
    unfold rationalBits
    omega
  unfold numericSize
  omega

theorem rationalBits_le_numericSize (L : Finset ι) (A : ι → Finset V) (c : ι → V → ℚ)
    (i : ι) (hi : i ∈ L) (v : V) (hv : v ∈ A i) :
    rationalBits (c i v) ≤ numericSize L A c := by
  have hv' : rationalBits (c i v) ≤ ∑ u ∈ A i, rationalBits (c i u) :=
    Finset.single_le_sum (f := fun u => rationalBits (c i u)) (fun _ _ => Nat.zero_le _) hv
  have hi' : (∑ u ∈ A i, rationalBits (c i u)) ≤
      ∑ j ∈ L, ∑ u ∈ A j, rationalBits (c j u) :=
    Finset.single_le_sum (f := fun j => ∑ u ∈ A j, rationalBits (c j u))
      (fun _ _ => Nat.zero_le _) hi
  unfold numericSize
  omega

theorem binaryLength_le_of_le_pow {n b : ℕ} (h : n ≤ 2^b) : binaryLength n ≤ b + 1 := by
  have hh := Nat.log_mono_right (b := 2) h
  simp only [← Nat.log2_eq_log_two, Nat.log2_two_pow] at hh
  unfold binaryLength
  omega

/-- The product denominator has at most `S+1` bits. -/
theorem commonDenominator_le_numeric_pow (L : Finset ι) (A : ι → Finset V) (c : ι → V → ℚ) :
    commonDenominator L A c ≤ 2 ^ numericSize L A c := by
  apply (commonDenominator_le_pow L A c).trans
  exact Nat.pow_le_pow_right (by omega) (denominatorBits_le_numericSize L A c)

theorem commonDenominator_binaryLength (L : Finset ι) (A : ι → Finset V) (c : ι → V → ℚ) :
    binaryLength (commonDenominator L A c) ≤ numericSize L A c + 1 :=
  binaryLength_le_of_le_pow (commonDenominator_le_numeric_pow L A c)

theorem numerator_le_numeric_pow (L : Finset ι) (A : ι → Finset V) (c : ι → V → ℚ)
    (i : ι) (hi : i ∈ L) (v : V) (hv : v ∈ A i) :
    (c i v).num.natAbs ≤ 2 ^ numericSize L A c := by
  have hn : Nat.log2 (c i v).num.natAbs + 1 ≤ numericSize L A c := by
    have := rationalBits_le_numericSize L A c i hi v hv
    unfold rationalBits at this
    omega
  exact (nat_lt_two_pow_bits _).le.trans (Nat.pow_le_pow_right (by omega) hn)

/-- An individual scaled cost has at most `2S+1` bits. This bound does not
need nonnegativity; negative numerators are mapped to zero by `scaleCost`. -/
theorem scaledCosts_le_numeric_pow (L : Finset ι) (A : ι → Finset V) (c : ι → V → ℚ)
    (i : ι) (hi : i ∈ L) (v : V) (hv : v ∈ A i) :
    scaledCosts L A c i v ≤ 2 ^ (2 * numericSize L A c) := by
  have hnum : (c i v).num.toNat ≤ (c i v).num.natAbs := by
    have := Int.toNat_add_toNat_neg_eq_natAbs (c i v).num
    omega
  have hdiv : commonDenominator L A c / (c i v).den ≤ commonDenominator L A c :=
    Nat.div_le_self _ _
  calc
    scaledCosts L A c i v ≤ (2 ^ numericSize L A c) * (2 ^ numericSize L A c) :=
      Nat.mul_le_mul (hnum.trans (numerator_le_numeric_pow L A c i hi v hv))
        (hdiv.trans (commonDenominator_le_numeric_pow L A c))
    _ = 2 ^ (2 * numericSize L A c) := by rw [← pow_add]; congr 1; omega

theorem scaledCosts_binaryLength (L : Finset ι) (A : ι → Finset V) (c : ι → V → ℚ)
    (i : ι) (hi : i ∈ L) (v : V) (hv : v ∈ A i) :
    binaryLength (scaledCosts L A c i v) ≤ 2 * numericSize L A c + 1 :=
  binaryLength_le_of_le_pow (scaledCosts_le_numeric_pow L A c i hi v hv)

/-- The optimization interval endpoint has at most `3S+1` bits. -/
theorem upperBudget_le_numeric_pow (L : Finset ι) (A : ι → Finset V) (c : ι → V → ℚ) :
    upperBudget L A (scaledCosts L A c) ≤ 2 ^ (3 * numericSize L A c) := by
  have hs : upperBudget L A (scaledCosts L A c) ≤ L.card * 2 ^ (2 * numericSize L A c) := by
    unfold upperBudget
    calc
      _ ≤ ∑ _i ∈ L, 2 ^ (2 * numericSize L A c) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sup_le
        intro v hv
        exact scaledCosts_le_numeric_pow L A c i hi v hv
      _ = _ := by simp
  have hc : L.card ≤ 2 ^ numericSize L A c :=
    (card_le_numericSize L A c).trans (Nat.lt_two_pow_self.le)
  calc
    _ ≤ L.card * 2 ^ (2 * numericSize L A c) := hs
    _ ≤ (2 ^ numericSize L A c) * (2 ^ (2 * numericSize L A c)) := Nat.mul_le_mul_right _ hc
    _ = 2 ^ (3 * numericSize L A c) := by rw [← pow_add]; congr 1; omega

theorem upperBudget_binaryLength (L : Finset ι) (A : ι → Finset V) (c : ι → V → ℚ) :
    binaryLength (upperBudget L A (scaledCosts L A c)) ≤ 3 * numericSize L A c + 1 :=
  binaryLength_le_of_le_pow (upperBudget_le_numeric_pow L A c)

/-- One initial feasibility query plus binary search is linear in numeric input
size. In particular this is logarithmic, not linear, in the budget value. -/
theorem optimizationCalls_le_numericSize (L : Finset ι) (A : ι → Finset V) (c : ι → V → ℚ) :
    optimizationCalls (upperBudget L A (scaledCosts L A c)) ≤ 3 * numericSize L A c + 2 := by
  have := upperBudget_binaryLength L A c
  unfold optimizationCalls binaryLength at *
  omega

/-- Every rational budget submitted by binary search can be represented as
`n / D` with at most `4S+2` bits across its numerator and denominator. -/
theorem oracleBudget_encoding_bound (L : Finset ι) (A : ι → Finset V) (c : ι → V → ℚ)
    (n : ℕ) (hn : n ≤ upperBudget L A (scaledCosts L A c)) :
    binaryLength n + binaryLength (commonDenominator L A c) ≤ 4 * numericSize L A c + 2 := by
  have hn' := binaryLength_le_of_le_pow (hn.trans (upperBudget_le_numeric_pow L A c))
  have hd := commonDenominator_binaryLength L A c
  omega

end IndependentSetDiscovery.Algorithms
