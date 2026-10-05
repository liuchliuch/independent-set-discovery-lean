import IndependentSetDiscovery.Algorithms.BitComplexity

/-!
# Polynomial-size residual rational arithmetic

Every partial assignment chooses at most one candidate for each original
label. Its scaled total is bounded by the same `U` used for optimization.
Consequently even a rejected negative residual budget has numerator magnitude
at most `U` over the common denominator `D`.
-/
namespace IndependentSetDiscovery.Algorithms

open Finset

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V]

theorem partialScaledCost_le_upper (L K : Finset ι) (A : ι → Finset V)
    (c : ι → V → ℚ) (hK : K ⊆ L) (x : ι → V) (hx : ∀ i ∈ K, x i ∈ A i) :
    (∑ i ∈ K, scaledCosts L A c i (x i)) ≤ upperBudget L A (scaledCosts L A c) := by
  calc
    _ ≤ ∑ i ∈ K, (A i).sup (scaledCosts L A c i) := by
      apply Finset.sum_le_sum
      intro i hi
      exact Finset.le_sup (hx i hi)
    _ ≤ ∑ i ∈ L, (A i).sup (scaledCosts L A c i) := Finset.sum_le_sum_of_subset hK

theorem scaled_partial_sum (L K : Finset ι) (A : ι → Finset V) (c : ι → V → ℚ)
    (nonneg : ∀ i v, 0 ≤ c i v) (hK : K ⊆ L) (x : ι → V) (hx : ∀ i ∈ K, x i ∈ A i) :
    ((∑ i ∈ K, scaledCosts L A c i (x i) : ℕ) : ℚ) =
      commonDenominator L A c * ∑ i ∈ K, c i (x i) := by
  rw [Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact scaledCosts_cast L A c nonneg i (hK hi) (x i) (hx i hi)

/-- The signed integer numerator of a residual budget in the common scale. -/
def residualNumerator (L K : Finset ι) (A : ι → Finset V) (c : ι → V → ℚ)
    (b : ℕ) (x : ι → V) : ℤ :=
  (b : ℤ) - (∑ i ∈ K, scaledCosts L A c i (x i) : ℕ)

theorem residualNumerator_eq (L K : Finset ι) (A : ι → Finset V) (c : ι → V → ℚ)
    (nonneg : ∀ i v, 0 ≤ c i v) (hK : K ⊆ L) (b : ℕ) (x : ι → V)
    (hx : ∀ i ∈ K, x i ∈ A i) :
    (residualNumerator L K A c b x : ℚ) / commonDenominator L A c =
      (b : ℚ) / commonDenominator L A c - ∑ i ∈ K, c i (x i) := by
  have heq := scaled_partial_sum L K A c nonneg hK x hx
  have hD : (commonDenominator L A c : ℚ) ≠ 0 := by
    exact_mod_cast (commonDenominator_pos L A c).ne'
  simp only [residualNumerator, Int.cast_sub, Int.cast_natCast]
  rw [heq]
  field_simp

theorem residualNumerator_natAbs_le (L K : Finset ι) (A : ι → Finset V) (c : ι → V → ℚ)
    (hK : K ⊆ L) (b : ℕ) (hb : b ≤ upperBudget L A (scaledCosts L A c))
    (x : ι → V) (hx : ∀ i ∈ K, x i ∈ A i) :
    (residualNumerator L K A c b x).natAbs ≤ upperBudget L A (scaledCosts L A c) := by
  have hp := partialScaledCost_le_upper L K A c hK x hx
  have hz : |residualNumerator L K A c b x| ≤
      (upperBudget L A (scaledCosts L A c) : ℤ) := by
    apply abs_le.mpr
    unfold residualNumerator
    constructor <;> omega
  rw [← Int.natCast_natAbs] at hz
  exact_mod_cast hz

/-- Fraction normalization cannot increase either numerator magnitude or the
positive denominator. -/
theorem normalized_fraction_bounds (z : ℤ) (D : ℕ) (hD : 0 < D) :
    (((z : ℚ) / D).num).natAbs ≤ z.natAbs ∧ ((z : ℚ) / D).den ≤ D := by
  have heq : (z : ℚ) / D = Rat.divInt z (D : ℤ) := by simp [Rat.divInt_eq_div]
  rw [heq]
  constructor
  · rw [Rat.num_divInt]
    have hs : (D : ℤ).sign = 1 := Int.sign_eq_one_iff_pos.mpr (by exact_mod_cast hD)
    rw [hs, one_mul]
    exact Int.natAbs_ediv_le_natAbs _ _
  · rw [Rat.den_divInt]
    simp only [Int.natCast_eq_zero, ne_eq, hD.ne', ↓reduceIte, Int.natAbs_natCast]
    exact Nat.div_le_self _ _

theorem binaryLength_mono : Monotone binaryLength := by
  intro a b hab
  have h := Nat.log_mono_right (b := 2) hab
  simp only [← Nat.log2_eq_log_two] at h
  unfold binaryLength
  omega

/-- Actual normalized rational residual budgets have at most `4S+2` unsigned
numerator/denominator bits (plus one sign bit if negative). -/
theorem residualBudget_rationalBits (L K : Finset ι) (A : ι → Finset V) (c : ι → V → ℚ)
    (nonneg : ∀ i v, 0 ≤ c i v) (hK : K ⊆ L)
    (b : ℕ) (hb : b ≤ upperBudget L A (scaledCosts L A c))
    (x : ι → V) (hx : ∀ i ∈ K, x i ∈ A i) :
    rationalBits ((b : ℚ) / commonDenominator L A c - ∑ i ∈ K, c i (x i)) ≤
      4 * numericSize L A c + 2 := by
  rw [← residualNumerator_eq L K A c nonneg hK b x hx]
  have hn := residualNumerator_natAbs_le L K A c hK b hb x hx
  have hn' := binaryLength_mono hn
  have hbnum := upperBudget_binaryLength L A c
  have hbden := commonDenominator_binaryLength L A c
  have hnorm := normalized_fraction_bounds (residualNumerator L K A c b x)
    (commonDenominator L A c) (commonDenominator_pos L A c)
  have hnum := binaryLength_mono hnorm.1
  have hden := binaryLength_mono hnorm.2
  unfold rationalBits binaryLength at *
  omega

end IndependentSetDiscovery.Algorithms
