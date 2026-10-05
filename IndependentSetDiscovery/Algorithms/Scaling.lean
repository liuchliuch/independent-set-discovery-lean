import IndependentSetDiscovery.Algorithms.State
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Log

namespace IndependentSetDiscovery.Algorithms

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V]

/-- Product clearing denominator. Its binary length is bounded by a sum of input lengths. -/
def commonDenominator (L : Finset ι) (A : ι → Finset V) (c : ι → V → ℚ) : ℕ :=
  ∏ i ∈ L, ∏ v ∈ A i, (c i v).den

theorem commonDenominator_pos (L : Finset ι) (A : ι → Finset V) (c : ι → V → ℚ) :
    0 < commonDenominator L A c := by
  exact Finset.prod_pos (fun i _ => Finset.prod_pos (fun v _ => (c i v).pos))

theorem denominator_dvd_common (L : Finset ι) (A : ι → Finset V) (c : ι → V → ℚ)
    (i : ι) (hi : i ∈ L) (v : V) (hv : v ∈ A i) :
    (c i v).den ∣ commonDenominator L A c := by
  exact (Finset.dvd_prod_of_mem (fun v => (c i v).den) hv).trans
    (Finset.dvd_prod_of_mem (fun i => ∏ v ∈ A i, (c i v).den) hi)

/-- Exact scaled nonnegative integer cost, computed using integer arithmetic only. -/
def scaleCost (D : ℕ) (q : ℚ) : ℕ := q.num.toNat * (D / q.den)

theorem scaleCost_cast (D : ℕ) (q : ℚ) (hq : 0 ≤ q) (hdiv : q.den ∣ D) :
    (scaleCost D q : ℚ) = D * q := by
  have hn : 0 ≤ q.num := Rat.num_nonneg.mpr hq
  have hnum : (q.num.toNat : ℚ) = q.num := by
    exact_mod_cast Int.toNat_of_nonneg hn
  have hden : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hD : (D : ℚ) = (D / q.den : ℕ) * (q.den : ℚ) := by
    exact_mod_cast (Nat.div_mul_cancel hdiv).symm
  simp only [scaleCost, Nat.cast_mul, hnum]
  have hqd : q * (q.den : ℚ) = q.num := (eq_div_iff hden).mp q.num_div_den.symm
  calc
    (q.num : ℚ) * (D / q.den : ℕ) = (q * (q.den : ℚ)) * (D / q.den : ℕ) := by rw [hqd]
    _ = D * q := by rw [hD]; ring

/-- Input numerical size, including one bit for zero numerators. -/
def rationalBits (q : ℚ) : ℕ := Nat.log2 q.num.natAbs + 1 + (Nat.log2 q.den + 1)

def denominatorBits (L : Finset ι) (A : ι → Finset V) (c : ι → V → ℚ) : ℕ :=
  ∑ i ∈ L, ∑ v ∈ A i, (Nat.log2 (c i v).den + 1)

theorem nat_lt_two_pow_bits (n : ℕ) : n < 2 ^ (Nat.log2 n + 1) := by
  simpa [Nat.log2_eq_log_two] using Nat.lt_pow_succ_log_self (by omega : 1 < 2) n

theorem commonDenominator_le_pow (L : Finset ι) (A : ι → Finset V) (c : ι → V → ℚ) :
    commonDenominator L A c ≤ 2 ^ denominatorBits L A c := by
  unfold commonDenominator denominatorBits
  calc
    _ ≤ ∏ i ∈ L, 2 ^ (∑ v ∈ A i, (Nat.log2 (c i v).den + 1)) := by
      apply Finset.prod_le_prod
      · intro i hi; omega
      · intro i hi
        calc
          _ ≤ ∏ v ∈ A i, 2 ^ (Nat.log2 (c i v).den + 1) := by
            apply Finset.prod_le_prod
            · intro v hv; omega
            · intro v hv; exact (nat_lt_two_pow_bits _).le
          _ = _ := Finset.prod_pow_eq_pow_sum (A i) _ 2
    _ = _ := Finset.prod_pow_eq_pow_sum L _ 2

def scaledCosts (L : Finset ι) (A : ι → Finset V) (c : ι → V → ℚ) : ι → V → ℕ :=
  fun i v => scaleCost (commonDenominator L A c) (c i v)

theorem scaledCosts_cast (L : Finset ι) (A : ι → Finset V) (c : ι → V → ℚ)
    (nonneg : ∀ i v, 0 ≤ c i v) (i : ι) (hi : i ∈ L) (v : V) (hv : v ∈ A i) :
    (scaledCosts L A c i v : ℚ) = commonDenominator L A c * c i v :=
  scaleCost_cast _ _ (nonneg i v) (denominator_dvd_common L A c i hi v hv)

theorem scaled_sum (L : Finset ι) (A : ι → Finset V) (c : ι → V → ℚ)
    (nonneg : ∀ i v, 0 ≤ c i v) (x : ι → V) (hx : ∀ i ∈ L, x i ∈ A i) :
    ((∑ i ∈ L, scaledCosts L A c i (x i) : ℕ) : ℚ) =
      commonDenominator L A c * ∑ i ∈ L, c i (x i) := by
  rw [Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact scaledCosts_cast L A c nonneg i hi (x i) (hx i hi)

/-- Every feasible selection has scaled cost bounded by this explicitly computable value. -/
def upperBudget (L : Finset ι) (A : ι → Finset V) (c : ι → V → ℕ) : ℕ :=
  ∑ i ∈ L, (A i).sup (c i)

theorem selection_le_upperBudget (L : Finset ι) (A : ι → Finset V)
    (c : ι → V → ℕ) (x : ι → V) (hx : ∀ i ∈ L, x i ∈ A i) :
    (∑ i ∈ L, c i (x i)) ≤ upperBudget L A c := by
  apply Finset.sum_le_sum
  intro i hi
  exact Finset.le_sup (hx i hi)

end IndependentSetDiscovery.Algorithms
