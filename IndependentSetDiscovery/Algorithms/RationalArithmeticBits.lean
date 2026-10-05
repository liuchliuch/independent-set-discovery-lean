import IndependentSetDiscovery.Algorithms.ResidualBits

/-!
# Bit bounds before rational normalization

The cross products and signed numerator sums used by exact rational arithmetic
are bounded as integers, not merely after gcd normalization. This also permits
an arbitrary supplied decision budget, whose encoding must be charged to input.
-/
namespace IndependentSetDiscovery.Algorithms

 theorem rational_num_le_pow (q : ℚ) : q.num.natAbs ≤ 2 ^ rationalBits q := by
  apply (nat_lt_two_pow_bits _).le.trans
  apply Nat.pow_le_pow_right (by omega)
  unfold rationalBits
  omega

 theorem rational_den_le_pow (q : ℚ) : q.den ≤ 2 ^ rationalBits q := by
  apply (nat_lt_two_pow_bits _).le.trans
  apply Nat.pow_le_pow_right (by omega)
  unfold rationalBits
  omega

 theorem rational_cross_le_pow (p q : ℚ) :
    (p.num * (q.den : ℤ)).natAbs ≤ 2 ^ (rationalBits p + rationalBits q) := by
  rw [Int.natAbs_mul, Int.natAbs_natCast, pow_add]
  exact Nat.mul_le_mul (rational_num_le_pow p) (rational_den_le_pow q)

 theorem rational_den_product_le_pow (p q : ℚ) :
    p.den * q.den ≤ 2 ^ (rationalBits p + rationalBits q) := by
  rw [pow_add]
  exact Nat.mul_le_mul (rational_den_le_pow p) (rational_den_le_pow q)

/-- Both comparison cross products, the signed subtraction before gcd, and
the unreduced denominator have linear binary length in the operand lengths. -/
theorem rational_arithmetic_intermediates (p q : ℚ) :
    binaryLength (p.num * (q.den : ℤ)).natAbs ≤ rationalBits p + rationalBits q + 1 ∧
    binaryLength (q.num * (p.den : ℤ)).natAbs ≤ rationalBits p + rationalBits q + 1 ∧
    binaryLength (p.num * (q.den : ℤ) - q.num * (p.den : ℤ)).natAbs ≤
      rationalBits p + rationalBits q + 2 ∧
    binaryLength (p.den * q.den) ≤ rationalBits p + rationalBits q + 1 := by
  have h₁ := rational_cross_le_pow p q
  have h₂ : (q.num * (p.den : ℤ)).natAbs ≤ 2 ^ (rationalBits p + rationalBits q) := by
    simpa [Nat.add_comm] using rational_cross_le_pow q p
  have hsub : (p.num * (q.den : ℤ) - q.num * (p.den : ℤ)).natAbs ≤
      2 ^ (rationalBits p + rationalBits q + 1) := by
    have h := Int.natAbs_sub_le (p.num * (q.den : ℤ)) (q.num * (p.den : ℤ))
    rw [pow_succ]
    omega
  exact ⟨binaryLength_le_of_le_pow h₁, binaryLength_le_of_le_pow h₂,
    by simpa [Nat.add_assoc] using binaryLength_le_of_le_pow hsub,
    binaryLength_le_of_le_pow (rational_den_product_le_pow p q)⟩

theorem rational_sub_fraction (p q : ℚ) :
    p - q = ((p.num * (q.den : ℤ) - q.num * (p.den : ℤ) : ℤ) : ℚ) /
      (p.den * q.den : ℕ) := by
  have hp : (p.den : ℚ) ≠ 0 := by exact_mod_cast p.den_nz
  have hq : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
  have heqp := p.num_div_den
  have heqq := q.num_div_den
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
  calc
    p - q = (p.num : ℚ) / p.den - (q.num : ℚ) / q.den := by rw [heqp, heqq]
    _ = _ := by field_simp

/-- Generic arbitrary-budget bound. Unlike the sharper common-scale bound,
this allows either operand to have an unrelated denominator and sign. -/
theorem rationalBits_sub_le (p q : ℚ) :
    rationalBits (p - q) ≤ 2 * (rationalBits p + rationalBits q) + 3 := by
  rw [rational_sub_fraction]
  have hn := normalized_fraction_bounds
    (p.num * (q.den : ℤ) - q.num * (p.den : ℤ)) (p.den * q.den)
    (Nat.mul_pos p.pos q.pos)
  have hb := rational_arithmetic_intermediates p q
  have hnum := binaryLength_mono hn.1
  have hden := binaryLength_mono hn.2
  unfold rationalBits binaryLength at *
  omega

@[simp] theorem rationalBits_neg (q : ℚ) : rationalBits (-q) = rationalBits q := by
  simp [rationalBits]

 theorem rationalBits_add_le (p q : ℚ) :
    rationalBits (p + q) ≤ 2 * (rationalBits p + rationalBits q) + 3 := by
  simpa using rationalBits_sub_le p (-q)

/-- The unnormalized numerator sum used by prefix-total accumulation and its
product denominator, before any gcd reduction. -/
theorem rational_addition_intermediates (p q : ℚ) :
    binaryLength (p.num * (q.den : ℤ) + q.num * (p.den : ℤ)).natAbs ≤
      rationalBits p + rationalBits q + 2 ∧
    binaryLength (p.den * q.den) ≤ rationalBits p + rationalBits q + 1 := by
  simpa using (rational_arithmetic_intermediates p (-q)).2.2

/-- Products are controlled before normalization as well. -/
theorem rational_multiplication_intermediates (p q : ℚ) :
    binaryLength (p.num * q.num).natAbs ≤ rationalBits p + rationalBits q + 1 ∧
    binaryLength (p.den * q.den) ≤ rationalBits p + rationalBits q + 1 := by
  refine ⟨binaryLength_le_of_le_pow ?_,
    binaryLength_le_of_le_pow (rational_den_product_le_pow p q)⟩
  rw [Int.natAbs_mul, pow_add]
  exact Nat.mul_le_mul (rational_num_le_pow p) (rational_num_le_pow q)

end IndependentSetDiscovery.Algorithms
