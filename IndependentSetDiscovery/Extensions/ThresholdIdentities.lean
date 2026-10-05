import IndependentSetDiscovery.Extensions.Arithmetic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.Floor.Ring

/-! Identification of the executable integer threshold with equation (11). -/

namespace IndependentSetDiscovery

theorem ceilSqrt_eq_natCeil_sqrt (n : ℕ) :
    ceilSqrt n = ⌈Real.sqrt (n : ℝ)⌉₊ := by
  apply Nat.le_antisymm
  · apply (ceilSqrt_le_iff n _).mpr
    have h := (Real.sqrt_le_iff.mp (Nat.le_ceil (Real.sqrt (n : ℝ)))).2
    exact_mod_cast h
  · apply Nat.ceil_le.mpr
    apply Real.sqrt_le_iff.mpr
    refine ⟨Nat.cast_nonneg _, ?_⟩
    exact_mod_cast le_ceilSqrt_sq n

theorem edgePrefixThreshold_eq_paper (m r : ℕ) :
    edgePrefixThreshold m r =
      8 * (r - 1) + ⌈4 * Real.sqrt ((m : ℝ) * (r - 1 : ℕ))⌉₊ + 1 := by
  unfold edgePrefixThreshold
  rw [ceilSqrt_eq_natCeil_sqrt]
  congr 2
  congr 1
  push_cast
  rw [mul_assoc, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16)]
  norm_num

end IndependentSetDiscovery
