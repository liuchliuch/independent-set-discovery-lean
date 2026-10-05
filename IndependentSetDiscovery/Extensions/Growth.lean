import IndependentSetDiscovery.Extensions.Arithmetic
import IndependentSetDiscovery.Extremal.Growth
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Exact parameter dependence for Theorems 5.2 and 5.3 -/

namespace IndependentSetDiscovery

private theorem nat_add_sq_le (x y : ℕ) : (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by
  have h : ((x : ℤ) + y) ^ 2 ≤ 2 * ((x : ℤ) ^ 2 + (y : ℤ) ^ 2) := add_sq_le
  exact_mod_cast h

theorem ceilSqrt_sq_le (n : ℕ) : ceilSqrt n ^ 2 ≤ 2 * n + 2 := by
  have hle := Nat.pow_le_pow_left (ceilSqrt_le_sqrt_add_one n) 2
  have hadd := nat_add_sq_le n.sqrt 1
  have hs := Nat.sqrt_le' n
  nlinarith

theorem ceilSqrt_mono : Monotone ceilSqrt := by
  intro m n h
  exact (ceilSqrt_le_iff m _).mpr (h.trans (le_ceilSqrt_sq n))

theorem edgePrefixThreshold_mono (m : ℕ) : Monotone (edgePrefixThreshold m) := by
  intro r s h
  have hp : r - 1 ≤ s - 1 := Nat.sub_le_sub_right h 1
  have hs := ceilSqrt_mono (Nat.mul_le_mul_left (16 * m) hp)
  unfold edgePrefixThreshold
  omega

theorem degeneracyPrefixThreshold_mono (a : ℕ) : Monotone (degeneracyPrefixThreshold a) := by
  intro r s h
  unfold degeneracyPrefixThreshold
  gcongr

/-- The edge threshold is `O(k + sqrt(k*m))`, with an explicit squared envelope. -/
theorem edgePrefixThreshold_sq_le {m k : ℕ} (hk : 1 ≤ k) :
    edgePrefixThreshold m k ^ 2 ≤ 300 * k ^ 2 * (m + 1) := by
  let R := k - 1
  let q := ceilSqrt (16 * m * R)
  have hq : q ^ 2 ≤ 32 * m * R + 2 := by
    have h := ceilSqrt_sq_le (16 * m * R)
    dsimp [q]
    nlinarith only [h]
  have hR : R ≤ k := Nat.sub_le k 1
  have hkSq : k ≤ k ^ 2 := Nat.le_self_pow (by decide : 2 ≠ 0) k
  have hleft : 8 * R + 1 ≤ 9 * k := by omega
  have hleftSq := Nat.pow_le_pow_left hleft 2
  have hmk := Nat.mul_le_mul_left (32 * m) (hR.trans hkSq)
  have hsum := nat_add_sq_le (8 * R + 1) q
  have hsq : 1 ≤ k ^ 2 := by nlinarith
  have heq : edgePrefixThreshold m k = (8 * R + 1) + q := by
    simp [edgePrefixThreshold, R, q, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  rw [heq]
  nlinarith only [hq, hleftSq, hmk, hsum, hsq]

theorem degeneracyPrefixThreshold_le {a k : ℕ} (hk : 1 ≤ k) :
    degeneracyPrefixThreshold a k ≤ 17 * k * (a + 1) := by
  have hR : k - 1 ≤ k := Nat.sub_le k 1
  have hmul := Nat.mul_le_mul_right (4 * a + 1) (Nat.mul_le_mul_left 4 hR)
  unfold degeneracyPrefixThreshold
  nlinarith

private theorem dyadic_degree_two (k : ℕ) :
    32 * k ^ 2 ≤ 2 ^ (7 * (k.log2 + 1)) := by
  have hk := nat_le_two_pow_log2_succ k
  calc
    _ ≤ 32 * (2 ^ (k.log2 + 1)) ^ 2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hk 2)
    _ = 2 ^ (5 + 2 * (k.log2 + 1)) := by
      rw [← pow_mul, show 32 = 2 ^ 5 by norm_num, ← pow_add]
      congr 1
      ring
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)

private theorem dyadic_degree_four (k : ℕ) :
    512 * k ^ 4 ≤ 2 ^ (13 * (k.log2 + 1)) := by
  have hk := nat_le_two_pow_log2_succ k
  calc
    _ ≤ 512 * (2 ^ (k.log2 + 1)) ^ 4 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hk 4)
    _ = 2 ^ (9 + 4 * (k.log2 + 1)) := by
      rw [← pow_mul, show 512 = 2 ^ 9 by norm_num, ← pow_add]
      congr 1
      ring
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)

/-- The exact natural-number factor `2^{O(k log k)}(a+1)^k`. -/
theorem degeneracy_search_factor_le_exp {a k : ℕ} (hk : 1 ≤ k) :
    (k * degeneracyPrefixThreshold a k) ^ k ≤
      2 ^ (7 * k * (k.log2 + 1)) * (a + 1) ^ k := by
  have hL := degeneracyPrefixThreshold_le (a := a) hk
  have hbase : k * degeneracyPrefixThreshold a k ≤
      2 ^ (7 * (k.log2 + 1)) * (a + 1) := by
    have hmul := Nat.mul_le_mul_left k hL
    have hdyad := Nat.mul_le_mul_right (a + 1) (dyadic_degree_two k)
    nlinarith
  calc
    _ ≤ (2 ^ (7 * (k.log2 + 1)) * (a + 1)) ^ k := Nat.pow_le_pow_left hbase k
    _ = _ := by rw [mul_pow, ← pow_mul]; congr 2 <;> ring

/-- Integer squared certificate for the edge-sensitive XP factor. -/
theorem edge_search_factor_sq_le_exp {m k : ℕ} (hk : 1 ≤ k) :
    ((k * edgePrefixThreshold m k) ^ k) ^ 2 ≤
      2 ^ (13 * k * (k.log2 + 1)) * (m + 1) ^ k := by
  have hL := edgePrefixThreshold_sq_le (m := m) hk
  have hbase : (k * edgePrefixThreshold m k) ^ 2 ≤
      2 ^ (13 * (k.log2 + 1)) * (m + 1) := by
    have hmul := Nat.mul_le_mul_left (k ^ 2) hL
    have hdyad := Nat.mul_le_mul_right (m + 1) (dyadic_degree_four k)
    nlinarith only [hmul, hdyad, Nat.zero_le (212 * k ^ 4 * (m + 1))]
  calc
    _ = ((k * edgePrefixThreshold m k) ^ 2) ^ k := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm k 2]
    _ ≤ (2 ^ (13 * (k.log2 + 1)) * (m + 1)) ^ k := Nat.pow_le_pow_left hbase k
    _ = _ := by rw [mul_pow, ← pow_mul]; congr 2 <;> ring

/-- Theorem 5.2's exact real-valued square-root factor, including odd `k`.
The exponent constant is deliberately conservative and uniform in `m,k`. -/
theorem edge_search_factor_le_real {m k : ℕ} (hk : 1 ≤ k) :
    (((k * edgePrefixThreshold m k) ^ k : ℕ) : ℝ) ≤
      (2 : ℝ) ^ (13 * k * (k.log2 + 1)) * (m + 1 : ℝ) ^ ((k : ℝ) / 2) := by
  let E := 13 * k * (k.log2 + 1)
  let b : ℝ := (m + 1 : ℝ) ^ ((k : ℝ) / 2)
  have hb : 0 ≤ b := Real.rpow_nonneg (by positivity) _
  have hb2 : b ^ 2 = (m + 1 : ℝ) ^ k := by
    dsimp [b]
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity)]
    norm_num only [Nat.cast_ofNat]
    rw [show (k : ℝ) / 2 * (2 : ℝ) = k by ring, Real.rpow_natCast]
  have hsq : ((((k * edgePrefixThreshold m k) ^ k : ℕ) : ℝ)) ^ 2 ≤
      (2 : ℝ) ^ E * (m + 1 : ℝ) ^ k := by
    exact_mod_cast edge_search_factor_sq_le_exp (m := m) hk
  have hA : (1 : ℝ) ≤ 2 ^ E := one_le_pow₀ (by norm_num)
  have hAsq : (2 : ℝ) ^ E ≤ (2 ^ E) ^ 2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hAsq (show 0 ≤ (m + 1 : ℝ) ^ k by positivity)
  have hrhs : 0 ≤ (2 : ℝ) ^ E * b := by positivity
  have hfinal : ((((k * edgePrefixThreshold m k) ^ k : ℕ) : ℝ)) ^ 2 ≤
      ((2 : ℝ) ^ E * b) ^ 2 := by
    rw [show ((2 : ℝ) ^ E * b) ^ 2 = ((2 : ℝ) ^ E) ^ 2 * b ^ 2 by ring, hb2]
    exact hsq.trans hm
  change _ ≤ (2 : ℝ) ^ E * b
  nlinarith

end IndependentSetDiscovery
