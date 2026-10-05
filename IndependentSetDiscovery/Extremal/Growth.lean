import IndependentSetDiscovery.Extremal.Threshold
import Mathlib.Data.Nat.Log

/-!
# Explicit uniform parameter dependence

These inequalities expose constants in the paper's exponential bounds. They
hold uniformly in the biclique and codegree parameters, so the constants do
not hide an extra `s log s` or `d log d` dependence.
-/
namespace IndependentSetDiscovery

/-- Exact balanced thresholds are monotone in the number of residual labels. -/
theorem balancedThreshold_mono (d : ℕ) : Monotone (balancedThreshold d) := by
  intro r r' h
  unfold balancedThreshold
  gcongr

/-- The two-label clamp used by the total recursion preserves the final bound. -/
theorem balancedThreshold_max_two_le {d r k : ℕ} (hk : 2 ≤ k) (hr : r ≤ k) :
    balancedThreshold d (max 2 r) ≤ balancedThreshold d k :=
  balancedThreshold_mono d (max_le hk hr)

/-- Codegree thresholds are monotone after converting label count to `r-1`. -/
theorem codegreeThreshold_pred_mono (s q : ℕ) :
    Monotone (fun r => codegreeThreshold s q (r - 1)) := by
  intro r r' h
  exact codegreeThreshold_mono s q (Nat.sub_le_sub_right h 1)

/-- The codegree analogue of the two-label clamp. -/
theorem codegreeThreshold_max_two_le {s q r k : ℕ} (hk : 2 ≤ k) (hr : r ≤ k) :
    codegreeThreshold s q (max 2 r - 1) ≤ codegreeThreshold s q (k - 1) :=
  codegreeThreshold_pred_mono s q (max_le hk hr)

/-- The balanced threshold is positive throughout the algorithmic range. -/
theorem balancedThreshold_pos_of_one_le {d r : ℕ} (hd : 1 ≤ d) (hr : 2 ≤ r) :
    0 < balancedThreshold d r := by
  have hd' : 0 < d := by omega
  have hr' : 0 < r - 1 := by omega
  have hterm : 0 < 4 * d ^ 2 * (r - 1) := by positivity
  unfold balancedThreshold
  omega

/-- The balanced search tree has branching bound at least two. -/
theorem two_le_balanced_branching {d k : ℕ} (hd : 1 ≤ d) (hk : 2 ≤ k) :
    2 ≤ k * balancedThreshold d k := by
  have h := balancedThreshold_pos_of_one_le hd hk
  nlinarith

/-- The bounded-codegree search tree has branching bound at least two. -/
theorem two_le_codegree_branching (s q : ℕ) {k : ℕ} (hk : 2 ≤ k) :
    2 ≤ k * codegreeThreshold s q (k - 1) := by
  have h := codegreeThreshold_pos s q (k - 1)
  nlinarith

/-- A uniform envelope for the exact bounded-codegree prefix threshold. -/
theorem codegreeThreshold_le_envelope {s q R k : ℕ} (hs : 1 ≤ s)
    (hk : 1 ≤ k) (hR : R ≤ k) :
    codegreeThreshold s q R ≤ (q + 1) * (16 * k) ^ s := by
  have hs0 : s ≠ 0 := by omega
  have hbase : 8 * k ≤ (8 * k) ^ s := Nat.le_self_pow hs0 _
  have hsPow : s + 1 ≤ 2 ^ s := Nat.succ_le_of_lt (Nat.lt_two_pow_self)
  have hlin : 8 * s * R + 1 ≤ (16 * k) ^ s := by
    calc
      _ ≤ (8 * k) * (s + 1) := by nlinarith only [hk, hR]
      _ ≤ (8 * k) * 2 ^ s := Nat.mul_le_mul_left _ hsPow
      _ ≤ (8 * k) ^ s * 2 ^ s := Nat.mul_le_mul_right _ hbase
      _ = (16 * k) ^ s := by rw [← mul_pow]; congr 1; ring
  have hmain : q * (8 * R) ^ s ≤ q * (16 * k) ^ s := by gcongr <;> omega
  unfold codegreeThreshold
  nlinarith only [hlin, hmain]

/-- A uniform envelope for the sharper exact balanced threshold. -/
theorem balancedThreshold_le_envelope {d r k : ℕ} (hd : 1 ≤ d)
    (hr : r ≤ k) : balancedThreshold d r ≤ (16 * k) ^ d := by
  have hd0 : d ≠ 0 := by omega
  have hR : r - 1 ≤ k := by omega
  have hbase : 4 * k ≤ (4 * k) ^ d := Nat.le_self_pow hd0 _
  have hlin : 4 * d ^ 2 * (r - 1) ≤ d ^ 2 * (4 * k) ^ d := by
    have hm := Nat.mul_le_mul_left (d ^ 2) hbase
    nlinarith only [hR, hm]
  have hmain : (d - 1) * (4 * (r - 1)) ^ d ≤ (d - 1) * (4 * k) ^ d := by
    gcongr
  have hcoeff : d - 1 + d ^ 2 ≤ (d + 1) ^ 2 := by nlinarith [Nat.sub_le d 1]
  have hdPow : d + 1 ≤ 2 ^ d := Nat.succ_le_of_lt (Nat.lt_two_pow_self)
  have hsquare : (d + 1) ^ 2 ≤ 4 ^ d := by
    calc
      _ ≤ (2 ^ d) ^ 2 := Nat.pow_le_pow_left hdPow 2
      _ = 4 ^ d := by rw [← pow_mul, Nat.mul_comm d 2, pow_mul]; norm_num
  calc
    balancedThreshold d r ≤ (d - 1 + d ^ 2) * (4 * k) ^ d := by
      unfold balancedThreshold
      nlinarith only [hlin, hmain]
    _ ≤ (d + 1) ^ 2 * (4 * k) ^ d := Nat.mul_le_mul_right _ hcoeff
    _ ≤ 4 ^ d * (4 * k) ^ d := Nat.mul_le_mul_right _ hsquare
    _ = (16 * k) ^ d := by rw [← mul_pow]; congr 1; ring

/-- Search-tree parameter factor for bounded codegree, before taking logs. -/
theorem codegree_search_factor_le {s q k : ℕ} (hs : 1 ≤ s) (hk : 1 ≤ k) :
    (k * codegreeThreshold s q (k - 1)) ^ k ≤
      (q + 1) ^ k * (16 * k) ^ (2 * s * k) := by
  have hL := codegreeThreshold_le_envelope (q := q) hs hk (Nat.sub_le k 1)
  have hb : 0 < 16 * k := by omega
  have hbound : k * codegreeThreshold s q (k - 1) ≤ (q + 1) * (16 * k) ^ (2 * s) := by
    calc
      _ ≤ (16 * k) * ((q + 1) * (16 * k) ^ s) :=
        Nat.mul_le_mul (by omega) hL
      _ = (q + 1) * (16 * k) ^ (s + 1) := by rw [pow_succ]; ring
      _ ≤ (q + 1) * (16 * k) ^ (2 * s) := by gcongr <;> omega
  calc
    _ ≤ ((q + 1) * (16 * k) ^ (2 * s)) ^ k := Nat.pow_le_pow_left hbound k
    _ = _ := by rw [mul_pow, ← pow_mul]

/-- Search-tree parameter factor for balanced biclique exclusion. -/
theorem balanced_search_factor_le {d k : ℕ} (hd : 1 ≤ d) (hk : 1 ≤ k) :
    (k * balancedThreshold d k) ^ k ≤ (16 * k) ^ (2 * d * k) := by
  have hL := balancedThreshold_le_envelope (d := d) hd (le_refl k)
  have hb : 0 < 16 * k := by omega
  have hbound : k * balancedThreshold d k ≤ (16 * k) ^ (2 * d) := by
    calc
      _ ≤ (16 * k) * (16 * k) ^ d := Nat.mul_le_mul (by omega) hL
      _ = (16 * k) ^ (d + 1) := (pow_succ' _ _).symm
      _ ≤ (16 * k) ^ (2 * d) := Nat.pow_le_pow_right hb (by omega)
  calc
    _ ≤ ((16 * k) ^ (2 * d)) ^ k := Nat.pow_le_pow_left hbound k
    _ = _ := (pow_mul _ _ _).symm

/-- A dyadic envelope valid also at zero. -/
theorem nat_le_two_pow_log2_succ (n : ℕ) : n ≤ 2 ^ (n.log2 + 1) := by
  simpa [Nat.log2_eq_log_two, Nat.succ_eq_add_one] using
    (Nat.lt_pow_succ_log_self (by decide : 1 < 2) n).le

/-- Encoding the polynomial base in binary. -/
theorem sixteen_mul_le_two_pow_log2 (k : ℕ) : 16 * k ≤ 2 ^ (k.log2 + 5) := by
  have h := Nat.mul_le_mul_left 16 (nat_le_two_pow_log2_succ k)
  calc
    _ ≤ 16 * 2 ^ (k.log2 + 1) := h
    _ = 2 ^ (k.log2 + 5) := by
      rw [show k.log2 + 5 = 4 + (k.log2 + 1) by omega, pow_add]
      norm_num [pow_add]

/-- Converting the constant-size base factor to a uniform logarithmic exponent. -/
theorem dyadic_exponent_le (a k : ℕ) :
    (k.log2 + 5) * (2 * a * k) ≤ 10 * a * k * (k.log2 + 1) := by
  calc
    _ ≤ (5 * (k.log2 + 1)) * (2 * a * k) :=
      Nat.mul_le_mul_right _ (by omega)
    _ = _ := by ring

/-- An explicit `2^{O(d k log k)}` bound with a universal constant. -/
theorem balanced_search_factor_le_exp {d k : ℕ} (hd : 1 ≤ d) (hk : 1 ≤ k) :
    (k * balancedThreshold d k) ^ k ≤ 2 ^ (10 * d * k * (k.log2 + 1)) := by
  calc
    _ ≤ (16 * k) ^ (2 * d * k) := balanced_search_factor_le hd hk
    _ ≤ (2 ^ (k.log2 + 5)) ^ (2 * d * k) :=
      Nat.pow_le_pow_left (sixteen_mul_le_two_pow_log2 k) _
    _ = 2 ^ ((k.log2 + 5) * (2 * d * k)) := (pow_mul _ _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (dyadic_exponent_le d k)

/-- An explicit `2^{O(s k log k + k log(q+1))}` bound with universal constants. -/
theorem codegree_search_factor_le_exp {s q k : ℕ} (hs : 1 ≤ s) (hk : 1 ≤ k) :
    (k * codegreeThreshold s q (k - 1)) ^ k ≤
      2 ^ (10 * s * k * (k.log2 + 1) + k * ((q + 1).log2 + 1)) := by
  calc
    _ ≤ (q + 1) ^ k * (16 * k) ^ (2 * s * k) := codegree_search_factor_le hs hk
    _ ≤ (2 ^ ((q + 1).log2 + 1)) ^ k *
        (2 ^ (k.log2 + 5)) ^ (2 * s * k) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left (nat_le_two_pow_log2_succ (q + 1)) k)
        (Nat.pow_le_pow_left (sixteen_mul_le_two_pow_log2 k) _)
    _ = 2 ^ (((q + 1).log2 + 1) * k + (k.log2 + 5) * (2 * s * k)) := by
      rw [← pow_mul, ← pow_mul, ← pow_add]
    _ ≤ _ := by
      apply Nat.pow_le_pow_right (by decide)
      calc
        _ ≤ ((q + 1).log2 + 1) * k + 10 * s * k * (k.log2 + 1) :=
          Nat.add_le_add_left (dyadic_exponent_le s k) _
        _ = _ := by ring

/-- Substituting `q=t-1` gives the exact unbalanced parameter dependence. -/
theorem unbalanced_search_factor_le_exp {s t k : ℕ} (hs : 1 ≤ s)
    (ht : 1 ≤ t) (hk : 1 ≤ k) :
    (k * codegreeThreshold s (t - 1) (k - 1)) ^ k ≤
      2 ^ (10 * s * k * (k.log2 + 1) + k * (t.log2 + 1)) := by
  simpa [Nat.sub_add_cancel ht] using codegree_search_factor_le_exp (q := t - 1) hs hk

end IndependentSetDiscovery
