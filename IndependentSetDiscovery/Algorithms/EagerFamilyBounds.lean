import IndependentSetDiscovery.Algorithms.EagerCompleteBounds
import IndependentSetDiscovery.Algorithms.CappedThreshold
import IndependentSetDiscovery.Extremal.Growth
import IndependentSetDiscovery.Extensions.Growth

/-!
# Full measured optimization: all graph-family parameter factors

Every bound below is on the actual `optimizeEagerComplete` counter, including
its concrete preprocessing. The finite threshold vector has already been
prepared; its separately measured preparation cost is added by encoded drivers.
-/
namespace IndependentSetDiscovery.Algorithms

variable (R : Fin n → Fin n → Prop) [DecidableRel R] (cost : Fin k → Fin n → ℚ)
variable [Inhabited (Fin n)]

/-- A universal input polynomial, independent of all graph-class parameters. -/
def eagerInputPolynomial (k n S : ℕ) : ℕ :=
  (6*S+6+(k+1)*(n+1))*256*(k+1)^2*(n+1)^2

theorem eagerComplete_cached_le_factor (threshold : ℕ → ℕ)
    (positive : ∀ r, 0 < threshold r) (mono : Monotone threshold)
    (table : Vector ℕ (k+1))
    (htable : ∀ r : Fin (k+1), table[r] = min (n+1) (threshold r))
    (hk : 2 ≤ k) (L : Finset (Fin k)) (rows : Vector (Finset (Fin n)) k) :
    (optimizeEagerComplete R cost (cachedThreshold table) L rows).2 ≤
      eagerInputPolynomial k n (numericSize L (fun i => rows[i]) cost) * (k*threshold k)^k := by
  have hw := optimizeEagerComplete_cost_le R cost (cachedThreshold table) (threshold k)
    (cachedThreshold_bound threshold table htable mono) L rows
  have hb : 2 ≤ k*threshold k := by have := positive k; nlinarith
  have ht := treeBound_add_one_le (k*threshold k) k hb
  have ht' : treeBound (k*threshold k) k ≤ 2*(k*threshold k)^k := by omega
  calc
    _ ≤ (6*numericSize L (fun i => rows[i]) cost+6+(k+1)*(n+1)) *
        (128*(k+1)^2*(n+1)^2) * (2*(k*threshold k)^k) :=
      hw.trans (Nat.mul_le_mul_left _ ht')
    _ = _ := by unfold eagerInputPolynomial; ring

/-- Theorem 4.4's full optimization bound on the measured finite-table machine. -/
theorem eagerComplete_balanced_bound {d : ℕ} (hd : 2 ≤ d) (hk : 2 ≤ k)
    (table : Vector ℕ (k+1))
    (htable : ∀ r : Fin (k+1), table[r] = min (n+1) (balancedSearchThreshold d r))
    (L : Finset (Fin k)) (rows : Vector (Finset (Fin n)) k) :
    (optimizeEagerComplete R cost (cachedThreshold table) L rows).2 ≤
      2^(10*d*k*(k.log2+1)) * eagerInputPolynomial k n (numericSize L (fun i => rows[i]) cost) := by
  have hw := eagerComplete_cached_le_factor R cost (balancedSearchThreshold d)
    (balancedSearchThreshold_pos hd) (balancedSearchThreshold_mono d) table htable hk L rows
  rw [balancedSearchThreshold_eq hk] at hw
  have hg := balanced_search_factor_le_exp (d := d) (k := k) (by omega) (by omega)
  have hm := Nat.mul_le_mul_left (eagerInputPolynomial k n (numericSize L (fun i => rows[i]) cost)) hg
  exact hw.trans (by simpa [Nat.mul_comm] using hm)

/-- Theorem 5.4, with the full uniform codegree parameter dependence. -/
theorem eagerComplete_codegree_bound {s q : ℕ} (hs : 1 ≤ s) (hk : 2 ≤ k)
    (table : Vector ℕ (k+1))
    (htable : ∀ r : Fin (k+1), table[r] = min (n+1) (codegreeSearchThreshold s q r))
    (L : Finset (Fin k)) (rows : Vector (Finset (Fin n)) k) :
    (optimizeEagerComplete R cost (cachedThreshold table) L rows).2 ≤
      2^(10*s*k*(k.log2+1)+k*((q+1).log2+1)) *
        eagerInputPolynomial k n (numericSize L (fun i => rows[i]) cost) := by
  have hw := eagerComplete_cached_le_factor R cost (codegreeSearchThreshold s q)
    (codegreeSearchThreshold_pos s q) (codegreeSearchThreshold_mono s q) table htable hk L rows
  have hg := codegree_search_factor_le_exp (s := s) (q := q) (k := k) hs (by omega)
  have hm := Nat.mul_le_mul_left (eagerInputPolynomial k n (numericSize L (fun i => rows[i]) cost)) hg
  exact hw.trans (by simpa [codegreeSearchThreshold, Nat.mul_comm] using hm)

/-- Theorem 5.5: the smaller biclique side controls the `k log k` exponent. -/
theorem eagerComplete_unbalanced_bound {s t : ℕ} (hs : 1 ≤ s) (ht : 0 < t) (hk : 2 ≤ k)
    (table : Vector ℕ (k+1))
    (htable : ∀ r : Fin (k+1), table[r] = min (n+1) (codegreeSearchThreshold s (t-1) r))
    (L : Finset (Fin k)) (rows : Vector (Finset (Fin n)) k) :
    (optimizeEagerComplete R cost (cachedThreshold table) L rows).2 ≤
      2^(10*s*k*(k.log2+1)+k*(t.log2+1)) *
        eagerInputPolynomial k n (numericSize L (fun i => rows[i]) cost) := by
  have h := eagerComplete_codegree_bound R cost hs hk table htable L rows
  simpa [Nat.sub_add_cancel ht] using h

/-- Theorem 5.3's direct degeneracy algorithm, including all optimization stages. -/
theorem eagerComplete_degeneracy_bound (a : ℕ) (hk : 2 ≤ k)
    (table : Vector ℕ (k+1))
    (htable : ∀ r : Fin (k+1), table[r] = min (n+1) (degeneracyPrefixThreshold a r))
    (L : Finset (Fin k)) (rows : Vector (Finset (Fin n)) k) :
    (optimizeEagerComplete R cost (cachedThreshold table) L rows).2 ≤
      2^(7*k*(k.log2+1)) * (a+1)^k *
        eagerInputPolynomial k n (numericSize L (fun i => rows[i]) cost) := by
  have hw := eagerComplete_cached_le_factor R cost (degeneracyPrefixThreshold a)
    (degeneracyPrefixThreshold_pos a) (degeneracyPrefixThreshold_mono a) table htable hk L rows
  have hg := degeneracy_search_factor_le_exp (a := a) (k := k) (by omega)
  exact hw.trans (by simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
    Nat.mul_le_mul_left (eagerInputPolynomial k n (numericSize L (fun i => rows[i]) cost)) hg)

/-- Theorem 5.2, including odd `k`: a genuine real square-root factor rather
than an integer exponent rounded up to the next full power of `m+1`. -/
theorem eagerComplete_edge_bound (m : ℕ) (hk : 2 ≤ k)
    (table : Vector ℕ (k+1))
    (htable : ∀ r : Fin (k+1), table[r] = min (n+1) (edgePrefixThreshold m r))
    (L : Finset (Fin k)) (rows : Vector (Finset (Fin n)) k) :
    ((optimizeEagerComplete R cost (cachedThreshold table) L rows).2 : ℝ) ≤
      (2 : ℝ)^(13*k*(k.log2+1)) * (m+1 : ℝ)^((k : ℝ)/2) *
        eagerInputPolynomial k n (numericSize L (fun i => rows[i]) cost) := by
  have hw := eagerComplete_cached_le_factor R cost (edgePrefixThreshold m)
    (edgePrefixThreshold_pos m) (edgePrefixThreshold_mono m) table htable hk L rows
  have hg := edge_search_factor_le_real (m := m) (k := k) (by omega)
  have hw' : ((optimizeEagerComplete R cost (cachedThreshold table) L rows).2 : ℝ) ≤
      (eagerInputPolynomial k n (numericSize L (fun i => rows[i]) cost) : ℝ) *
        ((k*edgePrefixThreshold m k)^k : ℕ) := by exact_mod_cast hw
  apply hw'.trans
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    mul_le_mul_of_nonneg_left hg
      (show (0 : ℝ) ≤ eagerInputPolynomial k n (numericSize L (fun i => rows[i]) cost) by positivity)

end IndependentSetDiscovery.Algorithms
