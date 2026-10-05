import IndependentSetDiscovery.Algorithms.EncodedInput
import IndependentSetDiscovery.Algorithms.EagerFamilyBounds
import IndependentSetDiscovery.Algorithms.EagerBitWork

/-! # Closed bounds for the actual finite-table encoded optimizer

The counters include candidate materialization, capped threshold preparation,
complete binary optimization and self-reduction, and bounded output caching.
These statements concern the measured driver rather than the earlier semantic
optimizer or a freely supplied operation tariff.
-/
namespace IndependentSetDiscovery.Algorithms.EncodedInput

variable {k n : ℕ} (E : EncodedInput k n)

/-- A universal polynomial covering both the measured core and every encoded
boundary operation; no graph-class parameter occurs in this polynomial. -/
def measuredInputPolynomial (k n B : ℕ) : ℕ :=
  8 * eagerInputPolynomial k n B +
    (k+1)*(12*(n+1)+38) + 5*k*(n+1) + k*(k+2) + 2

theorem measuredInputPolynomial_mono (k n : ℕ) : Monotone (measuredInputPolynomial k n) := by
  intro B C h
  unfold measuredInputPolynomial eagerInputPolynomial
  gcongr

theorem runPrepared_le_exp [NeZero n] {d : ℕ} (hd : 2 ≤ d) (hk : 2 ≤ k)
    (table : Vector ℕ (k+1))
    (htable : ∀ r : Fin (k+1), table[r] = min (n+1) (balancedSearchThreshold d r)) :
    (E.runPrepared table).2 ≤ 5*k*(n+1) +
      8 * (2^(10*d*k*(k.log2+1)) * eagerInputPolynomial k n E.inputBits) + k*(k+2) := by
  have hc := eagerComplete_balanced_bound (Compatible E.graph) E.normalizedCost
    hd hk table htable Finset.univ E.candidateTableCounted.1
  have hn : numericSize Finset.univ (fun i => E.candidateTableCounted.1[i])
      E.normalizedCost ≤ E.inputBits := by
    rw [E.candidateTableCounted_value]
    exact E.normalized_numericSize_le
  have hp : eagerInputPolynomial k n
      (numericSize Finset.univ (fun i => E.candidateTableCounted.1[i]) E.normalizedCost) ≤
        eagerInputPolynomial k n E.inputBits := by
    unfold eagerInputPolynomial
    gcongr
  have hb := hc.trans (Nat.mul_le_mul_left _ hp)
  unfold runPrepared runPreparedVector
  dsimp only
  rw [E.candidateTableCounted_work]
  split_ifs <;> nlinarith only [hb, Nat.zero_le (k*(k+2))]

/-- Exact uniform `2^{O(d k log k)}` for the counter returned by the complete
encoded driver, including every preprocessing and output stage. -/
theorem solveMeasured_le_exp {d : ℕ} (hd : 2 ≤ d) (hk : 2 ≤ k) :
    (E.solveMeasured d).2 ≤
      2^(10*d*k*(k.log2+1)) * measuredInputPolynomial k n E.inputBits := by
  have hk0 : k ≠ 0 := by omega
  have hpow : 1 ≤ 2^(10*d*k*(k.log2+1)) := Nat.one_le_pow _ _ (by decide)
  by_cases hn : n = 0
  · simp only [solveMeasured, dif_neg hk0, dif_pos hn]
    have hpoly : 2 ≤ measuredInputPolynomial k n E.inputBits := by
      unfold measuredInputPolynomial
      omega
    exact hpoly.trans (Nat.le_mul_of_pos_left _ hpow)
  · letI : NeZero n := ⟨hn⟩
    have hrun := E.runPrepared_le_exp hd hk (ThresholdPreparation.balancedTable k n d).1
      (ThresholdPreparation.balancedTable_spec k n d).1
    have hprep := (ThresholdPreparation.balancedTable_spec k n d).2
    have hbase := Nat.mul_le_mul_right
      ((k+1)*(12*(n+1)+38)+5*k*(n+1)+k*(k+2)+2) hpow
    simp only [solveMeasured, dif_neg hk0, dif_neg hn, solvePositiveMeasured]
    unfold measuredInputPolynomial
    nlinarith only [hrun, hprep, hbase]


theorem solveMeasuredVector_le_exp {d : ℕ} (hd : 2 ≤ d) (hk : 2 ≤ k) :
    (E.solveMeasuredVector d).2 ≤
      2^(10*d*k*(k.log2+1)) * measuredInputPolynomial k n E.inputBits := by
  rw [E.solveMeasuredVector_work]
  exact E.solveMeasured_le_exp hd hk

/-- Exponential bound for the canonical binary solver from `EagerBitWork`.
Its padded-register model and operand certificates are defined there. -/
theorem solveBinary_le_exp {d : ℕ} (hd : 2 ≤ d) (hk : 2 ≤ k) :
    (E.solveBinary d).2 ≤ 2^(10*d*k*(k.log2+1)) *
      (measuredInputPolynomial k n E.inputBits *
        binaryScalarTariff (binaryRegisterWidth E.inputBits k n (binaryLength d))) := by
  exact (Nat.mul_le_mul_right _ (E.solveMeasured_le_exp hd hk)).trans
    (le_of_eq (by ring))

end IndependentSetDiscovery.Algorithms.EncodedInput
