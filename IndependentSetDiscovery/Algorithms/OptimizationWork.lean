import IndependentSetDiscovery.Algorithms.CostModel
import IndependentSetDiscovery.Algorithms.OracleWork

/-!
# Complete optimization work

The oracle-work counter follows every actual decision invocation in the
executable optimizer. Administrative work is charged compositionally: initial
finite-list materialization/denominator clearing/scaling/maxima and at most one
quadratic finite-set pass per queried tentative assignment or budget. The fixed
up-front charge also pays for one candidate sorting pass in each witness round.
All numerical bit lengths are bounded separately in `BitComplexity`.
-/
namespace IndependentSetDiscovery.Algorithms

variable {ι V : Type*} [LinearOrder ι] [LinearOrder V] [Inhabited V]
variable (R : V → V → Prop) [DecidableRel R] (cost : ι → V → ℚ)
variable (ops : PrefixOperations V) (threshold : ℕ → ℕ)

/-- Input container size, independent of the currently tested budget. -/
def instanceMass (L : Finset ι) (A : ι → Finset V) : ℕ :=
  L.card + (∑ i ∈ L, (A i).card) + 1

/-- Exact charged work of one decision invocation. -/
def decisionRAMWork (s : State ι V) : ℕ :=
  runWork (prefixStep R cost ops threshold) (nodeWork R cost ops threshold) s.labels.card s

/-- Composed work, with separate explicit bills for preprocessing and each
actual queried child/budget. There is no oracle-correctness premise in this definition. -/
def optimizeRAMWork (L : Finset ι) (A : ι → Finset V) : ℕ :=
  let M := instanceMass L A
  16 * (M + 1)^3 +
  (optimizeCounted R cost ops threshold L A).2 * (8 * (M + 1)^2) +
  optimizeOracleWork R cost ops threshold (decisionRAMWork R cost ops threshold) L A

theorem treeBound_mono_depth (b : ℕ) : Monotone (treeBound b) := by
  apply monotone_nat_of_le_succ
  intro n
  by_cases hb : b = 0
  · subst b
    cases n <;> simp [treeBound]
  · simp only [treeBound]
    have hp := one_le_treeBound b n
    have hb' : 1 ≤ b := by omega
    nlinarith

theorem optimizeOracleRAMWork_le
    (symm : Symmetric R) (nonneg : ∀ i v, 0 ≤ cost i v)
    (positive : ∀ r, 0 < threshold r)
    (certificate : TransversalCertificate (ι := ι) R threshold)
    (L : Finset ι) (A : ι → Finset V) (maxThreshold : ℕ)
    (hthreshold : ∀ r ≤ L.card, threshold r ≤ maxThreshold) :
    optimizeOracleWork R cost ops threshold (decisionRAMWork R cost ops threshold) L A ≤
      (optimizationCalls (upperBudget L A (scaledCosts L A cost)) + ∑ i ∈ L, (A i).card) *
        (64 * (instanceMass L A + 1)^3 * treeBound (L.card * maxThreshold) L.card) := by
  let P : State ι V → Prop := fun s =>
    s.labels.card ≤ L.card ∧ stateMass s ≤ instanceMass L A
  apply optimizeOracleWork_le R cost ops threshold _ L A P
  · intro B
    exact ⟨le_rfl, le_rfl⟩
  · intro s hs i hi v
    exact ⟨(child_rank_lt R cost s i v hi).le.trans hs.1,
      (child_mass_le R cost s i v hi).trans hs.2⟩
  · intro s hs
    have hw := decisionWork_le R cost ops threshold symm nonneg positive certificate
      L.card maxThreshold hthreshold s hs.1
    apply hw.trans
    apply Nat.mul_le_mul
    · gcongr
      exact hs.2
    · exact treeBound_mono_depth _ hs.1

/-- Full optimization work is the same bounded-search factor times one fixed
polynomial in container size and binary numeric input size. -/
theorem optimizeRAMWork_le
    (symm : Symmetric R) (nonneg : ∀ i v, 0 ≤ cost i v)
    (positive : ∀ r, 0 < threshold r)
    (certificate : TransversalCertificate (ι := ι) R threshold)
    (L : Finset ι) (A : ι → Finset V) (maxThreshold : ℕ)
    (hthreshold : ∀ r ≤ L.card, threshold r ≤ maxThreshold) :
    optimizeRAMWork R cost ops threshold L A ≤
      256 * (instanceMass L A + numericSize L A cost + 1)^4 *
        treeBound (L.card * maxThreshold) L.card := by
  let M := instanceMass L A
  let S := numericSize L A cost
  let P := M + S + 1
  let T := treeBound (L.card * maxThreshold) L.card
  let Q := optimizationCalls (upperBudget L A (scaledCosts L A cost)) + ∑ i ∈ L, (A i).card
  have hT : 1 ≤ T := one_le_treeBound _ _
  have hCalls := optimizeCounted_calls R cost ops threshold L A
  have hOracle := optimizeOracleRAMWork_le R cost ops threshold symm nonneg positive certificate
    L A maxThreshold hthreshold
  have hNumeric := optimizationCalls_le_numericSize L A cost
  have hN : (∑ i ∈ L, (A i).card) ≤ M := by dsimp [M, instanceMass]; omega
  have hQ : Q + 1 ≤ 3 * P := by dsimp [Q, P, M, S] at *; omega
  have hMP : M + 1 ≤ P := by dsimp [P]; omega
  have hP : 1 ≤ P := by dsimp [P]; omega
  have hM2 : (M+1)^2 ≤ P^3 := by
    calc
      _ ≤ P^2 := Nat.pow_le_pow_left hMP 2
      _ ≤ P^3 := Nat.pow_le_pow_right hP (by omega)
  have hM3 : (M+1)^3 ≤ P^3 := Nat.pow_le_pow_left hMP 3
  have hT3 : P^3 ≤ P^3*T := Nat.le_mul_of_pos_right _ (by omega)
  have hBase : 16 * (M+1)^3 ≤ 16 * P^3 * T := by nlinarith
  have hAdmin : (optimizeCounted R cost ops threshold L A).2 * (8*(M+1)^2) ≤
      Q * (8*P^3*T) := by
    apply Nat.mul_le_mul hCalls
    nlinarith
  have hOr : optimizeOracleWork R cost ops threshold (decisionRAMWork R cost ops threshold) L A ≤
      Q * (64*P^3*T) := by
    apply hOracle.trans
    gcongr
  have hPoly : (Q+1) * (80*P^3*T) ≤ 256*P^4*T := by
    have hh := Nat.mul_le_mul_right (80*P^3*T) hQ
    nlinarith [Nat.zero_le (P^4*T)]
  change 16*(M+1)^3 + _ + _ ≤ 256*P^4*T
  calc
    _ ≤ (Q+1) * (80*P^3*T) := by nlinarith
    _ ≤ _ := hPoly

end IndependentSetDiscovery.Algorithms
