import IndependentSetDiscovery.Algorithms.EagerCompleteBounds
import IndependentSetDiscovery.Algorithms.EagerExecutionInvariant
import IndependentSetDiscovery.Algorithms.PreprocessingBits
import IndependentSetDiscovery.Algorithms.CappedThreshold
import IndependentSetDiscovery.Algorithms.EncodedInput

/-!
# Certified binary-scalar work of the concrete eager optimizer

## Cost model

We use a conservative binary-cost, finite-table RAM/list model. The measured
program's scalar instructions are implemented with padded `W`-bit registers.
One list-cell/control instruction, bounded table lookup, integer arithmetic,
or rational comparison/addition/subtraction/normalization is charged
`64*(W+1)^3` bit operations. This is a deliberately uniform upper tariff for
schoolbook multiplication/division and Euclidean normalization. The primitive
operation tariff is part of the declared model, not a theorem about Lean's VM
or compiler. The existing measured counters are ghost costs; computing and
printing those counters is not part of the optimization algorithm.

Unlike charging an arbitrary state-size expression, this translation rescales
the concrete measured instruction projection of `optimizeEagerComplete`.
`EagerOperandCertificate` proves that its actual eager query/execution traces,
including inactive row scans, and all preprocessing/fold intermediates fit the
padded registers. Thresholds are an already prepared finite table with entries
at most `n+1`; parameter-table preparation is charged separately. Arbitrary
semantic cost or compatibility functions do not receive a runtime guarantee:
the final encoded instantiation uses their explicit finite input tables.
-/
namespace IndependentSetDiscovery.Algorithms

open Finset

/-- Uniform binary tariff for one scalar/list/table instruction of the
explicit padded-register model. -/
def binaryScalarTariff (W : ℕ) : ℕ := 64 * (W+1)^3

/-- A generous polynomial register width, including optional parameter-input
bits. The square leaves ample room for finite indices and loop arithmetic. -/
def binaryRegisterWidth (S k n parameterBits : ℕ) : ℕ :=
  32 * (S+k+n+parameterBits+1)^2

theorem binaryRegisterWidth_large (S k n P : ℕ) :
    8*S + 2*k + 2*n + 16 ≤ binaryRegisterWidth S k n P := by
  have h : 1 ≤ S+k+n+P+1 := by omega
  have hs : S+k+n+P+1 ≤ (S+k+n+P+1)^2 := by nlinarith
  unfold binaryRegisterWidth
  nlinarith

theorem binaryLength_le_succ (m : ℕ) : binaryLength m ≤ m+1 :=
  binaryLength_le_of_le_pow Nat.lt_two_pow_self.le

variable {k n : ℕ} [Inhabited (Fin n)]
variable (R : Fin n → Fin n → Prop) [DecidableRel R] (cost : Fin k → Fin n → ℚ)

/-- A certificate for every numerical family actually used by measured
preprocessing, binary search, eager node construction and witness probing.
The arbitrary subsets cover every partially evaluated sorted fold. -/
structure EagerOperandCertificate (threshold : ℕ → ℕ)
    (rows : Vector (Finset (Fin n)) k) (W : ℕ) : Prop where
  denominator : ∀ K : Finset (Σ _ : Fin k, Fin n),
    K ⊆ Finset.univ.sigma (fun i => rows[i]) →
    binaryLength (∏ p ∈ K, (cost p.1 p.2).den) ≤ W
  scaledMaxima : ∀ (J : Finset (Fin k)) (P : Fin k → Finset (Fin n)),
    (∀ i ∈ J, P i ⊆ rows[i]) →
    binaryLength (∑ i ∈ J, (P i).sup (scaledCosts Finset.univ (fun i => rows[i]) cost i)) ≤ W
  scaling : ∀ i v, v ∈ rows[i] →
    binaryLength (cost i v).num.toNat ≤ W ∧ binaryLength (cost i v).den ≤ W ∧
    binaryLength (commonDenominator Finset.univ (fun j => rows[j]) cost / (cost i v).den) ≤ W ∧
    binaryLength (scaleCost (commonDenominator Finset.univ (fun j => rows[j]) cost) (cost i v)) ≤ W
  budget : ∀ s ∈ optimizeEagerExecutionTrace R cost threshold Finset.univ rows,
    rationalBits s.budget ≤ W
  rowCost : ∀ s ∈ optimizeEagerExecutionTrace R cost threshold Finset.univ rows,
    ∀ i v, v ∈ s.rows[i] → rationalBits (cost i v) ≤ W
  rowPrefix : ∀ s ∈ optimizeEagerExecutionTrace R cost threshold Finset.univ rows,
    ∀ i t, rationalBits (measuredPrefix (cost i) (s.rows[i]) t).2.1 ≤ W
  prefixSum : ∀ s ∈ optimizeEagerExecutionTrace R cost threshold Finset.univ rows,
    ∀ (J : Finset (Fin k)), J ⊆ s.labels → ∀ (P : Fin k → Finset (Fin n)),
      (∀ i ∈ J, P i ⊆ s.rows[i]) → rationalBits (∑ i ∈ J, prefixMax (cost i) (P i)) ≤ W
  childBudget : ∀ s ∈ optimizeEagerExecutionTrace R cost threshold Finset.univ rows,
    ∀ i ∈ s.labels, ∀ v ∈ s.rows[i], rationalBits (s.budget-cost i v) ≤ W
  midpoint : ∀ lo hi,
    lo ≤ upperBudget Finset.univ (fun i => rows[i]) (scaledCosts Finset.univ (fun i => rows[i]) cost) →
    hi ≤ upperBudget Finset.univ (fun i => rows[i]) (scaledCosts Finset.univ (fun i => rows[i]) cost) →
    binaryLength (lo+hi) ≤ W ∧ binaryLength ((lo+hi)/2) ≤ W
  thresholdWord : ∀ r ≤ k, binaryLength (threshold r) ≤ W
  indices : binaryLength k + binaryLength n ≤ W
  rationalTemporaries : ∀ p q : ℚ,
    rationalBits p ≤ 4*numericSize Finset.univ (fun i => rows[i]) cost+2 →
    rationalBits q ≤ 4*numericSize Finset.univ (fun i => rows[i]) cost+2 →
    binaryLength (p.num*(q.den : ℤ)).natAbs ≤ W ∧
    binaryLength (q.num*(p.den : ℤ)).natAbs ≤ W ∧
    binaryLength (p.num*(q.den : ℤ)-q.num*(p.den : ℤ)).natAbs ≤ W ∧
    binaryLength (p.num*(q.den : ℤ)+q.num*(p.den : ℤ)).natAbs ≤ W ∧
    binaryLength (p.den*q.den) ≤ W

/-- Every actual arithmetic operand family fits the selected fixed width.
No feasibility premise is used, so failed probes and negative budgets count. -/
theorem eagerOperandCertificate (nonneg : ∀ i v, 0 ≤ cost i v)
    (threshold : ℕ → ℕ) (rows : Vector (Finset (Fin n)) k)
    (ht : ∀ r ≤ k, threshold r ≤ n+1) (parameterBits : ℕ) :
    EagerOperandCertificate R cost threshold rows
      (binaryRegisterWidth (numericSize Finset.univ (fun i => rows[i]) cost) k n parameterBits) := by
  let S := numericSize Finset.univ (fun i => rows[i]) cost
  have hW := binaryRegisterWidth_large S k n parameterBits
  dsimp only [S] at hW
  constructor
  · intro K hK
    have h := denominator_partial_product_bits Finset.univ (fun i => rows[i]) cost K hK
    change _ ≤ S+1 at h
    omega
  · intro J P hP
    have h := scaled_partial_maxima_sum_bits Finset.univ J (fun i => rows[i]) P cost
      (Finset.subset_univ _) hP
    change _ ≤ 3*S+1 at h
    omega
  · intro i v hv
    have h := scaleCost_intermediate_bits Finset.univ (fun i => rows[i]) cost i (Finset.mem_univ _) v hv
    change _ ≤ S+1 ∧ _ ≤ S+1 ∧ _ ≤ S+1 ∧ _ ≤ 2*S+1 at h
    omega
  · intro s hs
    have h := (optimizeEagerExecutionTrace_operands_bits R cost threshold nonneg Finset.univ rows s hs).1
    change _ ≤ 4*S+2 at h
    omega
  · intro s hs i v hv
    have h := optimizeEagerExecutionTrace_allRow_bits R cost threshold rows s hs i v hv
    change _ ≤ S at h
    omega
  · intro s hs i t
    have h := optimizeEagerExecutionTrace_allPrefix_bits R cost threshold rows s hs i t
    change _ ≤ 4*S+2 at h
    omega
  · intro s hs J hJ P hP
    rcases optimizeEagerExecutionTrace_invariant R cost threshold Finset.univ rows s hs with ⟨b, hb, hs⟩
    have h := residualInvariant_prefixSum_bits cost nonneg hs J hJ P hP
    change _ ≤ 4*S+2 at h
    omega
  · intro s hs i hi v hv
    have h := (optimizeEagerExecutionTrace_operands_bits R cost threshold nonneg Finset.univ rows s hs).2.2.2 i hi v hv
    change _ ≤ 4*S+2 at h
    omega
  · intro lo hi hlo hhi
    have h := optimization_midpoint_temporary_bits cost Finset.univ (fun i => rows[i]) lo hi hlo hhi
    change _ ≤ 3*S+2 ∧ _ ≤ 3*S+2 at h
    omega
  · intro r hr
    have h := (binaryLength_mono (ht r hr)).trans (binaryLength_le_succ (n+1))
    omega
  · have hk := binaryLength_le_succ k
    have hn := binaryLength_le_succ n
    omega
  · intro p q hp hq
    have h := rational_arithmetic_intermediates p q
    have ha := rational_addition_intermediates p q
    change _ ≤ 4*S+2 at hp hq
    omega

/-- Binary realization of the concrete measured complete optimizer in the
specified padded-register model. The first projection is unchanged; the second
charges every actual measured instruction at the uniform scalar bit tariff. -/
def optimizeEagerBinary (table : Vector ℕ (k+1)) (parameterBits : ℕ)
    (rows : Vector (Finset (Fin n)) k) : Option (Fin k → Fin n) × ℕ :=
  let result := optimizeEagerComplete R cost (cachedThreshold table) Finset.univ rows
  let W := binaryRegisterWidth (numericSize Finset.univ (fun i => rows[i]) cost) k n parameterBits
  (result.1, result.2 * binaryScalarTariff W)

theorem optimizeEagerBinary_refinement (table : Vector ℕ (k+1)) (parameterBits : ℕ)
    (rows : Vector (Finset (Fin n)) k) :
    (optimizeEagerBinary R cost table parameterBits rows).1 =
      optimize R cost costPrefixOperations (cachedThreshold table) Finset.univ (fun i => rows[i]) :=
  optimizeEagerComplete_refinement R cost _ _ _

theorem cachedThreshold_le (table : Vector ℕ (k+1)) (M : ℕ)
    (h : ∀ r : Fin (k+1), table[r] ≤ M) (r : ℕ) (hr : r ≤ k) :
    cachedThreshold table r ≤ M := by
  unfold cachedThreshold
  rw [dif_pos (by omega)]
  exact h _

/-- Full measured optimization bit tariff: a fixed polynomial in original
numeric bits and finite indices, times the actual bounded search-tree factor. -/
theorem optimizeEagerBinary_cost_le (table : Vector ℕ (k+1)) (parameterBits : ℕ)
    (rows : Vector (Finset (Fin n)) k) (maxThreshold : ℕ)
    (hthreshold : ∀ r : Fin (k+1), table[r] ≤ maxThreshold) :
    let S := numericSize Finset.univ (fun i => rows[i]) cost
    (optimizeEagerBinary R cost table parameterBits rows).2 ≤
      ((6*S+6+(k+1)*(n+1))*128*(k+1)^2*(n+1)^2 *
        binaryScalarTariff (binaryRegisterWidth S k n parameterBits)) *
      treeBound (k*maxThreshold) k := by
  have h := optimizeEagerComplete_cost_le R cost (cachedThreshold table) maxThreshold
    (cachedThreshold_le table maxThreshold hthreshold) Finset.univ rows
  dsimp only [optimizeEagerBinary]
  apply (Nat.mul_le_mul_right _ h).trans
  exact le_of_eq (by ring)

/-- The bit-work bound is paired with a proof that the actual execution is
valid at the stated register width, rather than an isolated assigned bill. -/
theorem optimizeEagerBinary_certified (nonneg : ∀ i v, 0 ≤ cost i v)
    (table : Vector ℕ (k+1)) (parameterBits : ℕ) (rows : Vector (Finset (Fin n)) k)
    (hcap : ∀ r : Fin (k+1), table[r] ≤ n+1) (maxThreshold : ℕ)
    (hthreshold : ∀ r : Fin (k+1), table[r] ≤ maxThreshold) :
    let S := numericSize Finset.univ (fun i => rows[i]) cost
    EagerOperandCertificate R cost (cachedThreshold table) rows (binaryRegisterWidth S k n parameterBits) ∧
    (optimizeEagerBinary R cost table parameterBits rows).2 ≤
      ((6*S+6+(k+1)*(n+1))*128*(k+1)^2*(n+1)^2 *
        binaryScalarTariff (binaryRegisterWidth S k n parameterBits)) *
      treeBound (k*maxThreshold) k :=
  ⟨eagerOperandCertificate R cost nonneg _ rows (cachedThreshold_le table _ hcap) parameterBits,
    optimizeEagerBinary_cost_le R cost table parameterBits rows maxThreshold hthreshold⟩

/-- The complete program's query trace, with its measured preprocessing and
extra budget-division charges retained in the control expressions. -/
def optimizeEagerCompleteQueries (threshold : ℕ → ℕ)
    (L : Finset (Fin k)) (rows : Vector (Finset (Fin n)) k) : List (EagerState k n) :=
  let prep := prepareMeasured cost L rows
  let initial := fun b : ℕ => EagerState.mk L rows ((b : ℚ) / prep.1.1)
  let oracle := eagerDecide R cost threshold
  let p := fun b => let ans := oracle (initial b); (ans.1, ans.2+1)
  (leastBudgetQueries (fun b => (p b).1) prep.1.2).map initial ++
    match (leastBudgetMeasured p prep.1.2).1 with
    | none => []
    | some b => recoverMeasuredQueries R cost oracle L.card (initial b)

theorem optimizeEagerCompleteQueries_refinement (threshold : ℕ → ℕ)
    (L : Finset (Fin k)) (rows : Vector (Finset (Fin n)) k) :
    optimizeEagerCompleteQueries R cost threshold L rows = optimizeEagerQueries R cost threshold L rows := by
  unfold optimizeEagerCompleteQueries optimizeEagerQueries
  dsimp only
  rw [prepareMeasured_value]
  simp only [leastBudgetMeasured_value]
  rfl

/-- Consequently the earlier operand certificate covers the exact complete
program's decision expansions as well as its explicit preprocessing fields. -/
theorem optimizeEagerComplete_trace_refinement (threshold : ℕ → ℕ)
    (L : Finset (Fin k)) (rows : Vector (Finset (Fin n)) k) :
    ((optimizeEagerCompleteQueries R cost threshold L rows).flatMap fun s =>
      runTrace (eagerStep R cost threshold) s.labels.card s) =
      optimizeEagerExecutionTrace R cost threshold L rows := by
  rw [optimizeEagerCompleteQueries_refinement]
  rfl

/-- Remainder reduction, including all Euclidean normalization intermediates,
cannot increase either input's unsigned integer width. -/
theorem remainder_bits_le (a b : ℕ) : binaryLength (a % b) ≤ binaryLength a :=
  binaryLength_mono (Nat.mod_le _ _)

/-- Bound on a normalization gcd. Its second argument is a positive rational
product denominator, and all subsequent Euclidean remainders are smaller. -/
theorem normalization_gcd_bits_le (z D : ℕ) (hD : 0 < D) :
    binaryLength (Nat.gcd z D) ≤ binaryLength D :=
  binaryLength_mono (Nat.le_of_dvd hD (Nat.gcd_dvd_right _ _))

theorem binaryRegisterWidth_linear (S k n P : ℕ) :
    16*(S+k+n+P+1) ≤ binaryRegisterWidth S k n P := by
  have hx : 1 ≤ S+k+n+P+1 := by omega
  unfold binaryRegisterWidth
  nlinarith

/-- Numerical safety of the concrete saturated threshold generators. Raw
binary parameters are read before clamping; they are included explicitly.
All repeated arithmetic is performed on saturated words and rank bases. -/
structure ThresholdOperandCertificate (k n parameterBits W : ℕ) : Prop where
  parameter : ∀ p, binaryLength p ≤ parameterBits → binaryLength p ≤ W
  predecessor : ∀ p, binaryLength p ≤ parameterBits → binaryLength (p-1) ≤ W
  rankBase : ∀ r ≤ k, binaryLength (4*(max 2 r-1)) ≤ W ∧ binaryLength (8*(r-1)) ≤ W
  saturatedSum : ∀ x y, binaryLength (min (n+1) x + min (n+1) y) ≤ W
  saturatedProduct : ∀ x y, binaryLength (min (n+1) x * min (n+1) y) ≤ W
  boundedExponent : ∀ e, binaryLength (min e (n+1)) ≤ W

theorem thresholdOperandCertificate (S k n P : ℕ) :
    ThresholdOperandCertificate k n P (binaryRegisterWidth S k n P) := by
  have hW := binaryRegisterWidth_linear S k n P
  have hlarge := binaryRegisterWidth_large S k n P
  constructor
  · intro p hp
    omega
  · intro p hp
    have h := binaryLength_mono (Nat.sub_le p 1)
    omega
  · intro r hr
    have h₁ := binaryLength_le_succ (4*(max 2 r-1))
    have h₂ := binaryLength_le_succ (8*(r-1))
    omega
  · intro x y
    have hx := Nat.min_le_left (n+1) x
    have hy := Nat.min_le_left (n+1) y
    have h := binaryLength_le_succ (min (n+1) x + min (n+1) y)
    omega
  · intro x y
    have hprod := ThresholdPreparation.powLoop_product_le (n+1) x y
    have hbits := binaryLength_le_succ (min (n+1) x * min (n+1) y)
    have hsq : (n+1)^2 ≤ (S+k+n+P+1)^2 := by gcongr; omega
    unfold binaryRegisterWidth
    nlinarith
  · intro e
    have h := (binaryLength_mono (Nat.min_le_right e (n+1))).trans (binaryLength_le_succ (n+1))
    omega

omit [Inhabited (Fin n)]
namespace EncodedInput

variable (E : EncodedInput k n)

/-- Scalar polynomial for the boundary-complete encoded balanced solver.
It includes candidate incidence scans, bounded threshold-table preparation,
and expansion of abstract cost/compatibility queries into actual table reads. -/
def scalarWorkPolynomial (B k n : ℕ) : ℕ :=
  (k+1)*(12*(n+1)+38) + 5*k*(n+1) + k*(k+2) + 2 +
    8*((6*B+6+(k+1)*(n+1))*128*(k+1)^2*(n+1)^2)

 theorem scalarWorkPolynomial_two_le (B k n : ℕ) : 2 ≤ scalarWorkPolynomial B k n := by
  unfold scalarWorkPolynomial
  omega

theorem runPrepared_cost_inputBits [NeZero n] (table : Vector ℕ (k+1))
    (M : ℕ) (hM : ∀ r : Fin (k+1), table[r] ≤ M) :
    (E.runPrepared table).2 ≤ 5*k*(n+1) + k*(k+2) +
      8*((6*E.inputBits+6+(k+1)*(n+1))*128*(k+1)^2*(n+1)^2) * treeBound (k*M) k := by
  have hS : numericSize Finset.univ (fun i => E.candidateTable[i]) E.normalizedCost ≤ E.inputBits :=
    E.normalized_numericSize_le
  have hc := optimizeEagerComplete_cost_le (Compatible E.graph) E.normalizedCost
    (cachedThreshold table) M (cachedThreshold_le table M hM) Finset.univ E.candidateTable
  have hc' : (optimizeEagerComplete (Compatible E.graph) E.normalizedCost
      (cachedThreshold table) Finset.univ E.candidateTable).2 ≤
      (6*E.inputBits+6+(k+1)*(n+1))*128*(k+1)^2*(n+1)^2 * treeBound (k*M) k := by
    calc
      _ ≤ (6*E.inputBits+6+(k+1)*(n+1))*(128*(k+1)^2*(n+1)^2) * treeBound (k*M) k := by
        apply hc.trans
        gcongr
      _ = _ := by ring
  unfold runPrepared runPreparedVector
  dsimp only
  simp only [E.candidateTableCounted_value, E.candidateTableCounted_work]
  split_ifs <;> nlinarith

theorem solvePositiveMeasured_cost_inputBits [NeZero n] (d M : ℕ)
    (hM : ∀ r ≤ k, balancedSearchThreshold d r ≤ M) :
    (E.solvePositiveMeasured d).2 ≤ scalarWorkPolynomial E.inputBits k n * treeBound (k*M) k := by
  let table := (ThresholdPreparation.balancedTable k n d).1
  have ht : ∀ r : Fin (k+1), table[r] ≤ M := by
    intro r
    rw [(ThresholdPreparation.balancedTable_spec k n d).1 r]
    exact (Nat.min_le_right _ _).trans (hM r (by omega))
  have hr := E.runPrepared_cost_inputBits table M ht
  have hp := (ThresholdPreparation.balancedTable_spec k n d).2
  have hT := one_le_treeBound (k*M) k
  have hbase := Nat.mul_le_mul_left ((k+1)*(12*(n+1)+38)+5*k*(n+1)+k*(k+2)+2) hT
  unfold solvePositiveMeasured scalarWorkPolynomial
  dsimp only
  dsimp only [table] at hr
  nlinarith

/-- The actual total encoded counter, including both empty-input exits. -/
theorem solveMeasured_cost_inputBits (d M : ℕ)
    (hM : ∀ r ≤ k, balancedSearchThreshold d r ≤ M) :
    (E.solveMeasured d).2 ≤ scalarWorkPolynomial E.inputBits k n * treeBound (k*M) k := by
  have hpoly := scalarWorkPolynomial_two_le E.inputBits k n
  have hT := one_le_treeBound (k*M) k
  by_cases hk : k = 0
  · simp only [solveMeasured, dif_pos hk]
    nlinarith
  · by_cases hn : n = 0
    · simp only [solveMeasured, dif_neg hk, dif_pos hn]
      nlinarith
    · letI : NeZero n := ⟨hn⟩
      simp only [solveMeasured, dif_neg hk, dif_neg hn]
      exact E.solvePositiveMeasured_cost_inputBits d M hM

/-- Boundary-complete concrete encoded optimizer with binary-scalar cost.
The original binary parameter `d` is included, even though table arithmetic
is saturated. Cost counters remain ghost instrumentation in this model. -/
def solveBinary (d : ℕ) : Option (Fin k → Fin n) × ℕ :=
  let result := E.solveMeasured d
  (result.1, result.2 * binaryScalarTariff (binaryRegisterWidth E.inputBits k n (binaryLength d)))

@[simp] theorem solveBinary_value (d : ℕ) : (E.solveBinary d).1 = E.solve d := rfl

/-- Complete encoded bit-work bound under the declared binary primitive
model. Every factor outside `treeBound` is a fixed polynomial in input bits,
finite dimensions, and the binary parameter length. -/
theorem solveBinary_cost_le (d M : ℕ) (hM : ∀ r ≤ k, balancedSearchThreshold d r ≤ M) :
    (E.solveBinary d).2 ≤
      (scalarWorkPolynomial E.inputBits k n *
        binaryScalarTariff (binaryRegisterWidth E.inputBits k n (binaryLength d))) *
      treeBound (k*M) k := by
  have h := Nat.mul_le_mul_right
    (binaryScalarTariff (binaryRegisterWidth E.inputBits k n (binaryLength d)))
    (E.solveMeasured_cost_inputBits d M hM)
  exact h.trans (le_of_eq (by ring))

/-- Concrete table-lookups and all eager arithmetic are valid at the width
used by the final encoded binary solver. -/
theorem solveBinary_eagerCertificate [NeZero n] (d : ℕ) :
    EagerOperandCertificate (Compatible E.graph) E.normalizedCost
      (cachedThreshold (ThresholdPreparation.balancedTable k n d).1) E.candidateTable
      (binaryRegisterWidth E.inputBits k n (binaryLength d)) := by
  let S := numericSize Finset.univ (fun i => E.candidateTable[i]) E.normalizedCost
  have hS : S ≤ E.inputBits := E.normalized_numericSize_le
  have ht : ∀ r ≤ k,
      cachedThreshold (ThresholdPreparation.balancedTable k n d).1 r ≤ n+1 := by
    apply cachedThreshold_le
    intro r
    rw [(ThresholdPreparation.balancedTable_spec k n d).1 r]
    exact Nat.min_le_left _ _
  have h := eagerOperandCertificate (Compatible E.graph) E.normalizedCost
    E.normalizedCost_nonneg _ E.candidateTable ht (binaryLength d + (E.inputBits-S))
  have heq : S+k+n+(binaryLength d+(E.inputBits-S))+1 = E.inputBits+k+n+binaryLength d+1 := by omega
  change EagerOperandCertificate _ _ _ _ (32*(S+k+n+(binaryLength d+(E.inputBits-S))+1)^2) at h
  simpa only [heq, binaryRegisterWidth] using h

/-- The independently executed threshold preparation has its own operand
certificate, including original `d` and `d-1` before any saturation. -/
theorem solveBinary_thresholdCertificate (d : ℕ) :
    ThresholdOperandCertificate k n (binaryLength d)
      (binaryRegisterWidth E.inputBits k n (binaryLength d)) :=
  thresholdOperandCertificate E.inputBits k n (binaryLength d)

/-- Reusable binary-cost entrypoint for the other concrete prepared threshold
families. Their separately measured preparation work is added by the caller. -/
def runPreparedBinary [NeZero n] (table : Vector ℕ (k+1)) (parameterBits : ℕ) :
    Option (Fin k → Fin n) × ℕ :=
  let result := E.runPrepared table
  (result.1, result.2 * binaryScalarTariff (binaryRegisterWidth E.inputBits k n parameterBits))

theorem runPreparedBinary_cost_le [NeZero n] (table : Vector ℕ (k+1))
    (parameterBits M : ℕ) (hM : ∀ r : Fin (k+1), table[r] ≤ M) :
    (E.runPreparedBinary table parameterBits).2 ≤
      ((5*k*(n+1)+k*(k+2)+8*((6*E.inputBits+6+(k+1)*(n+1))*128*(k+1)^2*(n+1)^2)) *
        binaryScalarTariff (binaryRegisterWidth E.inputBits k n parameterBits)) *
      treeBound (k*M) k := by
  have h := E.runPrepared_cost_inputBits table M hM
  have hbase := Nat.mul_le_mul_left (5*k*(n+1)+k*(k+2)) (one_le_treeBound (k*M) k)
  have h' : (E.runPrepared table).2 ≤
      (5*k*(n+1)+k*(k+2)+8*((6*E.inputBits+6+(k+1)*(n+1))*128*(k+1)^2*(n+1)^2)) *
        treeBound (k*M) k := by nlinarith
  exact (Nat.mul_le_mul_right _ h').trans (le_of_eq (by ring))

theorem solveBinary_some {d : ℕ} (hd : 2 ≤ d) (hG : BicliqueFree E.graph d d)
    {x : Fin k → Fin n} (hx : (E.solveBinary d).1 = some x) : E.toWeightedInstance.Optimal x :=
  E.solve_some hd hG hx

theorem solveBinary_none_iff {d : ℕ} (hd : 2 ≤ d) (hG : BicliqueFree E.graph d d) :
    (E.solveBinary d).1 = none ↔ ¬∃ x, E.toWeightedInstance.Selection x :=
  E.solve_none_iff hd hG

/-- One paper-facing encoded statement pairs the actual return value, the
validity of both execution phases at the chosen width, and the bit-work bound. -/
theorem solveBinary_certified [NeZero n] (d M : ℕ)
    (hM : ∀ r ≤ k, balancedSearchThreshold d r ≤ M) :
    (E.solveBinary d).1 = E.solve d ∧
    EagerOperandCertificate (Compatible E.graph) E.normalizedCost
      (cachedThreshold (ThresholdPreparation.balancedTable k n d).1) E.candidateTable
      (binaryRegisterWidth E.inputBits k n (binaryLength d)) ∧
    ThresholdOperandCertificate k n (binaryLength d)
      (binaryRegisterWidth E.inputBits k n (binaryLength d)) ∧
    (E.solveBinary d).2 ≤
      (scalarWorkPolynomial E.inputBits k n *
        binaryScalarTariff (binaryRegisterWidth E.inputBits k n (binaryLength d))) *
      treeBound (k*M) k :=
  ⟨rfl, E.solveBinary_eagerCertificate d, E.solveBinary_thresholdCertificate d,
    E.solveBinary_cost_le d M hM⟩

end EncodedInput
end IndependentSetDiscovery.Algorithms
