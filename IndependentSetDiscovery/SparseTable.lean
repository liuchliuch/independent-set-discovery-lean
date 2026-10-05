import IndependentSetDiscovery.SparseTransfer
import IndependentSetDiscovery.Algorithms.EagerBitWork

/-!
# Lemma 5.1 with supplied finite threshold data

The input is a vector, not an executable threshold oracle. Only entries 2
through k are read; entries 0 and 1 are ignored. Preparation eagerly reads
and caps k+1 entries (terminal ranks reuse entry 2). Search then uses bounded
array lookups. The binary counter charges each raw threshold comparison by
its bit length before discarding the raw word. Consequently the search
register width contains no raw threshold-bit factor. All counters use the
explicit binary-scalar RAM/list model of `Algorithms.EagerBitWork`.
-/

namespace IndependentSetDiscovery.SparseTable

open Algorithms

variable {k n : ℕ}

/-- Semantic interpretation of the supplied finite input, only for proofs. -/
def threshold (L : Vector ℕ (k+1)) : ℕ → ℕ :=
  suppliedThreshold k (cachedThreshold L)

/-- The exact maximum over the ranks supplied in Lemma 5.1. -/
def maxThreshold (L : Vector ℕ (k+1)) : ℕ :=
  suppliedThresholdMax k (cachedThreshold L)

theorem threshold_eq (L : Vector ℕ (k+1)) (r : Fin (k+1)) (hr : 2 ≤ r.val) :
    threshold L r = L[r] := by
  rw [threshold, suppliedThreshold_eq _ hr (by omega)]
  simp [cachedThreshold, r.isLt]

theorem threshold_le_max (hk : 2 ≤ k) (L : Vector ℕ (k+1)) (r : ℕ) :
    threshold L r ≤ maxThreshold L :=
  suppliedThreshold_le_max hk (cachedThreshold L) r

theorem threshold_positive (hk : 2 ≤ k) (L : Vector ℕ (k+1))
    (positive : ∀ r : Fin (k+1), 2 ≤ r.val → 0 < L[r]) (r : ℕ) :
    0 < threshold L r := by
  apply suppliedThreshold_pos hk (cachedThreshold L)
  intro s hs hsk
  have hlt : s < k+1 := by omega
  simpa [cachedThreshold, hlt] using positive ⟨s,hlt⟩ hs

theorem maxThreshold_positive (hk : 2 ≤ k) (L : Vector ℕ (k+1))
    (positive : ∀ r : Fin (k+1), 2 ≤ r.val → 0 < L[r]) :
    1 ≤ maxThreshold L :=
  (threshold_positive hk L positive 2).trans_le (threshold_le_max hk L 2)

/-- A counted table callback: normalize rank, look up the supplied word, and
cap it. Eight scalar instructions cover the straight-line callback. -/
def prepareCell (n : ℕ) (L : Vector ℕ (k+1)) (r : Fin (k+1)) : ℕ × ℕ :=
  (min (n+1) (threshold L r), 8)

/-- Eager materialization, including four vector bookkeeping instructions per
entry. No callback survives in the returned vector. -/
def prepare (n : ℕ) (L : Vector ℕ (k+1)) : Vector ℕ (k+1) × ℕ :=
  let entries := Vector.ofFn (prepareCell n L)
  (entries.map Prod.fst, 4*(k+1) + (entries.toList.map Prod.snd).sum)

theorem prepare_value (n : ℕ) (L : Vector ℕ (k+1)) (r : Fin (k+1)) :
    (prepare n L).1[r] = min (n+1) (threshold L r) := by
  simp [prepare, prepareCell]

theorem prepare_work (n : ℕ) (L : Vector ℕ (k+1)) :
    (prepare n L).2 = 12*(k+1) := by
  simp [prepare, prepareCell, Vector.toList_ofFn, List.map_ofFn,
    Function.comp_def]
  ring

/-- Linear binary scanning/comparison of the raw supplied word. Only this
one-time phase sees its length; the result is already bounded by n+1. -/
def prepareCellBinary (n : ℕ) (L : Vector ℕ (k+1)) (r : Fin (k+1)) : ℕ × ℕ :=
  (min (n+1) (threshold L r),
    8*(binaryLength (threshold L r) + binaryLength (n+1) + binaryLength k + 1))

def prepareBinary (n : ℕ) (L : Vector ℕ (k+1)) : Vector ℕ (k+1) × ℕ :=
  let entries := Vector.ofFn (prepareCellBinary n L)
  (entries.map Prod.fst, 4*(k+1) + (entries.toList.map Prod.snd).sum)

theorem prepareBinary_value (n : ℕ) (L : Vector ℕ (k+1)) (r : Fin (k+1)) :
    (prepareBinary n L).1[r] = min (n+1) (threshold L r) := by
  simp [prepareBinary, prepareCellBinary]

theorem prepareBinary_table_eq (n : ℕ) (L : Vector ℕ (k+1)) :
    (prepareBinary n L).1 = (prepare n L).1 := by
  ext r hr
  simp [prepareBinary, prepare, prepareCellBinary, prepareCell]

theorem prepareBinary_cap (n : ℕ) (L : Vector ℕ (k+1)) (r : Fin (k+1)) :
    (prepareBinary n L).1[r] ≤ n+1 := by
  rw [prepareBinary_value]
  exact min_le_left _ _

theorem prepareBinary_max (hk : 2 ≤ k) (n : ℕ)
    (L : Vector ℕ (k+1)) (r : Fin (k+1)) :
    (prepareBinary n L).1[r] ≤ maxThreshold L := by
  rw [prepareBinary_value]
  exact (min_le_right _ _).trans (threshold_le_max hk L r)

/-- Raw threshold lengths are charged additively, never multiplied by the
number of search nodes. -/
theorem prepareBinary_work (n : ℕ) (L : Vector ℕ (k+1)) :
    (prepareBinary n L).2 = 4*(k+1) +
      ∑ r : Fin (k+1), 8*(binaryLength (threshold L r) +
        binaryLength (n+1) + binaryLength k + 1) := by
  simp only [prepareBinary, prepareCellBinary, Vector.toList_ofFn, List.map_ofFn,
    List.sum_ofFn, Function.comp_def]

theorem prepareBinary_work_le (hk : 2 ≤ k) (n : ℕ) (L : Vector ℕ (k+1)) :
    (prepareBinary n L).2 ≤
      4*(k+1) + 8*(k+1)*(maxThreshold L+n+k+5) := by
  have hs : ∀ r : Fin (k+1), binaryLength (threshold L r) ≤ maxThreshold L+1 := by
    intro r
    exact (binaryLength_le_succ _).trans (Nat.add_le_add_right (threshold_le_max hk L r) 1)
  have hn := binaryLength_le_succ (n+1)
  have hk' := binaryLength_le_succ k
  have hsum : (∑ r : Fin (k+1), 8*(binaryLength (threshold L r) +
      binaryLength (n+1) + binaryLength k + 1)) ≤
      ∑ _r : Fin (k+1), 8*(maxThreshold L+n+k+5) := by
    apply Finset.sum_le_sum
    intro r _
    have := hs r
    omega
  rw [prepareBinary_work]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  nlinarith

variable (E : EncodedInput k n)

/-- Fully concrete scalar-cost optimization, including finite preparation. -/
def solveMeasured (L : Vector ℕ (k+1)) : Option (Fin k → Fin n) × ℕ :=
  E.solveUsingPreparation (fun _ => prepare n L)

def solveMeasuredVector (L : Vector ℕ (k+1)) : Option (Vector (Fin n) k) × ℕ :=
  E.solveUsingPreparationVector (fun _ => prepare n L)

theorem solveMeasured_value (L : Vector ℕ (k+1)) :
    (solveMeasured E L).1 = E.solveWithThreshold (threshold L) :=
  E.solveUsingPreparation_value _ _ (prepare_value n L)

/-- Complete binary-cost driver. Raw words are scanned during preparation;
all search registers use parameterBits=0, independent of those raw words. -/
def solveBinary (L : Vector ℕ (k+1)) : Option (Fin k → Fin n) × ℕ :=
  if hk : k = 0 then (some (E.emptySelection hk), 1)
  else if hn : n = 0 then (none, 2)
  else
    letI : NeZero n := ⟨hn⟩
    let prep := prepareBinary n L
    let out := E.runPreparedBinary prep.1 0
    (out.1, prep.2 + out.2 + 2*binaryScalarTariff (binaryRegisterWidth E.inputBits k n 0))

theorem solveBinary_value (L : Vector ℕ (k+1)) :
    (solveBinary E L).1 = E.solveWithThreshold (threshold L) := by
  by_cases hk : k = 0
  · simp [solveBinary, EncodedInput.solveWithThreshold, hk]
  · by_cases hn : n = 0
    · simp [solveBinary, EncodedInput.solveWithThreshold, hk, hn]
    · letI : NeZero n := ⟨hn⟩
      simp only [solveBinary, EncodedInput.solveWithThreshold, dif_neg hk, dif_neg hn]
      exact (E.runPrepared_refinement (threshold L) _ (prepareBinary_value n L)).trans
        (E.solvePositiveWithThreshold_eq (threshold L)).symm

/-- The same binary execution exposes the stored finite witness directly. -/
def solveBinaryVector (L : Vector ℕ (k+1)) : Option (Vector (Fin n) k) × ℕ :=
  if hk : k = 0 then (some (Vector.ofFn (E.emptySelection hk)), 1)
  else if hn : n = 0 then (none, 2)
  else
    letI : NeZero n := ⟨hn⟩
    let prep := prepareBinary n L
    let out := E.runPreparedVector prep.1
    let tariff := binaryScalarTariff (binaryRegisterWidth E.inputBits k n 0)
    (out.1, prep.2 + out.2*tariff + 2*tariff)

theorem solveBinaryVector_value (L : Vector ℕ (k+1)) :
    EncodedInput.vectorFunctions (solveBinaryVector E L).1 = (solveBinary E L).1 := by
  unfold solveBinaryVector solveBinary
  split_ifs
  · simp [EncodedInput.vectorFunctions]
  · rfl
  · rfl

theorem solveBinaryVector_work (L : Vector ℕ (k+1)) :
    (solveBinaryVector E L).2 = (solveBinary E L).2 := by
  unfold solveBinaryVector solveBinary
  split_ifs <;> rfl

/-- Positivity is required only for the paper's supplied ranks. -/
def Positive (L : Vector ℕ (k+1)) : Prop :=
  ∀ r : Fin (k+1), 2 ≤ r.val → 0 < L[r]

/-- Normalized local ordered-pair sparsity, allowing overlapping sets. -/
def LocalBound (γ : ℕ → ℝ) : Prop :=
  ∀ t, 0 < t → ∀ U W : Finset (Fin n), U.card = t → W.card = t →
    ((adjacencyPairs E.graph U W).card : ℝ) ≤ γ t * (t : ℝ)^2

/-- Exactly inequality (10), only at ranks 2 through k. -/
def DensityCondition (L : Vector ℕ (k+1)) (γ : ℕ → ℝ) : Prop :=
  ∀ r : Fin (k+1), 2 ≤ r.val →
    4 * ((r.val-1 : ℕ) : ℝ) * (γ L[r] + 1 / (L[r] : ℝ)) < 1

theorem certificate [NeZero n] (hk : 2 ≤ k) (L : Vector ℕ (k+1)) (γ : ℕ → ℝ)
    (positive : Positive L) (hlocal : LocalBound E γ) (hdensity : DensityCondition L γ) :
    TransversalCertificate (ι := Fin k) (Compatible E.graph) (threshold L) := by
  have hp : ∀ r, 2 ≤ r → r ≤ k → 0 < cachedThreshold L r := by
    intro r hr hrk
    have hlt : r < k+1 := by omega
    simpa [cachedThreshold, hlt] using positive ⟨r,hlt⟩ hr
  have hd : ∀ r, 2 ≤ r → r ≤ k →
      4 * ((r-1 : ℕ) : ℝ) * (γ (cachedThreshold L r) + 1 / (cachedThreshold L r : ℝ)) < 1 := by
    intro r hr hrk
    have hlt : r < k+1 := by omega
    simpa [cachedThreshold, hlt] using hdensity ⟨r,hlt⟩ hr
  simpa only [Fintype.card_fin, threshold] using
    supplied_sparse_certificate (ι := Fin k) E.graph (by simpa using hk)
      (cachedThreshold L) γ (by simpa using hp) hlocal (by simpa using hd)

theorem solveBinary_some (hk : 2 ≤ k) (L : Vector ℕ (k+1)) (γ : ℕ → ℝ)
    (positive : Positive L) (hlocal : LocalBound E γ) (hdensity : DensityCondition L γ)
    {x : Fin k → Fin n} (hx : (solveBinary E L).1 = some x) :
    E.toWeightedInstance.Optimal x := by
  by_cases hn : n = 0
  · have hx' := (E.no_selection_of_no_vertices (by omega : k ≠ 0) hn)
    have hi := (x ⟨0, by omega⟩).isLt
    omega
  · letI : NeZero n := ⟨hn⟩
    rw [solveBinary_value] at hx
    exact E.solveWithThreshold_some (threshold_positive hk L positive)
      (certificate E hk L γ positive hlocal hdensity) hx

theorem solveBinary_none_iff (hk : 2 ≤ k) (L : Vector ℕ (k+1)) (γ : ℕ → ℝ)
    (positive : Positive L) (hlocal : LocalBound E γ) (hdensity : DensityCondition L γ) :
    (solveBinary E L).1 = none ↔ ¬∃ x, E.toWeightedInstance.Selection x := by
  by_cases hn : n = 0
  · have hs := E.no_selection_of_no_vertices (by omega : k ≠ 0) hn
    simp [solveBinary, show k ≠ 0 by omega, hn, hs]
  · letI : NeZero n := ⟨hn⟩
    rw [solveBinary_value]
    exact E.solveWithThreshold_none_iff (threshold_positive hk L positive)
      (certificate E hk L γ positive hlocal hdensity)

theorem solveBinaryVector_some (hk : 2 ≤ k) (L : Vector ℕ (k+1)) (γ : ℕ → ℝ)
    (positive : Positive L) (hlocal : LocalBound E γ) (hdensity : DensityCondition L γ)
    {targets : Vector (Fin n) k} (hx : (solveBinaryVector E L).1 = some targets) :
    E.toWeightedInstance.Optimal (fun i => targets[i]) := by
  apply solveBinary_some E hk L γ positive hlocal hdensity
  rw [← solveBinaryVector_value, hx]
  rfl

theorem solveBinaryVector_none_iff (hk : 2 ≤ k) (L : Vector ℕ (k+1)) (γ : ℕ → ℝ)
    (positive : Positive L) (hlocal : LocalBound E γ) (hdensity : DensityCondition L γ) :
    (solveBinaryVector E L).1 = none ↔ ¬∃ x, E.toWeightedInstance.Selection x := by
  rw [← solveBinary_none_iff E hk L γ positive hlocal hdensity,
    ← solveBinaryVector_value]
  simp [EncodedInput.vectorFunctions]

/-- Every operand of the actual capped search fits a fixed polynomial width
in the original weighted input; the supplied threshold words are excluded. -/
theorem search_operand_certificate [NeZero n] (L : Vector ℕ (k+1)) :
    EagerOperandCertificate (Compatible E.graph) E.normalizedCost
      (cachedThreshold (prepareBinary n L).1) E.candidateTable
      (binaryRegisterWidth E.inputBits k n 0) := by
  let S := numericSize Finset.univ (fun i => E.candidateTable[i]) E.normalizedCost
  have hS : S ≤ E.inputBits := E.normalized_numericSize_le
  have ht : ∀ r ≤ k, cachedThreshold (prepareBinary n L).1 r ≤ n+1 :=
    cachedThreshold_le _ _ (prepareBinary_cap n L)
  have h := eagerOperandCertificate (Compatible E.graph) E.normalizedCost
    E.normalizedCost_nonneg _ E.candidateTable ht (E.inputBits-S)
  have heq : S+k+n+(E.inputBits-S)+1 = E.inputBits+k+n+0+1 := by omega
  change EagerOperandCertificate _ _ _ _ (32*(S+k+n+(E.inputBits-S)+1)^2) at h
  simpa only [heq, binaryRegisterWidth] using h

/-- A fixed polynomial, with no supplied-threshold parameter. -/
def searchPolynomial (B k n : ℕ) : ℕ :=
  (5*k*(n+1)+k*(k+2)+8*((6*B+6+(k+1)*(n+1))*128*(k+1)^2*(n+1)^2)) *
    binaryScalarTariff (binaryRegisterWidth B k n 0)

def preparationPolynomial (k n : ℕ) : ℕ :=
  4*(k+1) + 8*(k+1)*(n+k+6)

/-- Explicit, fixed-degree original-input polynomial in Lemma 5.1. -/
def inputPolynomial (B k n : ℕ) : ℕ :=
  2*searchPolynomial B k n + preparationPolynomial k n +
    2*binaryScalarTariff (binaryRegisterWidth B k n 0)

theorem factor_bounds (hk : 2 ≤ k) (L : Vector ℕ (k+1)) (positive : Positive L) :
    1 ≤ (k*maxThreshold L)^k ∧ maxThreshold L ≤ (k*maxThreshold L)^k ∧
      treeBound (k*maxThreshold L) k ≤ 2*(k*maxThreshold L)^k := by
  have hM := maxThreshold_positive hk L positive
  have hb : 2 ≤ k*maxThreshold L := by nlinarith
  have h1 := Nat.one_le_pow k (k*maxThreshold L) (by omega)
  have hp : k*maxThreshold L ≤ (k*maxThreshold L)^k := by
    calc
      _ = (k*maxThreshold L)^1 := by simp
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
  have ht := treeBound_add_one_le (k*maxThreshold L) k hb
  exact ⟨h1, (by nlinarith), by omega⟩

theorem preparation_absorbed (hk : 2 ≤ k) (L : Vector ℕ (k+1)) (positive : Positive L) :
    (prepareBinary n L).2 ≤ preparationPolynomial k n * (k*maxThreshold L)^k := by
  rcases factor_bounds hk L positive with ⟨h1,hM,_⟩
  have hbase := Nat.mul_le_mul_right (n+k+5) h1
  have hsum : maxThreshold L+n+k+5 ≤ (n+k+6)*(k*maxThreshold L)^k := by
    nlinarith
  have hfirst := Nat.mul_le_mul_right (4*(k+1)) h1
  have hsecond := Nat.mul_le_mul_left (8*(k+1)) hsum
  have hprep := prepareBinary_work_le hk n L
  unfold preparationPolynomial
  nlinarith only [hfirst,hsecond,hprep]

/-- The actual binary counter, including the zero-vertex exit, has the exact
nonmonotone parameter factor stated in Lemma 5.1. -/
theorem solveBinary_cost_le (hk : 2 ≤ k) (L : Vector ℕ (k+1)) (positive : Positive L) :
    (solveBinary E L).2 ≤ (k*maxThreshold L)^k * inputPolynomial E.inputBits k n := by
  have hk0 : k ≠ 0 := by omega
  rcases factor_bounds hk L positive with ⟨h1,hM,ht⟩
  have htariff : 1 ≤ binaryScalarTariff (binaryRegisterWidth E.inputBits k n 0) := by
    unfold binaryScalarTariff
    have := Nat.one_le_pow 3 (binaryRegisterWidth E.inputBits k n 0+1) (by omega)
    omega
  by_cases hn : n = 0
  · simp only [solveBinary, dif_neg hk0, dif_pos hn]
    have hp : 2 ≤ inputPolynomial E.inputBits k n := by
      unfold inputPolynomial
      omega
    nlinarith only [hp, h1]
  · letI : NeZero n := ⟨hn⟩
    have hr := E.runPreparedBinary_cost_le (prepareBinary n L).1 0 (maxThreshold L)
      (prepareBinary_max hk n L)
    change _ ≤ searchPolynomial E.inputBits k n * treeBound (k*maxThreshold L) k at hr
    have hrun := hr.trans (Nat.mul_le_mul_left (searchPolynomial E.inputBits k n) ht)
    have hprep := preparation_absorbed (n := n) hk L positive
    have hcontrol := Nat.mul_le_mul_right
      (2*binaryScalarTariff (binaryRegisterWidth E.inputBits k n 0)) h1
    simp only [solveBinary, dif_neg hk0, dif_neg hn]
    unfold inputPolynomial
    nlinarith only [hrun,hprep,hcontrol]

theorem solveBinaryVector_cost_le (hk : 2 ≤ k) (L : Vector ℕ (k+1)) (positive : Positive L) :
    (solveBinaryVector E L).2 ≤ (k*maxThreshold L)^k * inputPolynomial E.inputBits k n := by
  rw [solveBinaryVector_work]
  exact solveBinary_cost_le E hk L positive

/-- The displayed polynomial has a uniform degree in the original weighted
input length alone. No length of a raw supplied threshold occurs here. -/
theorem inputPolynomial_le_power (B k n : ℕ) (hsize : k+n+1 ≤ B) :
    inputPolynomial B k n ≤ (26640*(64*129^3)+52)*B^12 := by
  have hB : 0 < B := by omega
  have hk : k+1 ≤ B := by omega
  have hn : n+1 ≤ B := by omega
  have hB2 : B ≤ B^2 := Nat.le_self_pow (by decide) B
  have h12 : 1 ≤ B^2 := Nat.one_le_pow _ _ hB
  have h26 : B^2 ≤ B^6 := Nat.pow_le_pow_right hB (by decide)
  have h212 : B^2 ≤ B^12 := Nat.pow_le_pow_right hB (by decide)
  have h612 : B^6 ≤ B^12 := Nat.pow_le_pow_right hB (by decide)
  have hwidth : binaryRegisterWidth B k n 0 ≤ 128*B^2 := by
    calc
      _ ≤ 32*(2*B)^2 := by unfold binaryRegisterWidth; gcongr; omega
      _ = _ := by ring
  have hwidth' : binaryRegisterWidth B k n 0+1 ≤ 129*B^2 := by omega
  have htariff : binaryScalarTariff (binaryRegisterWidth B k n 0) ≤ (64*129^3)*B^6 := by
    calc
      _ ≤ 64*(129*B^2)^3 := by unfold binaryScalarTariff; gcongr
      _ = _ := by ring
  have hprod : (k+1)*(n+1) ≤ B^2 := by
    calc
      _ ≤ B*B := Nat.mul_le_mul hk hn
      _ = _ := by ring
  have hcoeff : 6*B+6+(k+1)*(n+1) ≤ 13*B^2 := by omega
  have hlarge : 8*((6*B+6+(k+1)*(n+1))*128*(k+1)^2*(n+1)^2) ≤ 13312*B^6 := by
    calc
      _ ≤ 8*((13*B^2)*128*B^2*B^2) := by gcongr
      _ = _ := by ring
  have hsmall1 : 5*k*(n+1) ≤ 5*B^2 := by
    calc
      _ ≤ 5*B*B := by gcongr; omega
      _ = _ := by ring
  have hsmall2 : k*(k+2) ≤ 2*B^2 := by
    calc
      _ ≤ B*(2*B) := by gcongr <;> omega
      _ = _ := by ring
  have hscalar : 5*k*(n+1)+k*(k+2)+
      8*((6*B+6+(k+1)*(n+1))*128*(k+1)^2*(n+1)^2) ≤ 13319*B^6 := by omega
  have hsearch : searchPolynomial B k n ≤ (13319*(64*129^3))*B^12 := by
    calc
      _ ≤ (13319*B^6)*((64*129^3)*B^6) := Nat.mul_le_mul hscalar htariff
      _ = _ := by ring
  have hprep : preparationPolynomial k n ≤ 52*B^2 := by
    have hdim : n+k+6 ≤ 6*B := by omega
    have hmul : 8*(k+1)*(n+k+6) ≤ 48*B^2 := by
      calc
        _ ≤ 8*B*(6*B) := by gcongr
        _ = _ := by ring
    unfold preparationPolynomial
    omega
  unfold inputPolynomial
  nlinarith only [hsearch, hprep, htariff,
    Nat.mul_le_mul_left 52 h212, Nat.mul_le_mul_left (2*(64*129^3)) h612]

theorem solveBinaryVector_cost_inputBits (hk : 2 ≤ k)
    (L : Vector ℕ (k+1)) (positive : Positive L) :
    (solveBinaryVector E L).2 ≤
      (k*maxThreshold L)^k * (26640*(64*129^3)+52) * E.inputBits^12 := by
  have hsize : k+n+1 ≤ E.inputBits := by unfold EncodedInput.inputBits; omega
  calc
    _ ≤ (k*maxThreshold L)^k * inputPolynomial E.inputBits k n :=
      solveBinaryVector_cost_le E hk L positive
    _ ≤ (k*maxThreshold L)^k * ((26640*(64*129^3)+52)*E.inputBits^12) :=
      Nat.mul_le_mul_left _ (inputPolynomial_le_power E.inputBits k n hsize)
    _ = _ := by ring

/-- The budgeted yes-witness interface follows from the same computed global
optimum. The assignment is finite stored data, not an existential solver. -/
theorem solveBinaryVector_within_iff (hk : 2 ≤ k) (L : Vector ℕ (k+1)) (γ : ℕ → ℝ)
    (positive : Positive L) (hlocal : LocalBound E γ) (hdensity : DensityCondition L γ)
    (budget : ℚ) :
    (∃ targets, (solveBinaryVector E L).1 = some targets ∧
      E.toWeightedInstance.selectionCost (fun i => targets[i]) ≤ budget) ↔
      E.toWeightedInstance.Within budget := by
  constructor
  · rintro ⟨targets, ht, hb⟩
    exact ⟨_, (solveBinaryVector_some E hk L γ positive hlocal hdensity ht).1, hb⟩
  · rintro ⟨x, hx, hb⟩
    cases hresult : (solveBinaryVector E L).1 with
    | none =>
      exact False.elim ((solveBinaryVector_none_iff E hk L γ positive hlocal hdensity).mp
        hresult ⟨x,hx⟩)
    | some targets =>
      exact ⟨targets, rfl,
        ((solveBinaryVector_some E hk L γ positive hlocal hdensity hresult).2 x hx).trans hb⟩

/-- Lemma 5.1: a concrete supplied-vector optimizer, a globally optimal
finite witness or an exact impossibility report, and the total binary-work
bound. There is no monotonicity hypothesis on the supplied thresholds. -/
theorem lemma_5_1 (hk : 2 ≤ k) (L : Vector ℕ (k+1)) (γ : ℕ → ℝ)
    (positive : Positive L) (hlocal : LocalBound E γ) (hdensity : DensityCondition L γ) :
    (∀ targets, (solveBinaryVector E L).1 = some targets →
      E.toWeightedInstance.Optimal (fun i => targets[i])) ∧
    ((solveBinaryVector E L).1 = none ↔ ¬∃ x, E.toWeightedInstance.Selection x) ∧
    (solveBinaryVector E L).2 ≤ (k*maxThreshold L)^k * inputPolynomial E.inputBits k n :=
  ⟨fun _ => solveBinaryVector_some E hk L γ positive hlocal hdensity,
    solveBinaryVector_none_iff E hk L γ positive hlocal hdensity,
    solveBinaryVector_cost_le E hk L positive⟩

end IndependentSetDiscovery.SparseTable
