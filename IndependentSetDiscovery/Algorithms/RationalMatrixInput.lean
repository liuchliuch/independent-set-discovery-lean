import IndependentSetDiscovery.Algorithms.WeightedMatrixInput
import IndependentSetDiscovery.Extensions.RationalMovement

/-!
# Materialized rational directed input and exact scalarization

A single common denominator is computed over the actual arcs, then both the
integerized weights and the lexicographically scalarized weights are materialized
as finite matrices. The bounds below control their encoding size in the original
rational input size; they do not assume unary weights.
-/
namespace IndependentSetDiscovery.WeightedDirected

open WeightedShortestPaths Algorithms Finset

structure RationalMatrixInput (n : ℕ) where
  adjacency : Vector (Vector Bool n) n
  weights : Vector (Vector ℚ n) n
  nonneg : ∀ u v : Fin n, adjacency[u][v] = true → 0 ≤ weights[u][v]

namespace RationalMatrixInput
variable {n : ℕ} (A : RationalMatrixInput n)

def relation (u v : Fin n) : Prop := A.adjacency[u][v] = true
instance : DecidableRel A.relation := fun _ _ => inferInstanceAs (Decidable (_ = true))
def weight (u v : Fin n) : ℚ := A.weights[u][v]

/-- Numerical encoding size includes every matrix entry and label framing. -/
def numericBits : ℕ := numericSize (univ : Finset (Fin n)) (fun _ => univ) A.weight

/-- One denominator computation, followed by materialization of the integer weights. -/
def integerMatrix : MatrixInput n :=
  let denominator := arcDenominator A.relation A.weight
  { adjacency := A.adjacency
    weights := Vector.ofFn (fun u => Vector.ofFn (fun v => scaleCost denominator (A.weight u v))) }

/-- Materialize the shared lexicographic scalarization `C*w+1`. -/
def scalarMatrix (C : ℕ) : MatrixInput n :=
  let integerized := A.integerMatrix
  { adjacency := integerized.adjacency
    weights := integerized.weights.map (fun row => row.map (fun z => C * z + 1)) }

@[simp] theorem integerMatrix_relation : A.integerMatrix.relation = A.relation := rfl
@[simp] theorem scalarMatrix_relation (C : ℕ) : (A.scalarMatrix C).relation = A.relation := rfl

@[simp] theorem integerMatrix_weight (u v : Fin n) :
    A.integerMatrix.weight u v = integerArcWeight A.relation A.weight u v := by
  simp [integerMatrix, MatrixInput.weight, integerArcWeight]

@[simp] theorem scalarMatrix_weight (C : ℕ) (u v : Fin n) :
    (A.scalarMatrix C).weight u v = C * integerArcWeight A.relation A.weight u v + 1 := by
  simp [scalarMatrix, MatrixInput.weight, integerMatrix, integerArcWeight]

theorem integerMatrix_weight_cast (u v : Fin n) (huv : A.relation u v) :
    (A.integerMatrix.weight u v : ℚ) = arcDenominator A.relation A.weight * A.weight u v := by
  rw [A.integerMatrix_weight]
  exact integerArcWeight_cast A.relation A.weight A.nonneg u v huv

theorem denominatorBits_le_numericBits :
    denominatorBits univ (arcCandidates A.relation) A.weight ≤ A.numericBits := by
  have hsub : denominatorBits univ (arcCandidates A.relation) A.weight ≤
      denominatorBits univ (fun _ : Fin n => univ) A.weight := by
    apply Finset.sum_le_sum
    intro u _
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro _ _ _
    exact Nat.zero_le _
  exact hsub.trans (denominatorBits_le_numericSize univ (fun _ => univ) A.weight)

theorem arcDenominator_le_numeric_pow :
    arcDenominator A.relation A.weight ≤ 2 ^ A.numericBits :=
  (arcDenominator_le_pow A.relation A.weight).trans
    (Nat.pow_le_pow_right (by decide) A.denominatorBits_le_numericBits)

/-- Every integerized arc entry occupies at most twice the original numeric size. -/
theorem integerMatrix_weight_le (u v : Fin n) : A.integerMatrix.weight u v ≤ 2 ^ (2 * A.numericBits) := by
  have hn : (A.weight u v).num.toNat ≤ (A.weight u v).num.natAbs := by
    have := Int.toNat_add_toNat_neg_eq_natAbs (A.weight u v).num
    omega
  have hnum : (A.weight u v).num.natAbs ≤ 2 ^ A.numericBits :=
    numerator_le_numeric_pow univ (fun _ => univ) A.weight u (mem_univ _) v (mem_univ _)
  have hdiv : arcDenominator A.relation A.weight / (A.weight u v).den ≤
      arcDenominator A.relation A.weight := Nat.div_le_self _ _
  rw [A.integerMatrix_weight]
  unfold integerArcWeight scaleCost
  calc
    _ ≤ 2 ^ A.numericBits * 2 ^ A.numericBits :=
      Nat.mul_le_mul (hn.trans hnum) (hdiv.trans A.arcDenominator_le_numeric_pow)
    _ = _ := by rw [← pow_add]; congr 1; omega

theorem scalarMatrix_weight_le (C : ℕ) (u v : Fin n) :
    (A.scalarMatrix C).weight u v ≤ 2 ^ (binaryLength C + 2 * A.numericBits + 1) := by
  have hC : C ≤ 2 ^ binaryLength C := (nat_lt_two_pow_bits C).le
  have hmain := Nat.mul_le_mul hC (A.integerMatrix_weight_le u v)
  have hp : 1 ≤ 2 ^ (binaryLength C + 2 * A.numericBits) := Nat.one_le_pow _ _ (by decide)
  rw [A.scalarMatrix_weight, ← A.integerMatrix_weight]
  calc
    _ ≤ 2 ^ binaryLength C * 2 ^ (2 * A.numericBits) + 1 := Nat.add_le_add_right hmain 1
    _ = 2 ^ (binaryLength C + 2 * A.numericBits) + 1 := by rw [pow_add]
    _ ≤ 2 ^ (binaryLength C + 2 * A.numericBits + 1) := by rw [pow_succ]; omega

theorem scalarMatrix_weight_binaryLength (C : ℕ) (u v : Fin n) :
    binaryLength ((A.scalarMatrix C).weight u v) ≤ binaryLength C + 2 * A.numericBits + 2 := by
  have h := binaryLength_le_of_le_pow (A.scalarMatrix_weight_le C u v)
  omega

/-- The whole scalarized natural matrix has polynomial bit length. -/
theorem scalarMatrix_numericBits (C : ℕ) :
    (A.scalarMatrix C).numericBits ≤ 1 + n ^ 2 * (binaryLength C + 2 * A.numericBits + 2) := by
  have hsum : (∑ p : Fin n × Fin n, binaryLength ((A.scalarMatrix C).weight p.1 p.2)) ≤
      n ^ 2 * (binaryLength C + 2 * A.numericBits + 2) := by
    calc
      _ ≤ ∑ _p : Fin n × Fin n, (binaryLength C + 2 * A.numericBits + 2) := by
        apply Finset.sum_le_sum
        intro p _
        exact A.scalarMatrix_weight_binaryLength C p.1 p.2
      _ = _ := by simp [Fintype.card_prod, pow_two]
  unfold MatrixInput.numericBits
  omega

/-- The shared scalar used for a token configuration has polynomial magnitude. -/
theorem scalarizationBase_le (S : Finset (Fin n)) : scalarizationBase S.card n ≤ n ^ 2 + 1 := by
  have hS : S.card ≤ n := by simpa using Finset.card_le_univ S
  have hsub : n - 1 ≤ n := Nat.sub_le _ _
  unfold scalarizationBase
  nlinarith only [Nat.mul_le_mul hS hsub]

theorem scalarizationBase_binaryLength (S : Finset (Fin n)) :
    binaryLength (scalarizationBase S.card n) ≤ n ^ 2 + 2 := by
  have h := Nat.log2_le_self (scalarizationBase S.card n)
  have hs := scalarizationBase_le S
  unfold binaryLength
  omega

theorem configuration_scalarMatrix_numericBits (S : Finset (Fin n)) :
    (A.scalarMatrix (scalarizationBase S.card n)).numericBits ≤
      1 + n ^ 2 * (n ^ 2 + 2 * A.numericBits + 4) := by
  apply (A.scalarMatrix_numericBits _).trans
  have hb := scalarizationBase_binaryLength S
  have hi : binaryLength (scalarizationBase S.card n) + 2 * A.numericBits + 2 ≤
      n ^ 2 + 2 * A.numericBits + 4 := by omega
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hi) 1

/-- Fully materialized rational-to-natural preprocessing, ready for the
executable cached two-graph weighted-transversal reduction. -/
def prepared (S : Finset (Fin n)) :
    PreparedRows (A.scalarMatrix (scalarizationBase S.card n)).relation
      (A.scalarMatrix (scalarizationBase S.card n)).weight :=
  (A.scalarMatrix (scalarizationBase S.card n)).prepared

/-- The bit tariff of weighted shortest-path preprocessing is polynomial in
original rational-input length, rather than in rational numerator values. -/
theorem scalar_preprocessBitWork_le (S : Finset (Fin n)) :
    (A.scalarMatrix (scalarizationBase S.card n)).preprocessBitWork ≤
      (4 * n + 3 * n ^ 2 + 5 * n ^ 3 + 24 * n ^ 4) *
        (n + (1 + n ^ 2 * (n ^ 2 + 2 * A.numericBits + 4)) + 2) ^ 2 := by
  apply (MatrixInput.preprocessBitWork_le _).trans
  gcongr
  exact A.configuration_scalarMatrix_numericBits S

end RationalMatrixInput
end IndependentSetDiscovery.WeightedDirected
