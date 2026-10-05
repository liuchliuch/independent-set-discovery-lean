import IndependentSetDiscovery.Algorithms.RationalMatrixInput
import IndependentSetDiscovery.Algorithms.MeasuredPreprocessing

/-!
# Single-pass measured preprocessing of rational directed matrices

The denominator is obtained by an actual counted finite fold. Each scalar
weight is constructed once in a stored vector, and all shortest-path rows
are likewise computed once. The returned counter comes from this driver.
-/
namespace IndependentSetDiscovery.WeightedDirected

open Algorithms WeightedShortestPaths Finset

local instance : Std.Commutative (fun a b : ℕ => a*b) := ⟨Nat.mul_comm⟩
local instance : Std.Associative (fun a b : ℕ => a*b) := ⟨Nat.mul_assoc⟩

namespace RationalMatrixInput
variable {n : ℕ} (A : RationalMatrixInput n)

/-- Conditional denominator of one explicitly represented arc. -/
def denominatorCell (p : Fin n × Fin n) : ℕ × ℕ :=
  (if A.relation p.1 p.2 then (A.weight p.1 p.2).den else 1, 4)

def denominatorRowMeasured (u : Fin n) : ℕ × ℕ :=
  foldMapMeasured (fun v => A.denominatorCell (u, v)) (· * ·) 1 univ

def denominatorMeasured : ℕ × ℕ :=
  foldMapMeasured (fun u =>
    let row := A.denominatorRowMeasured u
    (row.1, row.2 + 1)) (· * ·) 1 univ

theorem denominatorMeasured_value :
    A.denominatorMeasured.1 = arcDenominator A.relation A.weight := by
  simp only [denominatorMeasured, denominatorRowMeasured, foldMapMeasured_value,
    fold_mul_eq_prod, denominatorCell]
  simp [arcDenominator, commonDenominator, arcCandidates, Finset.prod_filter]

theorem denominatorMeasured_cost :
    A.denominatorMeasured.2 ≤ 32 * (n + 1) ^ 3 := by
  have hrow (u : Fin n) : (A.denominatorRowMeasured u).2 ≤ 4*n^2+6*n := by
    have h := foldMapMeasured_cost (fun v => A.denominatorCell (u,v)) (· * ·) 1 univ 4
      (by intro v hv; exact le_rfl)
    simp only [Finset.card_univ, Fintype.card_fin] at h
    change (A.denominatorRowMeasured u).2 ≤ _ at h
    omega
  have h := foldMapMeasured_cost (fun u =>
    let row := A.denominatorRowMeasured u
    (row.1, row.2 + 1)) (· * ·) 1 univ (4*n^2+6*n+1)
      (by intro u hu; exact Nat.add_le_add_right (hrow u) 1)
  simp only [Finset.card_univ, Fintype.card_fin] at h
  change A.denominatorMeasured.2 ≤ _ at h
  nlinarith only [h, Nat.zero_le (n^2), Nat.zero_le n]

/-- Every partial product in the denominator fold is bounded by the final
product, since each factor is a positive rational denominator or one. -/
theorem denominator_partial_le (T : Finset (Fin n × Fin n)) :
    (∏ p ∈ T, (A.denominatorCell p).1) ≤ arcDenominator A.relation A.weight := by
  have he : (∏ p : Fin n × Fin n, (A.denominatorCell p).1) =
      arcDenominator A.relation A.weight := by
    simp [Fintype.prod_prod_type, denominatorCell, arcDenominator,
      commonDenominator, arcCandidates, Finset.prod_filter]
  rw [← he]
  apply Finset.prod_le_prod_of_subset_of_one_le' (Finset.subset_univ _)
  intro p hp _
  simp only [denominatorCell]
  split_ifs
  · exact (A.weight p.1 p.2).pos
  · exact le_rfl

/-- Scalar entry construction performs fixed-count reads and exact integer
conversion, division, multiplication and addition on the already-read entry. -/
def scalarCellMeasured (denom C : ℕ) (u v : Fin n) : ℕ × ℕ :=
  (C * scaleCost denom (A.weight u v) + 1, 16)

/-- Materialize the scalar matrix and sum precisely the per-cell charges. -/
def scalarMatrixMeasured (C : ℕ) : MatrixInput n × ℕ :=
  let denominator := A.denominatorMeasured
  let cells := Vector.ofFn fun u => Vector.ofFn (A.scalarCellMeasured denominator.1 C u)
  let weights := cells.map fun row => row.map Prod.fst
  let matrix : MatrixInput n := ⟨A.adjacency, weights⟩
  (matrix, denominator.2 + 8*n +
    (cells.toList.map (fun row => 8*n + (row.toList.map Prod.snd).sum)).sum)

theorem scalarMatrixMeasured_value (C : ℕ) :
    (A.scalarMatrixMeasured C).1 = A.scalarMatrix C := by
  change MatrixInput.mk A.adjacency _ = MatrixInput.mk A.adjacency _
  congr 1
  ext u v
  simp [scalarMatrixMeasured, scalarMatrix, integerMatrix, scalarCellMeasured,
    A.denominatorMeasured_value, MatrixInput.weight]

theorem scalarMatrixMeasured_cost (C : ℕ) :
    (A.scalarMatrixMeasured C).2 ≤ 64*(n+1)^4 := by
  have hd := A.denominatorMeasured_cost
  simp only [scalarMatrixMeasured, Vector.toList_ofFn, List.map_ofFn, List.sum_ofFn,
    Function.comp_def, scalarCellMeasured, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  norm_cast
  nlinarith only [hd, Nat.zero_le (n^4), Nat.zero_le (n^3), Nat.zero_le (n^2), Nat.zero_le n]

/-- The measured matrix and measured Bellman--Ford rows form one actual
preparation pass. Transports below affect proofs only, not its runtime data. -/
def prepareMeasured (S : Finset (Fin n)) :
    PreparedRows A.relation (fun u v => scalarizationBase S.card n *
      integerArcWeight A.relation A.weight u v + 1) × ℕ := by
  let matrix := A.scalarMatrixMeasured (scalarizationBase S.card n)
  let computed := allPairs matrix.1.relation matrix.1.weight
  let rows : PreparedRows A.relation matrix.1.weight :=
    ⟨computed.1, allPairs_get matrix.1.relation matrix.1.weight⟩
  have he : matrix.1 = A.scalarMatrix (scalarizationBase S.card n) :=
    A.scalarMatrixMeasured_value _
  have hr : matrix.1.relation = A.relation := by rw [he]; rfl
  have hw : matrix.1.weight = (fun u v => scalarizationBase S.card n *
      integerArcWeight A.relation A.weight u v + 1) := by
    rw [he]
    funext u v
    exact A.scalarMatrix_weight _ u v
  exact ⟨hw ▸ rows, matrix.2 + computed.2 + 1⟩

/-- A single fixed polynomial for the actual preparation pass. -/
theorem prepareMeasured_polynomial (S : Finset (Fin n)) :
    (A.prepareMeasured S).2 ≤ 128 * (n + 1) ^ 4 := by
  have hs := A.scalarMatrixMeasured_cost (scalarizationBase S.card n)
  have hp := allPairs_cost
    (A.scalarMatrixMeasured (scalarizationBase S.card n)).1.relation
    (A.scalarMatrixMeasured (scalarizationBase S.card n)).1.weight
  change (A.scalarMatrixMeasured (scalarizationBase S.card n)).2 +
    (allPairs (A.scalarMatrixMeasured (scalarizationBase S.card n)).1.relation
      (A.scalarMatrixMeasured (scalarizationBase S.card n)).1.weight).2 + 1 ≤ _
  nlinarith only [hs, hp, Nat.zero_le (n^4), Nat.zero_le (n^3), Nat.zero_le (n^2), Nat.zero_le n]

/-- A numeric operand envelope including denominator partial products,
scalarized entries, and every shortest-path relaxation candidate. -/
def preprocessingBits : ℕ := n + 1 + n^2*(n^2 + 2*A.numericBits + 4) + 2

theorem preprocessingBits_pos : 0 < A.preprocessingBits := by unfold preprocessingBits; omega

/-- The conservative schoolbook bit tariff refines the counter of the same
measured preparation, rather than evaluating a separate reference algorithm. -/
def prepareBitWork (S : Finset (Fin n)) : ℕ :=
  (A.prepareMeasured S).2 * (A.preprocessingBits + 1)^2

theorem prepareBitWork_le (S : Finset (Fin n)) :
    A.prepareBitWork S ≤ 128*(n+1)^4*(A.preprocessingBits+1)^2 :=
  Nat.mul_le_mul_right _ (A.prepareMeasured_polynomial S)


/-- Integer entries are materialized once and retained for reconstruction. -/
def integerMatrixMeasured : MatrixInput n × ℕ :=
  let den := A.denominatorMeasured
  let weights := Vector.ofFn fun u => Vector.ofFn fun v => scaleCost den.1 (A.weight u v)
  (⟨A.adjacency, weights⟩, den.2 + 16*n^2 + 8*n + 1)

theorem integerMatrixMeasured_value : A.integerMatrixMeasured.1 = A.integerMatrix := by
  simp only [integerMatrixMeasured, integerMatrix, A.denominatorMeasured_value]

theorem integerMatrixMeasured_cost : A.integerMatrixMeasured.2 ≤ 64*(n+1)^4 := by
  have h := A.denominatorMeasured_cost
  change A.denominatorMeasured.2 + 16*n^2 + 8*n + 1 ≤ _
  nlinarith only [h, Nat.zero_le (n^4), Nat.zero_le (n^3), Nat.zero_le (n^2), Nat.zero_le n]

/-- The runtime bundle retains direct integer-weight lookup together with its
scalarized shortest rows. Equality proofs do not replace the stored matrix. -/
structure PreparedBundle (S : Finset (Fin n)) where
  integerMatrix : MatrixInput n
  weight_eq : integerMatrix.weight = integerArcWeight A.relation A.weight
  rows : PreparedRows A.relation (fun u v => scalarizationBase S.card n * integerMatrix.weight u v + 1)
  work : ℕ
  work_le : work ≤ 256*(n+1)^4

/-- Single-pass measured preparation retaining every table needed later.
The integer matrix is never reconstructed inside an arc-weight callback. -/
def prepareBundle (S : Finset (Fin n)) : A.PreparedBundle S := by
  let integerized := A.integerMatrixMeasured
  let C := scalarizationBase S.card n
  let scalar : MatrixInput n :=
    { adjacency := A.adjacency
      weights := integerized.1.weights.map (fun row => row.map (fun z => C*z+1)) }
  let computed := allPairs scalar.relation scalar.weight
  let rows : PreparedRows A.relation scalar.weight :=
    ⟨computed.1, allPairs_get scalar.relation scalar.weight⟩
  have hw : scalar.weight = (fun u v => C*integerized.1.weight u v+1) := by
    funext u v
    simp [scalar, MatrixInput.weight]
  refine
    { integerMatrix := integerized.1
      weight_eq := ?_
      rows := hw ▸ rows
      work := integerized.2 + 16*n^2+8*n+computed.2+1
      work_le := ?_ }
  · rw [A.integerMatrixMeasured_value]
    funext u v
    exact A.integerMatrix_weight u v
  · have hi := A.integerMatrixMeasured_cost
    have hs := allPairs_cost scalar.relation scalar.weight
    change integerized.2 ≤ _ at hi
    change computed.2 ≤ _ at hs
    nlinarith only [hi, hs, Nat.zero_le (n^4), Nat.zero_le (n^3), Nat.zero_le (n^2), Nat.zero_le n]

/-- The retained matrix preserves the rational arc weights exactly. -/
theorem PreparedBundle.scale {S : Finset (Fin n)} (P : A.PreparedBundle S)
    (u v : Fin n) (huv : A.relation u v) :
    (P.integerMatrix.weight u v : ℚ) = arcDenominator A.relation A.weight * A.weight u v := by
  rw [P.weight_eq]
  exact integerArcWeight_cast A.relation A.weight A.nonneg u v huv

/-- Semantic view of the cached rows; this transport changes no runtime data. -/
def PreparedBundle.semanticRows {S : Finset (Fin n)} (P : A.PreparedBundle S) :
    PreparedRows A.relation (fun u v => scalarizationBase S.card n *
      integerArcWeight A.relation A.weight u v+1) := by
  have h := P.rows
  rw [P.weight_eq] at h
  exact h

end RationalMatrixInput
end IndependentSetDiscovery.WeightedDirected
