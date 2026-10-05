import IndependentSetDiscovery.Extensions.DirectedPreprocessing
import IndependentSetDiscovery.Algorithms.WeightedMeasuredEncoding
import IndependentSetDiscovery.Extensions.RationalDiscoveryAlgorithm
import IndependentSetDiscovery.Extensions.RetainedRationalReconstruction
import IndependentSetDiscovery.Extremal.Growth
import IndependentSetDiscovery.Algorithms.EncodedBounds

/-!
# Explicit directed weighted complexity composition

The finite rational matrix is converted by `prepareMeasured`, cached path
rows feed the encoded weighted optimizer, and returned paths are decoded
before the measured eager reconstruction. Numeric input-size bounds below
preserve polynomial dependence on binary rational arc weights.
-/
namespace IndependentSetDiscovery.WeightedDirected

open Algorithms WeightedShortestPaths Finset

namespace RationalMatrixInput
variable {n : ℕ} (A : RationalMatrixInput n)

/-- Scalarized arc scores and all shortest-path candidates fit this same
polynomial binary envelope for every correct cached table. -/
theorem prepared_score_bits (S : Finset (Fin n))
    (P : PreparedRows A.relation (fun u v => scalarizationBase S.card n *
      integerArcWeight A.relation A.weight u v + 1))
    (s v : Fin n) {p : Route n} (hp : P.entry s v = some p) :
    binaryLength p.score ≤ A.preprocessingBits := by
  let M := A.scalarMatrix (scalarizationBase S.card n)
  have he : M.weight = (fun u v => scalarizationBase S.card n *
      integerArcWeight A.relation A.weight u v + 1) := by
    funext u v
    exact A.scalarMatrix_weight _ u v
  have hs := P.row_sound s v hp
  have hv : Valid M.relation M.weight s v p := by
    rw [he]
    exact hs.1
  have h := MatrixInput.valid_score_binaryLength M hv (by omega)
  have hm := A.configuration_scalarMatrix_numericBits S
  change binaryLength p.score ≤ n + M.numericBits + 2 at h
  change M.numericBits ≤ _ at hm
  unfold preprocessingBits
  omega

theorem rationalBits_natCast (a : ℕ) : rationalBits (a : ℚ) = binaryLength a + 1 := by
  simp [rationalBits, binaryLength, show Nat.log2 1 = 0 by decide]

/-- The encoded weighted table contains only cached integer distances. -/
theorem encoded_cost_bits (S : Finset (Fin n))
    (P : PreparedRows A.relation (fun u v => scalarizationBase S.card n *
      integerArcWeight A.relation A.weight u v + 1))
    (a : ShortestPaths.MatrixGraph n) (i : Fin S.card) (v : Fin n) :
    rationalBits (P.encode a S).costs[i][v] ≤ A.preprocessingBits + 1 := by
  simp only [PreparedRows.encode, Fin.getElem_fin, Vector.getElem_ofFn]
  cases hp : P.entry (EncodedMovement.labelEquiv S i).val v with
  | none =>
    simp [rationalBits, show Nat.log2 1 = 0 by decide]
    have := A.preprocessingBits_pos
    omega
  | some p =>
    simp only [hp, rationalBits_natCast]
    exact Nat.add_le_add_right (A.prepared_score_bits S P _ _ hp) 1

/-- A fixed polynomial bound for the concrete encoded optimizer's input size. -/
def encodedBitsEnvelope : ℕ := 4 * (n + 1)^2 * (A.preprocessingBits + 2)

theorem encoded_inputBits_le (S : Finset (Fin n))
    (P : PreparedRows A.relation (fun u v => scalarizationBase S.card n *
      integerArcWeight A.relation A.weight u v + 1))
    (a : ShortestPaths.MatrixGraph n) :
    (P.encode a S).inputBits ≤ A.encodedBitsEnvelope := by
  have hS : S.card ≤ n := by simpa using Finset.card_le_univ S
  have hsum : (∑ i : Fin S.card, ∑ v : Fin n, rationalBits (P.encode a S).costs[i][v]) ≤
      S.card*n*(A.preprocessingBits+1) := by
    calc
      _ ≤ ∑ _i : Fin S.card, ∑ _v : Fin n, (A.preprocessingBits+1) := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro v _
        exact A.encoded_cost_bits S P a i v
      _ = _ := by simp; ring
  have hm := Nat.mul_le_mul_right (n*(A.preprocessingBits+1)) hS
  unfold EncodedInput.inputBits encodedBitsEnvelope
  nlinarith only [hsum, hm, hS, Nat.zero_le (n*A.preprocessingBits),
    Nat.zero_le (n^2*A.preprocessingBits), Nat.zero_le A.preprocessingBits,
    Nat.zero_le (n^2), Nat.zero_le n]

/-- Directed reconstruction uses at most `k(n-1)` slides, with its actual
plan-table work bounded by a universal graph-size polynomial. -/
theorem reconstructionWork_polynomial {Gf : SimpleGraph (Fin n)}
    {D : Fin n → Fin n → Prop} {w : Fin n → Fin n → ℚ} {S : Finset (Fin n)}
    (out : RationalDiscoveryResult Gf D w S) :
    out.reconstructionWork ≤ 64 * (n + 1)^5 := by
  have hS : S.card ≤ n := by simpa using Finset.card_le_univ S
  have hM : S.card*(n-1) ≤ n^2 := by
    simpa [pow_two] using Nat.mul_le_mul hS (Nat.sub_le n 1)
  have hA : S.card*(n-1)+1 ≤ (n+1)^2 := by nlinarith
  have hB : n+S.card*(n-1)+1 ≤ (n+1)^2 := by nlinarith
  have h := out.work_le
  simp only [Fintype.card_fin, reconstructionStepBudget] at h
  calc
    _ ≤ (S.card*(n-1)+1) * (64*(n+1)*(n+S.card*(n-1)+1)) := h
    _ ≤ (n+1)^2 * (64*(n+1)*(n+1)^2) := by gcongr
    _ = _ := by ring


/-- Bound for the counter returned by the eager selected-path cache. -/
theorem pathDecodingWork_polynomial {Gf : SimpleGraph (Fin n)}
    {D : Fin n → Fin n → Prop} {w : Fin n → Fin n → ℚ} {S : Finset (Fin n)}
    (out : RationalDiscoveryResult Gf D w S) :
    out.pathDecodingWork ≤ 96*(n+1)^3 := by
  have hS : S.card ≤ n := by simpa using Finset.card_le_univ S
  have h := out.pathDecodingWork_le
  simp only [Fintype.card_fin] at h
  have hm := Nat.mul_le_mul_right (2*n^2+24*n+24) hS
  nlinarith only [h, hm, Nat.zero_le (n^3), Nat.zero_le (n^2), Nat.zero_le n]

/-- The decoded cache and actual collision-free reconstruction are polynomial
independently of rational weight magnitudes. -/
theorem finishWork_polynomial {Gf : SimpleGraph (Fin n)}
    {D : Fin n → Fin n → Prop} {w : Fin n → Fin n → ℚ} {S : Finset (Fin n)}
    (out : RationalDiscoveryResult Gf D w S) :
    out.pathDecodingWork + out.reconstructionWork ≤ 160*(n+1)^5 := by
  have hp := pathDecodingWork_polynomial out
  have hr := reconstructionWork_polynomial out
  have hg : (n+1)^3 ≤ (n+1)^5 := Nat.pow_le_pow_right (by omega) (by omega)
  nlinarith only [hp, hr, Nat.mul_le_mul_left 96 hg]

/-- The actual finite-table encoding does not change the input-bit envelope. -/
theorem measured_encoded_inputBits_le (S : Finset (Fin n))
    (P : PreparedRows A.relation (fun u v => scalarizationBase S.card n *
      integerArcWeight A.relation A.weight u v + 1))
    (a : ShortestPaths.MatrixGraph n) :
    (P.encodeMeasured a S).1.inputBits ≤ A.encodedBitsEnvelope := by
  rw [P.encodeMeasured_value]
  exact A.encoded_inputBits_le S P a


/-- Transfer an optimal encoded vector to the decoded semantic selection. -/
theorem decodedVector_optimal (S : Finset (Fin n))
    (P : PreparedRows A.relation (fun u v => scalarizationBase S.card n *
      integerArcWeight A.relation A.weight u v + 1))
    (a : ShortestPaths.MatrixGraph n) (targets : Vector (Fin n) S.card)
    (ho : (P.encodeMeasured a S).1.toWeightedInstance.Optimal (fun i => targets[i])) :
    (movementInstance a.graph A.relation
      (fun u v => scalarizationBase S.card n * integerArcWeight A.relation A.weight u v + 1)
      S).Optimal (PreparedRows.decodeVectorMeasured S targets).1 := by
  rw [P.encodeMeasured_value, P.encode_eq_reindex] at ho
  have h := ((movementInstance a.graph A.relation
    (fun u v => scalarizationBase S.card n * integerArcWeight A.relation A.weight u v + 1)
    S).reindex_optimal (EncodedMovement.labelEquiv S) (fun i => targets[i])).mp ho
  have he : (PreparedRows.decodeVectorMeasured S targets).1 =
      (fun s => targets[(EncodedMovement.labelEquiv S).symm s]) := by
    funext s
    exact PreparedRows.decodeVectorMeasured_apply S targets s
  rwa [he]

/-- Reconstruction uses the retained integer matrix, not an integerization closure. -/
def reconstructVector [NeZero n] (a : ShortestPaths.MatrixGraph n) (S : Finset (Fin n))
    (Z : MatrixInput n) (hz : Z.weight = integerArcWeight A.relation A.weight)
    (P : PreparedRows A.relation (fun u v => scalarizationBase S.card n *
      integerArcWeight A.relation A.weight u v + 1))
    (targets : Vector (Fin n) S.card)
    (ho : (P.encodeMeasured a S).1.toWeightedInstance.Optimal (fun i => targets[i])) :
    RationalDiscoveryResult a.graph A.relation A.weight S := by
  apply reconstructScaledPreparedSelection a A.relation A.weight Z.weight
    (arcDenominator A.relation A.weight) (arcDenominator_pos A.relation A.weight)
    (by intro u v huv; rw [hz]; exact integerArcWeight_cast A.relation A.weight A.nonneg u v huv)
    S (by simpa only [hz] using P) (PreparedRows.decodeVectorMeasured S targets).1
  simpa only [hz] using A.decodedVector_optimal S P a targets ho

/-- Decoding and reconstruction consume actual stored output and weight vectors. -/
def finishVector [NeZero n] (a : ShortestPaths.MatrixGraph n) (S : Finset (Fin n))
    (Z : MatrixInput n) (hz : Z.weight = integerArcWeight A.relation A.weight)
    (P : PreparedRows A.relation (fun u v => scalarizationBase S.card n *
      integerArcWeight A.relation A.weight u v + 1))
    (targets : Vector (Fin n) S.card)
    (ho : (P.encodeMeasured a S).1.toWeightedInstance.Optimal (fun i => targets[i])) :
    RationalDiscoveryResult a.graph A.relation A.weight S × ℕ :=
  let decoded := PreparedRows.decodeVectorMeasured S targets
  let out := A.reconstructVector a S Z hz P targets ho
  (out, decoded.2 + out.pathDecodingWork + out.reconstructionWork + 1)

theorem finishVector_cost [NeZero n] (a : ShortestPaths.MatrixGraph n) (S : Finset (Fin n))
    (Z : MatrixInput n) (hz : Z.weight = integerArcWeight A.relation A.weight)
    (P : PreparedRows A.relation (fun u v => scalarizationBase S.card n *
      integerArcWeight A.relation A.weight u v + 1))
    (targets : Vector (Fin n) S.card)
    (ho : (P.encodeMeasured a S).1.toWeightedInstance.Optimal (fun i => targets[i])) :
    (A.finishVector a S Z hz P targets ho).2 ≤ 193*(n+1)^5 := by
  let out := A.reconstructVector a S Z hz P targets ho
  have hf := finishWork_polynomial out
  have hd := PreparedRows.decodeVectorMeasured_cost S targets
  have h35 : (n+1)^3 ≤ (n+1)^5 := Nat.pow_le_pow_right (by omega) (by omega)
  have h1 : 1 ≤ (n+1)^5 := Nat.one_le_pow _ _ (by omega)
  change (PreparedRows.decodeVectorMeasured S targets).2 + out.pathDecodingWork +
    out.reconstructionWork + 1 ≤ _
  nlinarith only [hf, hd, Nat.mul_le_mul_left 32 h35, h1]

/-- The actual efficient directed driver: all matrix preparation, encoded
search, decoded cache and reconstruction are executed once and charged.
The retained integer matrix supplies all reconstruction weight lookups. -/
def solveMeasured [NeZero n] (a : ShortestPaths.MatrixGraph n) (S : Finset (Fin n))
    (d : ℕ) (hd : 2 ≤ d) (hG : BicliqueFree a.graph d d) :
    Option (RationalDiscoveryResult a.graph A.relation A.weight S) × ℕ := by
  let prepared := A.prepareBundle S
  let P := prepared.semanticRows
  let encoded := P.encodeMeasured a S
  let result := encoded.1.solveMeasuredVector d
  match hr : result.1 with
  | none => exact ⟨none, prepared.work + encoded.2 + result.2 + 1⟩
  | some targets =>
    have ho : encoded.1.toWeightedInstance.Optimal (fun i => targets[i]) :=
      encoded.1.solveMeasuredVector_some hd hG hr
    let finished := A.finishVector a S prepared.integerMatrix prepared.weight_eq P targets ho
    exact ⟨some finished.1, prepared.work + encoded.2 + result.2 + finished.2⟩

/-- A universal polynomial in finite graph size and original rational bits. -/
def directedInputPolynomial (k : ℕ) : ℕ :=
  EncodedInput.measuredInputPolynomial k n A.encodedBitsEnvelope + 513*(n+1)^5

/-- Corollary 5.6's uniform FPT bound on the actual complete directed program.
The remaining factor is an explicit fixed polynomial in original binary input. -/
theorem solveMeasured_cost [NeZero n] (a : ShortestPaths.MatrixGraph n)
    (S : Finset (Fin n)) (d : ℕ) (hd : 2 ≤ d) (hk : 2 ≤ S.card)
    (hG : BicliqueFree a.graph d d) :
    (A.solveMeasured a S d hd hG).2 ≤
      2^(10*d*S.card*(S.card.log2+1)) * A.directedInputPolynomial S.card := by
  let prepared := A.prepareBundle S
  let P := prepared.semanticRows
  let encoded := P.encodeMeasured a S
  let result := encoded.1.solveMeasuredVector d
  let F := 2^(10*d*S.card*(S.card.log2+1))
  have hF : 1 ≤ F := Nat.one_le_pow _ _ (by decide)
  have hp := prepared.work_le
  have he := P.encodeMeasured_cost a S
  have hs := encoded.1.solveMeasuredVector_le_exp hd hk
  have hbits := A.measured_encoded_inputBits_le S P a
  have hpoly := EncodedInput.measuredInputPolynomial_mono S.card n hbits
  have hsearch : result.2 ≤ F*EncodedInput.measuredInputPolynomial S.card n A.encodedBitsEnvelope :=
    hs.trans (Nat.mul_le_mul_left F hpoly)
  have h45 : (n+1)^4 ≤ (n+1)^5 := Nat.pow_le_pow_right (by omega) (by omega)
  have h1 : 1 ≤ (n+1)^5 := Nat.one_le_pow _ _ (by omega)
  have hbase := Nat.mul_le_mul_right (513*(n+1)^5) hF
  unfold solveMeasured
  change (match hr : result.1 with
    | none => (none, prepared.work + encoded.2 + result.2 + 1)
    | some targets =>
      let ho := encoded.1.solveMeasuredVector_some hd hG hr
      let finished := A.finishVector a S prepared.integerMatrix prepared.weight_eq P targets ho
      (some finished.1, prepared.work + encoded.2 + result.2 + finished.2)).2 ≤ _
  split
  · dsimp only
    change _ ≤ F*(EncodedInput.measuredInputPolynomial S.card n A.encodedBitsEnvelope+513*(n+1)^5)
    nlinarith only [hp, he, hsearch, hbase, Nat.mul_le_mul_left 256 h45,
      Nat.mul_le_mul_left 64 h45, h1]
  · rename_i targets hr
    have hf := A.finishVector_cost a S prepared.integerMatrix prepared.weight_eq P targets
      (encoded.1.solveMeasuredVector_some hd hG hr)
    dsimp only
    change _ ≤ F*(EncodedInput.measuredInputPolynomial S.card n A.encodedBitsEnvelope+513*(n+1)^5)
    nlinarith only [hp, he, hf, hsearch, hbase, Nat.mul_le_mul_left 256 h45,
      Nat.mul_le_mul_left 64 h45]

/-- The reported solution and move list carry exact lexicographic optimality. -/
theorem solveMeasured_some [NeZero n] (a : ShortestPaths.MatrixGraph n)
    (S : Finset (Fin n)) (d : ℕ) (hd : 2 ≤ d) (hG : BicliqueFree a.graph d d)
    (out : RationalDiscoveryResult a.graph A.relation A.weight S)
    (_h : (A.solveMeasured a S d hd hG).1 = some out) :
    RationalLexOptimal a.graph A.relation A.weight S out.target
      (rationalMovesCost A.weight out.moves) out.moves.length := out.optimal


/-- Exact infeasibility reporting for the new retained-matrix measured driver. -/
theorem solveMeasured_none_iff [NeZero n] (a : ShortestPaths.MatrixGraph n)
    (S : Finset (Fin n)) (d : ℕ) (hd : 2 ≤ d) (hG : BicliqueFree a.graph d d) :
    (A.solveMeasured a S d hd hG).1 = none ↔
      ¬ ∃ T c k, Independent a.graph T ∧ RationalSlideSequence A.relation A.weight S T c k := by
  let prepared := A.prepareBundle S
  let P := prepared.semanticRows
  let encoded := P.encodeMeasured a S
  have he : encoded.1.toWeightedInstance =
      (rationalMovementInstance a.graph A.relation A.weight S).reindex (EncodedMovement.labelEquiv S) := by
    dsimp only [encoded]
    rw [P.encodeMeasured_value, P.encode_eq_reindex]
    simp only [rationalMovementInstance, Fintype.card_fin]
  have hnone : (encoded.1.solveMeasuredVector d).1 = none ↔
      ¬ ∃ T c k, Independent a.graph T ∧ RationalSlideSequence A.relation A.weight S T c k := by
    rw [encoded.1.solveMeasuredVector_none_iff hd hG, he,
      WeightedInstance.reindex_exists_selection]
    exact rational_no_selection_iff_unreachable a.graph A.relation A.weight A.nonneg S
  rw [← hnone]
  unfold solveMeasured
  change (match hr : (encoded.1.solveMeasuredVector d).1 with
    | none => (none, _)
    | some targets =>
      let ho := encoded.1.solveMeasuredVector_some hd hG hr
      let finished := A.finishVector a S prepared.integerMatrix prepared.weight_eq P targets ho
      (some finished.1, _)).1 = none ↔ _
  split <;> simp_all

end RationalMatrixInput
end IndependentSetDiscovery.WeightedDirected
