import IndependentSetDiscovery.Algorithms.WeightedEncodedReduction
import IndependentSetDiscovery.Algorithms.WeightedSelectedPaths

/-! Measured materialization of the directed cached rows as finite encoded
weighted input. Source enumeration and each matrix cell run once, and value
and work are returned by the same vector loops. -/
namespace IndependentSetDiscovery.WeightedShortestPaths.PreparedRows

open Algorithms EncodedMovement
variable {n : ℕ} {D : Fin n → Fin n → Prop} [DecidableRel D]
variable {w : Fin n → Fin n → ℕ} (P : PreparedRows D w)

def encodedCell (s v : Fin n) : (Bool × ℚ) × ℕ :=
  let entry := P.entry s v
  ((entry.isSome, ((entry.map Route.score).getD 0 : ℚ)), 8)

theorem encodedCell_nonneg (s v : Fin n) : 0 ≤ (P.encodedCell s v).1.2 := by
  unfold encodedCell
  cases P.entry s v <;> simp

/-- The finite enumeration charge includes a quadratic sort/index bound for
each source label. Entry callbacks perform only cached vector lookups. -/
def encodeMeasured (a : ShortestPaths.MatrixGraph n) (S : Finset (Fin n)) :
    EncodedInput S.card n × ℕ :=
  let labels := Vector.ofFn fun i : Fin S.card =>
    ((labelEquiv S i).val, 4*(S.card+1)^2+2*S.card+4)
  let cells := Vector.ofFn fun i => Vector.ofFn (P.encodedCell labels[i].1)
  let E : EncodedInput S.card n :=
    { graphData := a
      allowed := cells.map fun row => row.map (fun cell => cell.1.1)
      costs := cells.map fun row => row.map (fun cell => cell.1.2)
      nonneg := by
        intro i v _
        simpa [cells] using P.encodedCell_nonneg labels[i].1 v }
  (E, 8*(S.card+n)+4+(labels.toList.map Prod.snd).sum+
    (cells.toList.map (fun row => 4*n+(row.toList.map Prod.snd).sum)).sum)

private theorem encoded_eq_of_data {k n : ℕ} (E F : EncodedInput k n)
    (hg : E.graphData = F.graphData) (ha : E.allowed = F.allowed) (hc : E.costs = F.costs) : E = F := by
  cases E
  cases F
  cases hg
  cases ha
  cases hc
  rfl

theorem encodeMeasured_value (a : ShortestPaths.MatrixGraph n) (S : Finset (Fin n)) :
    (P.encodeMeasured a S).1 = P.encode a S := by
  apply encoded_eq_of_data
  · rfl
  · ext i v
    simp [encodeMeasured, encode, encodedCell]
  · ext i v
    simp [encodeMeasured, encode, encodedCell]

theorem encodeMeasured_cost (a : ShortestPaths.MatrixGraph n) (S : Finset (Fin n)) :
    (P.encodeMeasured a S).2 ≤ 64*(n+1)^4 := by
  have hk : S.card ≤ n := by simpa using Finset.card_le_univ S
  have hk2 := Nat.pow_le_pow_left (Nat.add_le_add_right hk 1) 2
  have hm := Nat.mul_le_mul hk hk2
  have hkn := Nat.mul_le_mul_right n hk
  have hkk := Nat.pow_le_pow_left hk 2
  simp only [encodeMeasured, Vector.toList_ofFn, List.map_ofFn, List.sum_ofFn,
    Function.comp_def, encodedCell, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  norm_cast
  nlinarith only [hk, hm, hkn, hkk, Nat.zero_le (n^4), Nat.zero_le (n^3),
    Nat.zero_le (n^2), Nat.zero_le n]


/-- Decode an already materialized output vector. All source-index inverses
are computed in one measured vector pass; no arbitrary function is evaluated. -/
def decodeVectorMeasured (S : Finset (Fin n)) (targets : Vector (Fin n) S.card) :
    (S → Fin n) × ℕ :=
  let inverse := Vector.ofFn (inverseIndexCell S)
  let answer : S → Fin n := fun s =>
    let hi : (inverse[s.val]).1.isSome := by simp [inverse, inverseIndexCell, s.property]
    targets[(inverse[s.val]).1.get hi]
  (answer, 8*n+4+(inverse.toList.map Prod.snd).sum)

@[simp] theorem decodeVectorMeasured_apply (S : Finset (Fin n))
    (targets : Vector (Fin n) S.card) (s : S) :
    (decodeVectorMeasured S targets).1 s = targets[(labelEquiv S).symm s] := by
  simp [decodeVectorMeasured, inverseIndexCell, s.property]

theorem decodeVectorMeasured_cost (S : Finset (Fin n))
    (targets : Vector (Fin n) S.card) :
    (decodeVectorMeasured S targets).2 ≤ 32*(n+1)^3 := by
  simp only [decodeVectorMeasured, Vector.toList_ofFn, List.map_ofFn, List.sum_ofFn,
    Function.comp_def, inverseIndexCell, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  norm_cast
  nlinarith [Nat.zero_le (n^3), Nat.zero_le (n^2), Nat.zero_le n]

end IndependentSetDiscovery.WeightedShortestPaths.PreparedRows
