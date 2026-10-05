import IndependentSetDiscovery.Algorithms.WeightedCachedReduction
import IndependentSetDiscovery.Algorithms.EncodedMovement

/-! # Cached directed rows enter the concrete finite-table weighted optimizer -/

namespace IndependentSetDiscovery.WeightedShortestPaths.PreparedRows

open Algorithms EncodedMovement WeightedDirected

variable {n : ℕ} {D : Fin n → Fin n → Prop} [DecidableRel D]
variable {w : Fin n → Fin n → ℕ} (P : PreparedRows D w)

def encode (a : ShortestPaths.MatrixGraph n) (S : Finset (Fin n)) : EncodedInput S.card n :=
  let labels := Vector.ofFn (fun i => (labelEquiv S i).val)
  { graphData := a
    allowed := Vector.ofFn fun i => Vector.ofFn fun v => (P.entry labels[i] v).isSome
    costs := Vector.ofFn fun i => Vector.ofFn fun v =>
      (((P.entry labels[i] v).map Route.score).getD 0 : ℚ)
    nonneg := by intro i v hv; simp }

theorem encode_eq_reindex (a : ShortestPaths.MatrixGraph n) (S : Finset (Fin n)) :
    (P.encode a S).toWeightedInstance =
      (WeightedDirected.movementInstance a.graph D w S).reindex (labelEquiv S) := by
  rw [← P.movementInstance_eq a.graph S]
  apply WeightedInstance.ext_data
  · rfl
  · funext i
    ext v
    simp [EncodedInput.mem_candidates, encode, WeightedInstance.reindex, movementInstance]
  · funext i v
    cases h : P.entry (labelEquiv S i).val v <;>
      simp [EncodedInput.toWeightedInstance, encode, WeightedInstance.reindex, movementInstance, h]
    all_goals rfl

def solveEncoded (a : ShortestPaths.MatrixGraph n) (S : Finset (Fin n)) (d : ℕ) :
    Option (S → Fin n) :=
  ((P.encode a S).solve d).map (decodeSelection S)

theorem solveEncoded_some (a : ShortestPaths.MatrixGraph n) (S : Finset (Fin n))
    {d : ℕ} (hd : 2 ≤ d) (hG : BicliqueFree a.graph d d) {x : S → Fin n}
    (hx : P.solveEncoded a S d = some x) :
    (WeightedDirected.movementInstance a.graph D w S).Optimal x := by
  obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hx
  have ho := (P.encode a S).solve_some hd hG hy
  rw [P.encode_eq_reindex] at ho
  have hm := ((WeightedDirected.movementInstance a.graph D w S).reindex_optimal (labelEquiv S) y).mp ho
  have heq : decodeSelection S y = fun s => y ((labelEquiv S).symm s) :=
    funext (decodeSelection_apply S y)
  rwa [heq]

theorem solveEncoded_none_iff (a : ShortestPaths.MatrixGraph n) (S : Finset (Fin n))
    {d : ℕ} (hd : 2 ≤ d) (hG : BicliqueFree a.graph d d) :
    P.solveEncoded a S d = none ↔
      ¬ ∃ x, (WeightedDirected.movementInstance a.graph D w S).Selection x := by
  rw [solveEncoded, Option.map_eq_none_iff, (P.encode a S).solve_none_iff hd hG,
    P.encode_eq_reindex, WeightedInstance.reindex_exists_selection]

end IndependentSetDiscovery.WeightedShortestPaths.PreparedRows
