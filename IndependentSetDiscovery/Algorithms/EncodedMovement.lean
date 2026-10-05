import IndependentSetDiscovery.Algorithms.EncodedInput
import IndependentSetDiscovery.Algorithms.ComputedMovement
import IndependentSetDiscovery.Algorithms.Reindex
import IndependentSetDiscovery.Algorithms.CertificateReindex

/-! Graph-metric preprocessing into the concrete encoded weighted solver.
Labels are enumerated by their sorted starting vertices, using a computable
finite order isomorphism. Successful selections are eagerly tabulated again
before translating back to the original subtype of starting vertices. -/

namespace IndependentSetDiscovery.EncodedMovement

open ShortestPaths ComputedMovement Movement Algorithms

variable {n : ℕ}

def labelEquiv (S : Finset (Fin n)) : Fin S.card ≃ S :=
  (S.orderIsoOfFin rfl).toEquiv

/-- Store both incidence and rational costs explicitly after shortest paths. -/
def encodeFromRows (a : MatrixGraph n) (S : Finset (Fin n))
    (rows : Vector (Table n) n) : EncodedInput S.card n :=
  let labels := Vector.ofFn (fun i => (labelEquiv S i).val)
  { graphData := a
    allowed := Vector.ofFn fun i => Vector.ofFn fun v => rows[labels[i]][v].isSome
    costs := Vector.ofFn fun i => Vector.ofFn fun v => ((rows[labels[i]][v].getD []).length : ℚ)
    nonneg := by intro i v hv; simp }

def encodedInstance (a : MatrixGraph n) (S : Finset (Fin n)) : EncodedInput S.card n :=
  let rows := allRows a
  encodeFromRows a S rows

theorem encoded_candidates (a : MatrixGraph n) (S : Finset (Fin n))
    (i : Fin S.card) (v : Fin n) :
    v ∈ (encodedInstance a S).toWeightedInstance.candidates i ↔
      a.graph.Reachable (labelEquiv S i).val v := by
  rw [EncodedInput.mem_candidates]
  have hm := computed_candidates a S (labelEquiv S i) v
  simpa [encodedInstance, encodeFromRows, ComputedMovement.computedInstance,
    ComputedMovement.instanceFromRows] using hm

theorem encoded_cost (a : MatrixGraph n) (S : Finset (Fin n))
    (i : Fin S.card) (v : Fin n) :
    (encodedInstance a S).toWeightedInstance.cost i v =
      (a.graph.dist (labelEquiv S i).val v : ℚ) := by
  simpa [encodedInstance, encodeFromRows, EncodedInput.toWeightedInstance,
    ComputedMovement.computedInstance, ComputedMovement.instanceFromRows] using
    computed_cost a S (labelEquiv S i) v

theorem encoded_eq_reindex (a : MatrixGraph n) (S : Finset (Fin n)) :
    (encodedInstance a S).toWeightedInstance =
      (movementInstance a.graph S).reindex (labelEquiv S) := by
  apply WeightedInstance.ext_data
  · rfl
  · funext i
    ext v
    rw [encoded_candidates]
    exact (movementInstance_mem a.graph S (labelEquiv S i) v).symm
  · funext i v
    exact encoded_cost a S i v

/-- Cache both output vertices and the inverse label map. The returned function
therefore performs bounded vector lookups instead of replaying the solver's
update closures or sorting the source set on each query. -/
def decodeSelection (S : Finset (Fin n)) (x : Fin S.card → Fin n) : S → Fin n :=
  let targets := Vector.ofFn x
  let inverse := Vector.ofFn fun v : Fin n =>
    if hv : v ∈ S then some ((labelEquiv S).symm ⟨v, hv⟩) else none
  fun s =>
    let hi : inverse[s.val].isSome := by simp [inverse, s.property]
    targets[(inverse[s.val]).get hi]

theorem decodeSelection_apply (S : Finset (Fin n)) (x : Fin S.card → Fin n) (s : S) :
    decodeSelection S x s = x ((labelEquiv S).symm s) := by
  simp [decodeSelection, s.property]

def solveEncoded (a : MatrixGraph n) (S : Finset (Fin n)) (d : ℕ) : Option (S → Fin n) :=
  let E := encodedInstance a S
  (E.solve d).map (decodeSelection S)

theorem solveEncoded_some (a : MatrixGraph n) (S : Finset (Fin n))
    {d : ℕ} (hd : 2 ≤ d) (hG : BicliqueFree a.graph d d) {x : S → Fin n}
    (hx : solveEncoded a S d = some x) : (movementInstance a.graph S).Optimal x := by
  obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hx
  have ho := (encodedInstance a S).solve_some hd hG hy
  rw [encoded_eq_reindex] at ho
  have hm := ((movementInstance a.graph S).reindex_optimal (labelEquiv S) y).mp ho
  have heq : decodeSelection S y = fun s => y ((labelEquiv S).symm s) :=
    funext (decodeSelection_apply S y)
  rwa [heq]

theorem solveEncoded_none_iff (a : MatrixGraph n) (S : Finset (Fin n))
    {d : ℕ} (hd : 2 ≤ d) (hG : BicliqueFree a.graph d d) :
    solveEncoded a S d = none ↔ ¬ ∃ x, (movementInstance a.graph S).Selection x := by
  rw [solveEncoded, Option.map_eq_none_iff, (encodedInstance a S).solve_none_iff hd hG,
    encoded_eq_reindex, (movementInstance a.graph S).reindex_exists_selection]

def solveEncodedWithThreshold (a : MatrixGraph n) (S : Finset (Fin n))
    (threshold : ℕ → ℕ) : Option (S → Fin n) :=
  let E := encodedInstance a S
  (E.solveWithThreshold threshold).map (decodeSelection S)

theorem solveEncodedWithThreshold_some (a : MatrixGraph n) (S : Finset (Fin n))
    {threshold : ℕ → ℕ} (positive : ∀ r, 0 < threshold r)
    (certificate : TransversalCertificate (ι := S) (Compatible a.graph) threshold)
    {x : S → Fin n} (hx : solveEncodedWithThreshold a S threshold = some x) :
    (movementInstance a.graph S).Optimal x := by
  obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hx
  have hc := reindex_certificate (Compatible a.graph) threshold (labelEquiv S) certificate
  have ho := (encodedInstance a S).solveWithThreshold_some positive hc hy
  rw [encoded_eq_reindex] at ho
  have hm := ((movementInstance a.graph S).reindex_optimal (labelEquiv S) y).mp ho
  have heq : decodeSelection S y = fun s => y ((labelEquiv S).symm s) :=
    funext (decodeSelection_apply S y)
  rwa [heq]

theorem solveEncodedWithThreshold_none_iff (a : MatrixGraph n) (S : Finset (Fin n))
    {threshold : ℕ → ℕ} (positive : ∀ r, 0 < threshold r)
    (certificate : TransversalCertificate (ι := S) (Compatible a.graph) threshold) :
    solveEncodedWithThreshold a S threshold = none ↔
      ¬ ∃ x, (movementInstance a.graph S).Selection x := by
  have hc := reindex_certificate (Compatible a.graph) threshold (labelEquiv S) certificate
  rw [solveEncodedWithThreshold, Option.map_eq_none_iff,
    (encodedInstance a S).solveWithThreshold_none_iff positive hc,
    encoded_eq_reindex, (movementInstance a.graph S).reindex_exists_selection]

def solveEncodedPrepared (a : MatrixGraph n) (S : Finset (Fin n))
    (table : Vector ℕ (S.card+1)) : Option (S → Fin n) :=
  ((encodedInstance a S).solvePrepared table).map (decodeSelection S)

theorem solveEncodedPrepared_eq (a : MatrixGraph n) (S : Finset (Fin n))
    (threshold : ℕ → ℕ) (table : Vector ℕ (S.card+1))
    (htable : ∀ r : Fin (S.card+1), table[r] = min (n+1) (threshold r)) :
    solveEncodedPrepared a S table = solveEncodedWithThreshold a S threshold := by
  unfold solveEncodedPrepared solveEncodedWithThreshold
  rw [(encodedInstance a S).solvePrepared_refinement threshold table htable]

theorem solveEncodedPrepared_some (a : MatrixGraph n) (S : Finset (Fin n))
    (threshold : ℕ → ℕ) (table : Vector ℕ (S.card+1))
    (htable : ∀ r : Fin (S.card+1), table[r] = min (n+1) (threshold r))
    (positive : ∀ r, 0 < threshold r)
    (certificate : TransversalCertificate (ι := S) (Compatible a.graph) threshold)
    {x : S → Fin n} (hx : solveEncodedPrepared a S table = some x) :
    (movementInstance a.graph S).Optimal x := by
  rw [solveEncodedPrepared_eq a S threshold table htable] at hx
  exact solveEncodedWithThreshold_some a S positive certificate hx

theorem solveEncodedPrepared_none_iff (a : MatrixGraph n) (S : Finset (Fin n))
    (threshold : ℕ → ℕ) (table : Vector ℕ (S.card+1))
    (htable : ∀ r : Fin (S.card+1), table[r] = min (n+1) (threshold r))
    (positive : ∀ r, 0 < threshold r)
    (certificate : TransversalCertificate (ι := S) (Compatible a.graph) threshold) :
    solveEncodedPrepared a S table = none ↔
      ¬ ∃ x, (movementInstance a.graph S).Selection x := by
  rw [solveEncodedPrepared_eq a S threshold table htable]
  exact solveEncodedWithThreshold_none_iff a S positive certificate

end IndependentSetDiscovery.EncodedMovement
