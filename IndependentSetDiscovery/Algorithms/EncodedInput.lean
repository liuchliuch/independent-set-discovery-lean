import IndependentSetDiscovery.Algorithms.ShortestPaths
import IndependentSetDiscovery.Algorithms.WeightedSolver
import IndependentSetDiscovery.Algorithms.BitComplexity
import IndependentSetDiscovery.Algorithms.EagerComplete
import IndependentSetDiscovery.Algorithms.CappedThreshold
import IndependentSetDiscovery.Algorithms.ThresholdPreparation
import IndependentSetDiscovery.Algorithms.EdgeThresholdPreparation
import IndependentSetDiscovery.Algorithms.SelectionOrigin

/-!
# Concrete finite representation of weighted input

Graph adjacency, candidate incidence and costs are explicit bounded vectors.
Candidate finite sets are materialized once before search; the cost routine
uses the Boolean candidate table directly and never scans a finite set merely
to normalize an off-candidate cost. The dense representation is polynomially
larger than sparse graph/list input: at most `n² + k*n` table slots, plus the
rational entries. The wrapper handles zero vertices and zero labels.
-/

namespace IndependentSetDiscovery
namespace Algorithms

open ShortestPaths

/-- Dense, explicitly represented weighted input. -/
structure EncodedInput (k n : ℕ) where
  graphData : MatrixGraph n
  allowed : Vector (Vector Bool n) k
  costs : Vector (Vector ℚ n) k
  nonneg : ∀ (i : Fin k) (v : Fin n), allowed[i][v] = true → 0 ≤ costs[i][v]

namespace EncodedInput

variable {k n : ℕ} (E : EncodedInput k n)

def graph : SimpleGraph (Fin n) := E.graphData.graph

instance : DecidableRel E.graph.Adj :=
  inferInstanceAs (DecidableRel E.graphData.graph.Adj)

/-- Every row is computed once and stored, rather than an unevaluated filter. -/
def candidateTable : Vector (Finset (Fin n)) k :=
  Vector.ofFn fun i => Finset.univ.filter fun v => E.allowed[i][v] = true

def toWeightedInstance : WeightedInstance (Fin k) (Fin n) :=
  let candidates := E.candidateTable
  { graph := E.graph
    candidates := fun i => candidates[i]
    cost := fun i v => E.costs[i][v]
    nonneg := by
      intro i v hv
      apply E.nonneg i v
      simpa [candidates, candidateTable] using hv }

instance : DecidableRel E.toWeightedInstance.graph.Adj :=
  inferInstanceAs (DecidableRel E.graph.Adj)

@[simp] theorem mem_candidates (i : Fin k) (v : Fin n) :
    v ∈ E.toWeightedInstance.candidates i ↔ E.allowed[i][v] = true := by
  simp [toWeightedInstance, candidateTable]

@[simp] theorem cost_eq (i : Fin k) (v : Fin n) :
    E.toWeightedInstance.cost i v = E.costs[i][v] := rfl

/-- Concrete normalized cost: two bounded-array lookups plus one Boolean test. -/
def normalizedCost (i : Fin k) (v : Fin n) : ℚ :=
  if E.allowed[i][v] = true then E.costs[i][v] else 0

theorem normalizedCost_eq (i : Fin k) (v : Fin n) :
    E.normalizedCost i v = E.toWeightedInstance.normalizedCost i v := by
  simp [normalizedCost, WeightedInstance.normalizedCost]

theorem normalizedCost_nonneg (i : Fin k) (v : Fin n) : 0 ≤ E.normalizedCost i v := by
  rw [E.normalizedCost_eq]
  exact E.toWeightedInstance.normalizedCost_nonneg i v

/-- The concrete lookup has two incidence-table accesses, a Boolean branch,
and at most two cost-table accesses. Rational arithmetic is charged separately. -/
def normalizedCostCounted (i : Fin k) (v : Fin n) : ℚ × ℕ :=
  if E.allowed[i][v] = true then (E.costs[i][v], 5) else (0, 3)

theorem normalizedCostCounted_spec (i : Fin k) (v : Fin n) :
    (E.normalizedCostCounted i v).1 = E.normalizedCost i v ∧
      (E.normalizedCostCounted i v).2 ≤ 8 := by
  unfold normalizedCostCounted normalizedCost
  split_ifs <;> simp

/-- Distinctness plus the two adjacency-matrix accesses is a bounded concrete
compatibility routine, rather than a free arbitrary relation oracle. -/
def compatibleCounted (u v : Fin n) : Bool × ℕ :=
  if u = v then (false, 1) else (!E.graphData.matrix[u][v], 5)

theorem compatibleCounted_spec (u v : Fin n) :
    (E.compatibleCounted u v).1 = decide (Compatible E.graph u v) ∧
      (E.compatibleCounted u v).2 ≤ 8 := by
  by_cases h : u = v
  · simp [compatibleCounted, h, Compatible]
  · simp [compatibleCounted, h, Compatible, graph, MatrixGraph.graph]

/-- Eager measured construction of a single duplicate-free candidate row. -/
def candidateRowCounted (i : Fin k) : Finset (Fin n) × ℕ :=
  let row := filterCounted (fun v : Fin n => E.allowed[i][v]) (List.finRange n)
  let hs : row.1.Nodup := by
    rw [(filterCounted_spec _ _).1]
    exact (List.nodup_finRange n).filter _
  (⟨↑row.1, hs⟩, 4 * row.2 + n + 1)

theorem candidateRowCounted_value (i : Fin k) :
    (E.candidateRowCounted i).1 = E.candidateTable[i] := by
  ext v
  simp [candidateRowCounted, (filterCounted_spec _ _).1, candidateTable]

theorem candidateRowCounted_work (i : Fin k) :
    (E.candidateRowCounted i).2 = 5 * n + 1 := by
  simp [candidateRowCounted, (filterCounted_spec _ _).2]
  omega

def candidateTableCounted : Vector (Finset (Fin n)) k × ℕ :=
  let entries := Vector.ofFn E.candidateRowCounted
  (entries.map Prod.fst, 4 * k + (entries.toList.map Prod.snd).sum)

theorem candidateTableCounted_value : E.candidateTableCounted.1 = E.candidateTable := by
  ext i hi
  simp [candidateTableCounted, E.candidateRowCounted_value]

theorem candidateTableCounted_work : E.candidateTableCounted.2 = 5 * k * (n+1) := by
  simp [candidateTableCounted, Vector.toList_ofFn, List.map_ofFn, List.sum_ofFn,
    Function.comp_def, E.candidateRowCounted_work]
  ring

/-- A finite, explicit input-bit measure; adjacency and candidate bits are
included separately from rational numerator/denominator bits. -/
def inputBits : ℕ :=
  n ^ 2 + k * n + k + n + 1 + ∑ i : Fin k, ∑ v : Fin n, rationalBits E.costs[i][v]

theorem inputBits_pos : 0 < E.inputBits := by unfold inputBits; omega

theorem normalized_numericSize_le :
    numericSize Finset.univ E.toWeightedInstance.candidates E.normalizedCost ≤ E.inputBits := by
  have hs : (∑ i : Fin k, ∑ v ∈ E.toWeightedInstance.candidates i,
      rationalBits (E.normalizedCost i v)) ≤
      ∑ i : Fin k, ∑ v : Fin n, rationalBits E.costs[i][v] := by
    apply Finset.sum_le_sum
    intro i hi
    calc
      _ = ∑ v ∈ E.toWeightedInstance.candidates i, rationalBits E.costs[i][v] := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [normalizedCost, if_pos ((E.mem_candidates i v).mp hv)]
      _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  unfold numericSize inputBits
  simp only [Finset.card_univ, Fintype.card_fin]
  omega

/-- Eagerly store each returned target so later clients only query a vector. -/
def cacheOutput (answer : Option (Fin k → Fin n)) : Option (Fin k → Fin n) :=
  answer.map fun x =>
    let stored := Vector.ofFn x
    fun i => stored[i]

@[simp] theorem cacheOutput_eq (answer : Option (Fin k → Fin n)) : cacheOutput answer = answer := by
  cases answer <;> simp [cacheOutput]

def vectorFunctions (answer : Option (Vector (Fin n) k)) : Option (Fin k → Fin n) :=
  answer.map fun stored => fun i => stored[i]

@[simp] theorem vectorFunctions_ofFn (answer : Option (Fin k → Fin n)) :
    vectorFunctions (answer.map Vector.ofFn) = answer := by
  cases answer <;> simp [vectorFunctions]

/-- The actual finite-table optimizer and its returned operation counter.
The factor eight expands each abstract lookup/compatibility instruction into
its bounded straight-line matrix implementation. `SelectionOrigin` proves
the returned closure has at most `k` updates, justifying `k*(k+2)` to evaluate
and store every output cell once. -/
def runPreparedVector [NeZero n] (table : Vector ℕ (k+1)) : Option (Vector (Fin n) k) × ℕ :=
  let candidates := E.candidateTableCounted
  let result := optimizeEagerComplete (Compatible E.graph) E.normalizedCost
    (cachedThreshold table) Finset.univ candidates.1
  (result.1.map Vector.ofFn, candidates.2 + 8 * result.2 +
    if result.1.isSome then k * (k+2) else 0)

def runPrepared [NeZero n] (table : Vector ℕ (k+1)) : Option (Fin k → Fin n) × ℕ :=
  let out := E.runPreparedVector table
  (vectorFunctions out.1, out.2)

theorem runPrepared_refinement [NeZero n] (threshold : ℕ → ℕ) (table : Vector ℕ (k+1))
    (htable : ∀ r : Fin (k+1), table[r] = min (n+1) (threshold r)) :
    (E.runPrepared table).1 = E.toWeightedInstance.solveWithThreshold threshold := by
  unfold runPrepared runPreparedVector
  dsimp only
  rw [vectorFunctions_ofFn, optimizeEagerComplete_refinement, E.candidateTableCounted_value,
    optimize_cached _ _ _ threshold table htable]
  have hc : E.normalizedCost = E.toWeightedInstance.normalizedCost :=
    funext fun i => funext fun v => E.normalizedCost_eq i v
  unfold WeightedInstance.solveWithThreshold
  rw [hc]
  rfl

def solvePositiveMeasured [NeZero n] (d : ℕ) : Option (Fin k → Fin n) × ℕ :=
  let prep := ThresholdPreparation.balancedTable k n d
  let result := E.runPrepared prep.1
  (result.1, prep.2 + result.2 + 2)

def solvePositiveMeasuredVector [NeZero n] (d : ℕ) : Option (Vector (Fin n) k) × ℕ :=
  let prep := ThresholdPreparation.balancedTable k n d
  let result := E.runPreparedVector prep.1
  (result.1, prep.2 + result.2 + 2)

/-- Search uses the measured eager implementation and the bounded prepared threshold table. -/
def solvePositive [NeZero n] (d : ℕ) : Option (Fin k → Fin n) :=
  (E.solvePositiveMeasured d).1

theorem solvePositive_eq [NeZero n] (d : ℕ) :
    E.solvePositive d = E.toWeightedInstance.solveBicliqueFree d := by
  exact E.runPrepared_refinement (balancedSearchThreshold d) _
    (ThresholdPreparation.balancedTable_spec k n d).1

def emptySelection (_E : EncodedInput k n) (hk : k = 0) : Fin k → Fin n :=
  fun i => False.elim (by have hi := i.isLt; omega)

def solveMeasuredVector (d : ℕ) : Option (Vector (Fin n) k) × ℕ :=
  if hk : k = 0 then (some (Vector.ofFn (E.emptySelection hk)), 1)
  else if hn : n = 0 then (none, 2)
  else
    letI : NeZero n := ⟨hn⟩
    E.solvePositiveMeasuredVector d

/-- Boundary-complete weighted optimizer. Empty label sets return their unique
empty selection, even when the graph itself has no vertices. -/
def solveMeasured (d : ℕ) : Option (Fin k → Fin n) × ℕ :=
  if hk : k = 0 then (some (E.emptySelection hk), 1)
  else if hn : n = 0 then (none, 2)
  else
    letI : NeZero n := ⟨hn⟩
    E.solvePositiveMeasured d

def solve (d : ℕ) : Option (Fin k → Fin n) := (E.solveMeasured d).1

theorem solveMeasuredVector_value (d : ℕ) :
    vectorFunctions (E.solveMeasuredVector d).1 = (E.solveMeasured d).1 := by
  unfold solveMeasuredVector solveMeasured
  split_ifs
  · simp [vectorFunctions]
  · rfl
  · rfl

theorem solveMeasuredVector_work (d : ℕ) :
    (E.solveMeasuredVector d).2 = (E.solveMeasured d).2 := by
  unfold solveMeasuredVector solveMeasured
  split_ifs <;> rfl

theorem optimal_of_no_labels (hk : k = 0) (x : Fin k → Fin n) :
    E.toWeightedInstance.Optimal x := by
  subst k
  refine ⟨⟨fun i => Fin.elim0 i, ?_, ?_⟩, ?_⟩
  · intro i; exact Fin.elim0 i
  · intro i; exact Fin.elim0 i
  · intro y hy
    simp [WeightedInstance.selectionCost]

theorem no_selection_of_no_vertices (hk : k ≠ 0) (hn : n = 0) :
    ¬ ∃ x, E.toWeightedInstance.Selection x := by
  rintro ⟨x, hx⟩
  have h := (x ⟨0, Nat.pos_of_ne_zero hk⟩).isLt
  omega

theorem solve_some {d : ℕ} (hd : 2 ≤ d) (hG : BicliqueFree E.graph d d)
    {x : Fin k → Fin n} (hx : E.solve d = some x) : E.toWeightedInstance.Optimal x := by
  by_cases hk : k = 0
  · exact E.optimal_of_no_labels hk x
  · by_cases hn : n = 0
    · simp [solve, solveMeasured, hk, hn] at hx
    · letI : NeZero n := ⟨hn⟩
      have hx' : E.toWeightedInstance.solveBicliqueFree d = some x := by
        have hp : E.solvePositive d = some x := by
          simpa [solve, solveMeasured, solvePositive, hk, hn] using hx
        rwa [E.solvePositive_eq] at hp
      exact E.toWeightedInstance.solveBicliqueFree_some hd hG hx'

theorem solve_none_iff {d : ℕ} (hd : 2 ≤ d) (hG : BicliqueFree E.graph d d) :
    E.solve d = none ↔ ¬ ∃ x, E.toWeightedInstance.Selection x := by
  by_cases hk : k = 0
  · have hs : ∃ x, E.toWeightedInstance.Selection x :=
      ⟨E.emptySelection hk, (E.optimal_of_no_labels hk _).1⟩
    simp [solve, solveMeasured, hk, hs]
  · by_cases hn : n = 0
    · have hs := E.no_selection_of_no_vertices hk hn
      simp [solve, solveMeasured, hk, hn, hs]
    · letI : NeZero n := ⟨hn⟩
      have he : E.solve d = E.solvePositive d := by
        simp [solve, solveMeasured, solvePositive, hk, hn]
      rw [he, E.solvePositive_eq]
      exact E.toWeightedInstance.solveBicliqueFree_none_iff hd hG

theorem solveMeasuredVector_some {d : ℕ} (hd : 2 ≤ d) (hG : BicliqueFree E.graph d d)
    {stored : Vector (Fin n) k} (h : (E.solveMeasuredVector d).1 = some stored) :
    E.toWeightedInstance.Optimal (fun i => stored[i]) := by
  apply E.solve_some hd hG
  change (E.solveMeasured d).1 = _
  rw [← E.solveMeasuredVector_value, h]
  rfl

theorem solveMeasuredVector_none_iff {d : ℕ} (hd : 2 ≤ d) (hG : BicliqueFree E.graph d d) :
    (E.solveMeasuredVector d).1 = none ↔ ¬∃ x, E.toWeightedInstance.Selection x := by
  rw [← E.solve_none_iff hd hG]
  change _ ↔ (E.solveMeasured d).1 = none
  rw [← E.solveMeasuredVector_value]
  simp [vectorFunctions]

/-- The same concrete representation supports each threshold family in Section 5. -/
def solvePositiveWithThreshold [NeZero n] (threshold : ℕ → ℕ) : Option (Fin k → Fin n) :=
  let table := Vector.ofFn fun r : Fin (k+1) => min (n+1) (threshold r)
  (E.runPrepared table).1

theorem solvePositiveWithThreshold_eq [NeZero n] (threshold : ℕ → ℕ) :
    E.solvePositiveWithThreshold threshold = E.toWeightedInstance.solveWithThreshold threshold := by
  apply E.runPrepared_refinement threshold
  intro r
  simp

def solveWithThreshold (threshold : ℕ → ℕ) : Option (Fin k → Fin n) :=
  if hk : k = 0 then some (E.emptySelection hk)
  else if hn : n = 0 then none
  else
    letI : NeZero n := ⟨hn⟩
    E.solvePositiveWithThreshold threshold

theorem solveWithThreshold_some {threshold : ℕ → ℕ}
    (positive : ∀ r, 0 < threshold r)
    (certificate : TransversalCertificate (ι := Fin k) (Compatible E.graph) threshold)
    {x : Fin k → Fin n} (hx : E.solveWithThreshold threshold = some x) :
    E.toWeightedInstance.Optimal x := by
  by_cases hk : k = 0
  · exact E.optimal_of_no_labels hk x
  · by_cases hn : n = 0
    · simp [solveWithThreshold, hk, hn] at hx
    · letI : NeZero n := ⟨hn⟩
      have hx' : E.toWeightedInstance.solveWithThreshold threshold = some x := by
        simpa [solveWithThreshold, hk, hn, E.solvePositiveWithThreshold_eq] using hx
      exact E.toWeightedInstance.solveWithThreshold_some positive certificate hx'

theorem solveWithThreshold_none_iff {threshold : ℕ → ℕ}
    (positive : ∀ r, 0 < threshold r)
    (certificate : TransversalCertificate (ι := Fin k) (Compatible E.graph) threshold) :
    E.solveWithThreshold threshold = none ↔ ¬ ∃ x, E.toWeightedInstance.Selection x := by
  by_cases hk : k = 0
  · have hs : ∃ x, E.toWeightedInstance.Selection x :=
      ⟨E.emptySelection hk, (E.optimal_of_no_labels hk _).1⟩
    simp [solveWithThreshold, hk, hs]
  · by_cases hn : n = 0
    · have hs := E.no_selection_of_no_vertices hk hn
      simp [solveWithThreshold, hk, hn, hs]
    · letI : NeZero n := ⟨hn⟩
      simpa [solveWithThreshold, hk, hn, E.solvePositiveWithThreshold_eq] using
        E.toWeightedInstance.solveWithThreshold_none_iff positive certificate

/-- A boundary-complete measured driver accepting already prepared threshold
data. Preparation is charged by the concrete producer in the caller. -/
def solvePreparedMeasured (table : Vector ℕ (k+1)) : Option (Fin k → Fin n) × ℕ :=
  if hk : k = 0 then (some (E.emptySelection hk), 1)
  else if hn : n = 0 then (none, 2)
  else
    letI : NeZero n := ⟨hn⟩
    let out := E.runPrepared table
    (out.1, out.2 + 2)

def solvePrepared (table : Vector ℕ (k+1)) : Option (Fin k → Fin n) :=
  (E.solvePreparedMeasured table).1

theorem solvePrepared_refinement (threshold : ℕ → ℕ) (table : Vector ℕ (k+1))
    (htable : ∀ r : Fin (k+1), table[r] = min (n+1) (threshold r)) :
    E.solvePrepared table = E.solveWithThreshold threshold := by
  by_cases hk : k = 0
  · simp [solvePrepared, solvePreparedMeasured, solveWithThreshold, hk]
  · by_cases hn : n = 0
    · simp [solvePrepared, solvePreparedMeasured, solveWithThreshold, hk, hn]
    · letI : NeZero n := ⟨hn⟩
      simp only [solvePrepared, solvePreparedMeasured, solveWithThreshold, dif_neg hk, dif_neg hn]
      exact (E.runPrepared_refinement threshold table htable).trans
        (E.solvePositiveWithThreshold_eq threshold).symm

/-- A concrete producer is evaluated exactly once and its actual counter is
added. The producer itself is skipped in either empty-input boundary case. -/
def solveUsingPreparation (prepare : Unit → Vector ℕ (k+1) × ℕ) :
    Option (Fin k → Fin n) × ℕ :=
  if hk : k = 0 then (some (E.emptySelection hk), 1)
  else if hn : n = 0 then (none, 2)
  else
    letI : NeZero n := ⟨hn⟩
    let prep := prepare ()
    let out := E.runPrepared prep.1
    (out.1, prep.2 + out.2 + 2)

theorem solveUsingPreparation_value (threshold : ℕ → ℕ)
    (prepare : Unit → Vector ℕ (k+1) × ℕ)
    (htable : ∀ r : Fin (k+1), (prepare ()).1[r] = min (n+1) (threshold r)) :
    (E.solveUsingPreparation prepare).1 = E.solveWithThreshold threshold := by
  have he : (E.solveUsingPreparation prepare).1 = E.solvePrepared (prepare ()).1 := by
    unfold solveUsingPreparation solvePrepared solvePreparedMeasured
    split_ifs <;> rfl
  exact he.trans (E.solvePrepared_refinement threshold _ htable)

def solveUsingPreparationVector (prepare : Unit → Vector ℕ (k+1) × ℕ) :
    Option (Vector (Fin n) k) × ℕ :=
  if hk : k = 0 then (some (Vector.ofFn (E.emptySelection hk)), 1)
  else if hn : n = 0 then (none, 2)
  else
    letI : NeZero n := ⟨hn⟩
    let prep := prepare ()
    let out := E.runPreparedVector prep.1
    (out.1, prep.2 + out.2 + 2)

theorem solveUsingPreparationVector_value (prepare : Unit → Vector ℕ (k+1) × ℕ) :
    vectorFunctions (E.solveUsingPreparationVector prepare).1 =
      (E.solveUsingPreparation prepare).1 := by
  unfold solveUsingPreparationVector solveUsingPreparation
  split_ifs
  · simp [vectorFunctions]
  · rfl
  · rfl

theorem solveUsingPreparationVector_work (prepare : Unit → Vector ℕ (k+1) × ℕ) :
    (E.solveUsingPreparationVector prepare).2 = (E.solveUsingPreparation prepare).2 := by
  unfold solveUsingPreparationVector solveUsingPreparation
  split_ifs <;> rfl

theorem solveUsingPreparationVector_some (threshold : ℕ → ℕ)
    (prepare : Unit → Vector ℕ (k+1) × ℕ)
    (htable : ∀ r : Fin (k+1), (prepare ()).1[r] = min (n+1) (threshold r))
    (positive : ∀ r, 0 < threshold r)
    (certificate : TransversalCertificate (ι := Fin k) (Compatible E.graph) threshold)
    {targets : Vector (Fin n) k} (h : (E.solveUsingPreparationVector prepare).1 = some targets) :
    E.toWeightedInstance.Optimal (fun i => targets[i]) := by
  apply E.solveWithThreshold_some positive certificate
  rw [← E.solveUsingPreparation_value threshold prepare htable,
    ← E.solveUsingPreparationVector_value, h]
  rfl

theorem solveUsingPreparationVector_none_iff (threshold : ℕ → ℕ)
    (prepare : Unit → Vector ℕ (k+1) × ℕ)
    (htable : ∀ r : Fin (k+1), (prepare ()).1[r] = min (n+1) (threshold r))
    (positive : ∀ r, 0 < threshold r)
    (certificate : TransversalCertificate (ι := Fin k) (Compatible E.graph) threshold) :
    (E.solveUsingPreparationVector prepare).1 = none ↔
      ¬ ∃ x, E.toWeightedInstance.Selection x := by
  rw [← E.solveWithThreshold_none_iff positive certificate,
    ← E.solveUsingPreparation_value threshold prepare htable,
    ← E.solveUsingPreparationVector_value]
  simp [vectorFunctions]

def solveCodegreeMeasured (s q : ℕ) : Option (Fin k → Fin n) × ℕ :=
  E.solveUsingPreparation (fun _ => ThresholdPreparation.codegreeTable k n s q)

def solveDegeneracyMeasured (a : ℕ) : Option (Fin k → Fin n) × ℕ :=
  E.solveUsingPreparation (fun _ => ThresholdPreparation.degeneracyTable k n a)

def solveEdgeMeasured (m : ℕ) : Option (Fin k → Fin n) × ℕ :=
  E.solveUsingPreparation (fun _ => ThresholdPreparation.edgeTable k n m)

def solveCodegreeMeasuredVector (s q : ℕ) : Option (Vector (Fin n) k) × ℕ :=
  E.solveUsingPreparationVector (fun _ => ThresholdPreparation.codegreeTable k n s q)

def solveDegeneracyMeasuredVector (a : ℕ) : Option (Vector (Fin n) k) × ℕ :=
  E.solveUsingPreparationVector (fun _ => ThresholdPreparation.degeneracyTable k n a)

def solveEdgeMeasuredVector (m : ℕ) : Option (Vector (Fin n) k) × ℕ :=
  E.solveUsingPreparationVector (fun _ => ThresholdPreparation.edgeTable k n m)

theorem solveCodegreeMeasured_value (s q : ℕ) :
    (E.solveCodegreeMeasured s q).1 = E.solveWithThreshold (codegreeSearchThreshold s q) :=
  E.solveUsingPreparation_value _ _ (ThresholdPreparation.codegreeTable_spec k n s q).1

theorem solveDegeneracyMeasured_value (a : ℕ) :
    (E.solveDegeneracyMeasured a).1 = E.solveWithThreshold (degeneracyPrefixThreshold a) :=
  E.solveUsingPreparation_value _ _ (ThresholdPreparation.degeneracyTable_spec k n a).1

theorem solveEdgeMeasured_value (m : ℕ) :
    (E.solveEdgeMeasured m).1 = E.solveWithThreshold (edgePrefixThreshold m) :=
  E.solveUsingPreparation_value _ _ (ThresholdPreparation.edgeTable_spec k n m).1

end EncodedInput
end Algorithms
end IndependentSetDiscovery
