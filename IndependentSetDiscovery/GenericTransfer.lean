import IndependentSetDiscovery.Algorithms.EncodedMovement
import IndependentSetDiscovery.DiscoveryComplexity
import IndependentSetDiscovery.Algorithms.EagerBitWork

/-!
# Corollary 3.3: algorithmic transfer from a supplied weighted optimizer

Unlike the unconditional concrete biclique-free algorithm, this corollary
*assumes a supplied executable optimizer* with correctness and a declared
measured running-time contract. Its output is a finite vector, not an opaque
selection oracle. The reduction below runs that optimizer on actual encoded
input, and returns an independent target and an actual shortest slide list.

Exactly `|S|` source tables are materialized. The certified finite-table
shortest-path dynamic program replaces the paper's breadth-first searches;
this changes only a polynomial factor. All candidate/cost cells, inverse
labels, selected shortest paths, and reconstruction are explicitly charged.
The underlying graph is unchanged, so the promise parameter may depend on the
input, in particular on its edge count.
-/
namespace IndependentSetDiscovery.GenericTransfer

open ShortestPaths Algorithms EncodedMovement Movement DiscoveryComplexity

variable {n : ℕ}

/-- Conservative primitive-operation tariff for the concrete sorted finite-set
indexing routine: sorting plus a list index/search. This is the same finite
representation convention as `WeightedShortestPaths.PreparedRows.encodeMeasured`.
It is paid per call; no constant-time arbitrary-function access is assumed. -/
def labelIndexWork (k : ℕ) : ℕ := 4*(k+1)^2 + 2*k + 4

/-- Run one actual shortest-path source program per token, storing every row. -/
def sourceRowsMeasured (a : MatrixGraph n) (S : Finset (Fin n)) :
    Vector (Table n) S.card × ℕ :=
  let entries := Vector.ofFn fun i : Fin S.card =>
    let source := (labelEquiv S i).val
    let row := shortestPaths a.graph source
    (row.1, row.2 + labelIndexWork S.card)
  (entries.map Prod.fst, S.card + (entries.toList.map Prod.snd).sum)

@[simp] theorem sourceRowsMeasured_get (a : MatrixGraph n) (S : Finset (Fin n))
    (i : Fin S.card) :
    (sourceRowsMeasured a S).1[i] = (shortestPaths a.graph (labelEquiv S i).val).1 := by
  simp [sourceRowsMeasured]

theorem labelIndexWork_le (S : Finset (Fin n)) :
    labelIndexWork S.card ≤ 10*(n+1)^2 := by
  have hk : S.card ≤ n := by simpa using Finset.card_le_univ S
  have hk2 := Nat.pow_le_pow_left (Nat.add_le_add_right hk 1) 2
  unfold labelIndexWork
  nlinarith

theorem sourceRowsMeasured_cost (a : MatrixGraph n) (S : Finset (Fin n)) :
    (sourceRowsMeasured a S).2 ≤ 39*(n+1)^5 := by
  have hk : S.card ≤ n := by simpa using Finset.card_le_univ S
  have hi := labelIndexWork_le S
  have hp : (n+1)^2 ≤ (n+1)^4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun (i : Fin S.card) _ =>
    Nat.add_le_add (shortestPaths_quartic a (labelEquiv S i).val) hi)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  have hm : S.card * (n+1)^4 ≤ (n+1)^5 := by
    calc
      _ ≤ (n+1) * (n+1)^4 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' (n+1) 4).symm
  have hn : n ≤ (n+1)^5 := by simpa using power_envelope n 1 5 (by omega)
  simp only [sourceRowsMeasured, Vector.toList_ofFn, List.map_ofFn, List.sum_ofFn,
    Function.comp_def]
  nlinarith [Nat.mul_le_mul_left S.card hp]

/-- Read a cached route and traverse its length once, paying also for conversion
to its nonnegative integer rational cost. -/
def encodedCellMeasured (row : Table n) (v : Fin n) : (Bool × ℚ) × ℕ :=
  let entry := row[v]
  let len := (entry.getD []).length
  ((entry.isSome, (len : ℚ)), 8 + 4*len)

/-- The encoder stores all incidence and cost values eagerly. -/
def prepare (a : MatrixGraph n) (S : Finset (Fin n)) : EncodedInput S.card n × ℕ :=
  let rows := sourceRowsMeasured a S
  let cells := Vector.ofFn fun i : Fin S.card =>
    Vector.ofFn (encodedCellMeasured rows.1[i])
  let E : EncodedInput S.card n :=
    { graphData := a
      allowed := cells.map fun row => row.map (fun cell => cell.1.1)
      costs := cells.map fun row => row.map (fun cell => cell.1.2)
      nonneg := by intro i v _; simp [cells, encodedCellMeasured] }
  (E, rows.2 + 8*(S.card+n)+4 +
    (cells.toList.map (fun row => 4*n+(row.toList.map Prod.snd).sum)).sum)

private theorem encoded_ext {k n : ℕ} (E F : EncodedInput k n)
    (hg : E.graphData = F.graphData) (ha : E.allowed = F.allowed) (hc : E.costs = F.costs) : E = F := by
  cases E; cases F; cases hg; cases ha; cases hc; rfl

theorem prepare_value (a : MatrixGraph n) (S : Finset (Fin n)) :
    (prepare a S).1 = encodedInstance a S := by
  apply encoded_ext
  · rfl
  · ext i v
    simp [prepare, encodedInstance, encodeFromRows, encodedCellMeasured,
      ComputedMovement.allRows, sourceRowsMeasured]
  · ext i v
    simp [prepare, encodedInstance, encodeFromRows, encodedCellMeasured,
      ComputedMovement.allRows, sourceRowsMeasured]

theorem source_route_length_le (a : MatrixGraph n) (s v : Fin n) :
    (((shortestPaths a.graph s).1[v]).getD []).length ≤ n := by
  cases he : (shortestPaths a.graph s).1[v] with
  | none => simp
  | some p => exact (table_sound a.graph s n v p he).2

theorem prepare_cost (a : MatrixGraph n) (S : Finset (Fin n)) :
    (prepare a S).2 ≤ 64*(n+1)^5 := by
  have hk : S.card ≤ n := by simpa using Finset.card_le_univ S
  have hr := sourceRowsMeasured_cost a S
  have hcell : ∀ (i : Fin S.card) (v : Fin n),
      (encodedCellMeasured (sourceRowsMeasured a S).1[i] v).2 ≤ 8+4*n := by
    intro i v
    simp only [encodedCellMeasured, sourceRowsMeasured_get]
    have := source_route_length_le a (labelEquiv S i).val v
    omega
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun (i : Fin S.card) _ =>
    Nat.add_le_add_left (Finset.sum_le_sum (s := Finset.univ)
      (fun (v : Fin n) _ => hcell i v)) (4*n))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  have hkn := Nat.mul_le_mul_right (4*n+n*(8+4*n)) hk
  have hp2 : (n+1)^2 ≤ (n+1)^5 := Nat.pow_le_pow_right (by omega) (by omega)
  have hp3 : (n+1)^3 ≤ (n+1)^5 := Nat.pow_le_pow_right (by omega) (by omega)
  change (sourceRowsMeasured a S).2 + 8*(S.card+n)+4 + _ ≤ _
  simp only [Vector.toList_ofFn, List.map_ofFn, List.sum_ofFn, Function.comp_def]
  nlinarith only [hk, hr, hs, hkn, hp2, hp3, Nat.zero_le n, Nat.zero_le (n^2)]

/-- Metric entries need only the bits of integers at most `n`. -/
theorem rationalBits_nat_le (r : ℕ) : rationalBits (r : ℚ) ≤ r+2 := by
  simp only [rationalBits, Rat.num_natCast, Int.natAbs_natCast, Rat.den_natCast,
    show Nat.log2 1 = 0 from rfl]
  have := Nat.log2_le_self r
  omega

theorem metric_inputBits_le (a : MatrixGraph n) (S : Finset (Fin n)) :
    (encodedInstance a S).inputBits ≤ 8*(n+1)^3 := by
  have hk : S.card ≤ n := by simpa using Finset.card_le_univ S
  have hc : ∀ (i : Fin S.card) (v : Fin n),
      rationalBits (encodedInstance a S).costs[i][v] ≤ n+2 := by
    intro i v
    have h := (rationalBits_nat_le _).trans (Nat.add_le_add_right
      (source_route_length_le a (labelEquiv S i).val v) 2)
    simpa [encodedInstance, encodeFromRows, ComputedMovement.allRows] using h
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun (i : Fin S.card) _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun (v : Fin n) _ => hc i v))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  have hkn := Nat.mul_le_mul_right n hk
  have hm := Nat.mul_le_mul_right (n*(n+2)) hk
  unfold EncodedInput.inputBits
  nlinarith only [hk, hs, hkn, hm, Nat.zero_le n, Nat.zero_le (n^2), Nat.zero_le (n^3)]

/-- Decode a supplied finite vector. Inverse labels are computed and cached at
most once per graph vertex; every later selection query is a vector lookup. -/
def decodeVectorMeasured (S : Finset (Fin n)) (targets : Vector (Fin n) S.card) :
    (S → Fin n) × ℕ :=
  let entries := Vector.ofFn fun v : Fin n =>
    if hv : v ∈ S then
      (some ((labelEquiv S).symm ⟨v, hv⟩), S.card + labelIndexWork S.card + 4)
    else (none, S.card + 2)
  let inverse := entries.map Prod.fst
  let selection : S → Fin n := fun s =>
    have hi : inverse[s.val].isSome := by simp [inverse, entries, s.property]
    targets[(inverse[s.val]).get hi]
  (selection, 4*n + (entries.toList.map Prod.snd).sum)

theorem decodeVectorMeasured_apply (S : Finset (Fin n))
    (targets : Vector (Fin n) S.card) (s : S) :
    (decodeVectorMeasured S targets).1 s = targets[(labelEquiv S).symm s] := by
  simp [decodeVectorMeasured]

theorem decodeVectorMeasured_cost (S : Finset (Fin n))
    (targets : Vector (Fin n) S.card) :
    (decodeVectorMeasured S targets).2 ≤ 32*(n+1)^3 := by
  have hk : S.card ≤ n := by simpa using Finset.card_le_univ S
  have hi := labelIndexWork_le S
  have hs : (∑ v : Fin n, (if hv : v ∈ S then
        (some ((labelEquiv S).symm ⟨v, hv⟩), S.card+labelIndexWork S.card+4)
        else (none, S.card+2)).2) ≤ n*(n+10*(n+1)^2+4) := by
    calc
      _ ≤ ∑ _v : Fin n, (n+10*(n+1)^2+4) := by
        apply Finset.sum_le_sum
        intro v _
        split_ifs <;> dsimp <;> omega
      _ = _ := by simp
  simp only [decodeVectorMeasured, Vector.toList_ofFn, List.map_ofFn, List.sum_ofFn,
    Function.comp_def]
  nlinarith only [hs, Nat.zero_le n, Nat.zero_le (n^2), Nat.zero_le (n^3)]

/-- The hypothesis of Corollary 3.3, expressed as supplied executable data.
The work component belongs to the supplied implementation's declared measured
cost model. Correctness is required only on the stated graph promise. No
existence or running-time assertion about such an optimizer is postulated by
this structure, and the concrete main theorem does not take this hypothesis. -/
structure WeightedOptimizer (P : Type*)
    (promise : P → {n : ℕ} → MatrixGraph n → Prop) where
  run : (p : P) → {k n : ℕ} → EncodedInput k n → Option (Vector (Fin n) k) × ℕ
  some_optimal : ∀ {p : P} {k n : ℕ} (E : EncodedInput k n)
    (_hG : promise p E.graphData) {targets : Vector (Fin n) k},
    (run p E).1 = some targets → E.toWeightedInstance.Optimal (fun i => targets[i])
  none_iff : ∀ {p : P} {k n : ℕ} (E : EncodedInput k n)
    (_hG : promise p E.graphData),
    (run p E).1 = none ↔ ¬ ∃ x, E.toWeightedInstance.Selection x

/-- The assumed measured complexity, with a uniform polynomial exponent.
`p` remains a free value; it need not be independent of the input graph. -/
def WeightedOptimizer.HasCostBound {P : Type*}
    {promise : P → {n : ℕ} → MatrixGraph n → Prop}
    (solver : WeightedOptimizer P promise) (f : ℕ → P → ℕ) (q : ℕ) : Prop :=
  ∀ {p : P} {k n : ℕ} (E : EncodedInput k n), promise p E.graphData →
    (solver.run p E).2 ≤ f k p * E.inputBits^q

theorem decoded_optimal (a : MatrixGraph n) (S : Finset (Fin n))
    (targets : Vector (Fin n) S.card)
    (hopt : (prepare a S).1.toWeightedInstance.Optimal (fun i => targets[i])) :
    (movementInstance a.graph S).Optimal (decodeVectorMeasured S targets).1 := by
  rw [prepare_value, encoded_eq_reindex] at hopt
  have h := ((movementInstance a.graph S).reindex_optimal (labelEquiv S)
    (fun i => targets[i])).mp hopt
  have heq : (decodeVectorMeasured S targets).1 = fun s => targets[(labelEquiv S).symm s] :=
    funext (decodeVectorMeasured_apply S targets)
  rwa [heq]

/-- The concrete final stages, including the eager inverse-label cache, the
selected shortest-path cache, and the actual cached collision-free routing. -/
def finish (a : MatrixGraph n) (S : Finset (Fin n))
    (targets : Vector (Fin n) S.card)
    (hopt : (movementInstance a.graph S).Optimal (decodeVectorMeasured S targets).1) :
    DiscoveryResult a.graph S × ℕ :=
  let decoded := decodeVectorMeasured S targets
  let paths := cachedSelectedPathsCounted a.graph S decoded.1 hopt.1
  let out := reconstructOptimalSelection decoded.1 hopt paths.1
  (out, decoded.2 + paths.2 + out.reconstructionWork + 1)

theorem finish_cost (a : MatrixGraph n) (S : Finset (Fin n))
    (targets : Vector (Fin n) S.card)
    (hopt : (movementInstance a.graph S).Optimal (decodeVectorMeasured S targets).1) :
    (finish a S targets hopt).2 ≤ 141*(n+1)^5 := by
  have hd := decodeVectorMeasured_cost S targets
  have hp := selectedPathsSourceWork_polynomial a S (decodeVectorMeasured S targets).1
  have hr := reconstructionWork_polynomial
    (reconstructOptimalSelection (decodeVectorMeasured S targets).1 hopt
      (cachedSelectedPaths a.graph S (decodeVectorMeasured S targets).1 hopt.1))
  have h35 : (n+1)^3 ≤ (n+1)^5 := Nat.pow_le_pow_right (by omega) (by omega)
  have h1 : 1 ≤ (n+1)^5 := Nat.one_le_pow _ _ (by omega)
  unfold finish
  dsimp only
  rw [cachedSelectedPathsCounted_value, cachedSelectedPathsCounted_work]
  nlinarith only [hd, hp, hr, Nat.mul_le_mul_left 32 h35, h1]

theorem finish_optimum_cost (a : MatrixGraph n) (S : Finset (Fin n))
    (targets : Vector (Fin n) S.card)
    (hopt : (movementInstance a.graph S).Optimal (decodeVectorMeasured S targets).1) :
    (((finish a S targets hopt).1.moves.length) : ℚ) =
      (movementInstance a.graph S).selectionCost (decodeVectorMeasured S targets).1 :=
  reconstructOptimalSelection_cost (decodeVectorMeasured S targets).1 hopt
    (cachedSelectedPathsCounted a.graph S (decodeVectorMeasured S targets).1 hopt.1).1

/-- The algorithm in Corollary 3.3, instantiated with the supplied optimizer.
The proof of the graph promise is erased and is not consulted by execution. -/
def runWithTariff {P : Type*} {promise : P → {n : ℕ} → MatrixGraph n → Prop}
    (solver : WeightedOptimizer P promise) (p : P) (a : MatrixGraph n)
    (S : Finset (Fin n)) (hG : promise p a) (auxiliaryTariff : ℕ) :
    Option (DiscoveryResult a.graph S) × ℕ :=
  let prepared := prepare a S
  let answer := solver.run p prepared.1
  match hx : answer.1 with
  | none => (none, answer.2 + (prepared.2 + 1)*auxiliaryTariff)
  | some targets =>
    have hopt := decoded_optimal a S targets (solver.some_optimal prepared.1 hG hx)
    let result := finish a S targets hopt
    (some result.1, answer.2 + (prepared.2 + result.2 + 1)*auxiliaryTariff)

/-- Standard primitive-RAM counter. To compose with a binary-cost optimizer,
use `runWithTariff` and the polynomial `auxiliaryBinaryTariff` below. -/
def run {P : Type*} {promise : P → {n : ℕ} → MatrixGraph n → Prop}
    (solver : WeightedOptimizer P promise) (p : P) (a : MatrixGraph n)
    (S : Finset (Fin n)) (hG : promise p a) : Option (DiscoveryResult a.graph S) × ℕ :=
  runWithTariff solver p a S hG 1

/-- Changing the auxiliary cost model never changes the computed answer. -/
theorem runWithTariff_value {P : Type*} {promise : P → {n : ℕ} → MatrixGraph n → Prop}
    (solver : WeightedOptimizer P promise) (p : P) (a : MatrixGraph n)
    (S : Finset (Fin n)) (hG : promise p a) (tariff : ℕ) :
    (runWithTariff solver p a S hG tariff).1 = (run solver p a S hG).1 := by
  unfold run runWithTariff
  dsimp only
  split <;> rfl

theorem run_none_iff {P : Type*} {promise : P → {n : ℕ} → MatrixGraph n → Prop}
    (solver : WeightedOptimizer P promise) (p : P) (a : MatrixGraph n)
    (S : Finset (Fin n)) (hG : promise p a) :
    (run solver p a S hG).1 = none ↔
      ¬ ∃ T m, Independent a.graph T ∧ SlideSequence a.graph S T m := by
  have he : (solver.run p (prepare a S).1).1 = none ↔
      ¬ ∃ T m, Independent a.graph T ∧ SlideSequence a.graph S T m := by
    rw [solver.none_iff (prepare a S).1 hG, prepare_value, encoded_eq_reindex,
      (movementInstance a.graph S).reindex_exists_selection,
      no_selection_iff_unreachable]
  unfold run runWithTariff
  dsimp only
  split <;> rename_i hx
  · simpa using he.mp hx
  · have hn : ¬ ¬ ∃ T m, Independent a.graph T ∧ SlideSequence a.graph S T m := by
      intro hn
      have := he.mpr hn
      simp [hx] at this
    simp only [Option.some_ne_none, false_iff]
    exact hn

/-- Success includes the actual target and move list, global optimality against
all collision-free sequences, and the paper's finite output-length bound. -/
theorem run_some_spec {P : Type*} {promise : P → {n : ℕ} → MatrixGraph n → Prop}
    (solver : WeightedOptimizer P promise) (p : P) (a : MatrixGraph n)
    (S : Finset (Fin n)) (hG : promise p a) (out : DiscoveryResult a.graph S)
    (_hout : (run solver p a S hG).1 = some out) :
    Independent a.graph out.target ∧ ValidMoves a.graph S out.moves out.target ∧
    out.target.card = S.card ∧
    (∀ T m, Independent a.graph T → SlideSequence a.graph S T m → out.moves.length ≤ m) ∧
    out.moves.length ≤ S.card*(n-1) := by
  exact ⟨out.independent, out.valid, out.valid.slideSequence.card_eq,
    out.optimal, by simpa using out.length_le⟩

/-- Exact additive form: the supplied optimizer's measured work plus polynomial
preprocessing, finite representation conversion, caching, and reconstruction.
This form needs no positivity assumption on a chosen runtime envelope. -/
theorem runWithTariff_cost_additive {P : Type*}
    {promise : P → {n : ℕ} → MatrixGraph n → Prop}
    (solver : WeightedOptimizer P promise) (p : P) (a : MatrixGraph n)
    (S : Finset (Fin n)) (hG : promise p a) (tariff : ℕ) :
    (runWithTariff solver p a S hG tariff).2 ≤
      (solver.run p (prepare a S).1).2 + 206*(n+1)^5*tariff := by
  have hp := prepare_cost a S
  have h1 : 1 ≤ (n+1)^5 := Nat.one_le_pow _ _ (by omega)
  unfold runWithTariff
  dsimp only
  split <;> rename_i hx
  · dsimp only
    exact Nat.add_le_add_left (Nat.mul_le_mul_right tariff (by omega)) _
  · dsimp only
    have hf := finish_cost a S _ (decoded_optimal a S _
      (solver.some_optimal (prepare a S).1 hG hx))
    exact Nat.add_le_add_left (Nat.mul_le_mul_right tariff (by omega)) _

theorem run_cost_additive {P : Type*} {promise : P → {n : ℕ} → MatrixGraph n → Prop}
    (solver : WeightedOptimizer P promise) (p : P) (a : MatrixGraph n)
    (S : Finset (Fin n)) (hG : promise p a) :
    (run solver p a S hG).2 ≤ (solver.run p (prepare a S).1).2 + 206*(n+1)^5 := by
  simpa [run] using runWithTariff_cost_additive solver p a S hG 1

/-- Explicit `f(k,p)` times graph-polynomial transfer. Positivity is the usual
harmless normalization of a running-time envelope (replace `f` by `max 1 f`).
The exponent is uniform and never depends on `k` or `p`. -/
theorem corollary_3_3 {P : Type*} {promise : P → {n : ℕ} → MatrixGraph n → Prop}
    (solver : WeightedOptimizer P promise) (f : ℕ → P → ℕ) (q : ℕ)
    (hcost : solver.HasCostBound f q) (p : P) (a : MatrixGraph n)
    (S : Finset (Fin n)) (hG : promise p a) (hf : 1 ≤ f S.card p) (m : ℕ) :
    (run solver p a S hG).2 ≤
      f S.card p * (8^q+206) * (n+m+1)^(3*q+5) := by
  have hc := hcost (prepare a S).1 hG
  have hb : (prepare a S).1.inputBits ≤ 8*(n+1)^3 := by
    rw [prepare_value]
    exact metric_inputBits_le a S
  have hsearch : (solver.run p (prepare a S).1).2 ≤
      f S.card p * 8^q * (n+1)^(3*q) := by
    calc
      _ ≤ f S.card p * (8*(n+1)^3)^q := hc.trans (Nat.mul_le_mul_left _
        (Nat.pow_le_pow_left hb q))
      _ = _ := by rw [mul_pow, ← pow_mul]; ring
  have hbase : n+1 ≤ n+m+1 := by omega
  have hlow : (n+1)^(3*q) ≤ (n+m+1)^(3*q+5) :=
    (Nat.pow_le_pow_left hbase _).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have hpoly : (n+1)^5 ≤ (n+m+1)^(3*q+5) :=
    (Nat.pow_le_pow_left hbase _).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have haux : 206*(n+1)^5 ≤ f S.card p*206*(n+m+1)^(3*q+5) := by
    calc
      _ ≤ 206*(n+m+1)^(3*q+5) := Nat.mul_le_mul_left _ hpoly
      _ ≤ _ := by nlinarith only [Nat.mul_le_mul_right (206*(n+m+1)^(3*q+5)) hf]
  have hs := Nat.mul_le_mul_left (f S.card p*8^q) hlow
  have ha := run_cost_additive solver p a S hG
  nlinarith only [ha, hsearch, hs, haux]

/-- Input-dependent parameters require no closure assumption or reduction to a
different graph class. In particular `parameter a S` may be the edge count. -/
theorem corollary_3_3_input_dependent {P : Type*}
    {promise : P → {n : ℕ} → MatrixGraph n → Prop}
    (solver : WeightedOptimizer P promise) (f : ℕ → P → ℕ) (q : ℕ)
    (hcost : solver.HasCostBound f q)
    (parameter : MatrixGraph n → Finset (Fin n) → P)
    (a : MatrixGraph n) (S : Finset (Fin n)) (hG : promise (parameter a S) a)
    (hf : 1 ≤ f S.card (parameter a S)) (m : ℕ) :
    (run solver (parameter a S) a S hG).2 ≤
      f S.card (parameter a S)*(8^q+206)*(n+m+1)^(3*q+5) :=
  corollary_3_3 solver f q hcost (parameter a S) a S hG hf m

/-- Transfer in any explicitly declared polynomial auxiliary-instruction
model. This permits a binary-cost optimizer without mixing its bit counter
with uncharged unit-cost graph arithmetic. -/
theorem corollary_3_3_with_polynomial_tariff {P : Type*}
    {promise : P → {n : ℕ} → MatrixGraph n → Prop}
    (solver : WeightedOptimizer P promise) (f : ℕ → P → ℕ) (q : ℕ)
    (hcost : solver.HasCostBound f q) (p : P) (a : MatrixGraph n)
    (S : Finset (Fin n)) (hG : promise p a) (hf : 1 ≤ f S.card p)
    (tariff C d : ℕ) (htariff : tariff ≤ C*(n+1)^d) (m : ℕ) :
    (runWithTariff solver p a S hG tariff).2 ≤
      f S.card p * (8^q+206*C) * (n+m+1)^(3*q+5+d) := by
  have hc := hcost (prepare a S).1 hG
  have hb : (prepare a S).1.inputBits ≤ 8*(n+1)^3 := by
    rw [prepare_value]
    exact metric_inputBits_le a S
  have hsearch : (solver.run p (prepare a S).1).2 ≤
      f S.card p * 8^q * (n+1)^(3*q) := by
    calc
      _ ≤ f S.card p * (8*(n+1)^3)^q := hc.trans (Nat.mul_le_mul_left _
        (Nat.pow_le_pow_left hb q))
      _ = _ := by rw [mul_pow, ← pow_mul]; ring
  have hbase : n+1 ≤ n+m+1 := by omega
  have hlow : (n+1)^(3*q) ≤ (n+m+1)^(3*q+5+d) :=
    (Nat.pow_le_pow_left hbase _).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have hpoly : (n+1)^(5+d) ≤ (n+m+1)^(3*q+5+d) :=
    (Nat.pow_le_pow_left hbase _).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have haux : 206*(n+1)^5*tariff ≤ f S.card p*(206*C)*(n+m+1)^(3*q+5+d) := by
    calc
      _ ≤ 206*(n+1)^5*(C*(n+1)^d) := Nat.mul_le_mul_left _ htariff
      _ = (206*C)*(n+1)^(5+d) := by rw [pow_add]; ring
      _ ≤ (206*C)*(n+m+1)^(3*q+5+d) := Nat.mul_le_mul_left _ hpoly
      _ ≤ _ := by
        nlinarith only [Nat.mul_le_mul_right ((206*C)*(n+m+1)^(3*q+5+d)) hf]
  have hs := Nat.mul_le_mul_left (f S.card p*8^q) hlow
  have ha := runWithTariff_cost_additive solver p a S hG tariff
  nlinarith only [ha, hsearch, hs, haux]

/-- Padded-register width for the unweighted auxiliary computation. All
vertices, route lengths, finite-set indices, matrix addresses, and routing
budgets are polynomially bounded. Even its entire auxiliary instruction
counter fits this width, as the next theorem verifies. Ghost work counters
are not part of the execution's arithmetic data. -/
def auxiliaryRegisterWidth (n : ℕ) : ℕ := 256*(n+1)^2

theorem auxiliary_integer_binaryLength {value : ℕ}
    (hvalue : value ≤ 206*(n+1)^5) : binaryLength value ≤ auxiliaryRegisterWidth n := by
  have hp : n+1 ≤ 2^(n+1) := Nat.lt_two_pow_self.le
  have hconst : 206 ≤ 2^8 := by norm_num
  have hbound : value ≤ 2^(8+(n+1)*5) := by
    calc
      _ ≤ 206*(n+1)^5 := hvalue
      _ ≤ 2^8*(2^(n+1))^5 := Nat.mul_le_mul hconst (Nat.pow_le_pow_left hp 5)
      _ = _ := by rw [← pow_mul, ← pow_add]
  have hbits := binaryLength_le_of_le_pow hbound
  unfold auxiliaryRegisterWidth
  nlinarith only [hbits, Nat.zero_le n, Nat.zero_le (n^2)]

/-- Use exactly the existing padded binary-scalar RAM/list tariff. As elsewhere
in this development, this is an explicit cost model, not a claim about the
Lean VM/compiler. The solver's counter is already in its supplied cost model;
only the auxiliary source programs are rescaled here. -/
def auxiliaryBinaryTariff (n : ℕ) : ℕ := binaryScalarTariff (auxiliaryRegisterWidth n)

theorem auxiliaryBinaryTariff_le :
    auxiliaryBinaryTariff n ≤ (64*257^3)*(n+1)^6 := by
  have h1 : 1 ≤ (n+1)^2 := Nat.one_le_pow _ _ (by omega)
  have hwidth : auxiliaryRegisterWidth n+1 ≤ 257*(n+1)^2 := by
    unfold auxiliaryRegisterWidth
    omega
  calc
    _ ≤ 64*(257*(n+1)^2)^3 := Nat.mul_le_mul_left 64 (Nat.pow_le_pow_left hwidth 3)
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

/-- Binary-cost version of Corollary 3.3 for a supplied binary-cost weighted
optimizer. It returns the same target and moves as `run`, and its polynomial
exponent remains independent of the token count and graph-class parameter. -/
theorem corollary_3_3_binary {P : Type*}
    {promise : P → {n : ℕ} → MatrixGraph n → Prop}
    (solver : WeightedOptimizer P promise) (f : ℕ → P → ℕ) (q : ℕ)
    (hcost : solver.HasCostBound f q) (p : P) (a : MatrixGraph n)
    (S : Finset (Fin n)) (hG : promise p a) (hf : 1 ≤ f S.card p) (m : ℕ) :
    (runWithTariff solver p a S hG (auxiliaryBinaryTariff n)).2 ≤
      f S.card p * (8^q+206*(64*257^3)) * (n+m+1)^(3*q+11) := by
  simpa [Nat.add_assoc] using corollary_3_3_with_polynomial_tariff solver f q hcost
    p a S hG hf (auxiliaryBinaryTariff n) (64*257^3) 6 auxiliaryBinaryTariff_le m

end IndependentSetDiscovery.GenericTransfer
