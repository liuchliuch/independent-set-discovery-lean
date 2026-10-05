import IndependentSetDiscovery.Algorithms.ExecutionInvariant
import IndependentSetDiscovery.Algorithms.EagerOptimization

/-!
# Execution and bit-invariant refinement for the eager table machine

These are trace equalities, stronger than equality of the final Boolean or
assignment. They project the actual measured decision and recovery branch
choices to the traces whose residual arithmetic was bounded earlier.
-/
namespace IndependentSetDiscovery.Algorithms

/-- Exact trace refinement along the same instruction map used for the
value refinement of the measured interpreter. -/
theorem runTrace_map_refinement (stepA : α → Instruction α) (stepB : β → Instruction β)
    (f : α → β) (hrefine : ∀ a, (stepA a).map f = stepB (f a)) :
    ∀ fuel a, (runTrace stepA fuel a).map f = runTrace stepB fuel (f a) := by
  intro fuel
  induction fuel with
  | zero => intro a; rfl
  | succ fuel ih =>
    intro a
    have h := (hrefine a).symm
    cases ha : stepA a <;> simp only [ha, Instruction.map] at h
    · simp [runTrace, ha, h]
    · simp [runTrace, ha, h]
    · simp [runTrace, ha, h, List.map_flatMap, List.flatMap_map, ih, Function.comp_def]

theorem list_sum_flatMap (f : α → List ℕ) (xs : List α) :
    (xs.flatMap f).sum = (xs.map fun a => (f a).sum).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [ih]

/-- The trace charges sum to the measured interpreter's actual work projection.
The same pass evaluates precisely these nodes with their measured tariffs. -/
theorem execute_trace_work (step : σ → Instruction σ × ℕ) : ∀ fuel s,
    ((runTrace (fun t => (step t).1) fuel s).map (fun t => (step t).2)).sum =
      (execute step fuel s).2 := by
  intro fuel
  induction fuel with
  | zero =>
    intro s
    cases h : step s with
    | mk ins charge => cases ins <;> simp [runTrace, execute, h]
  | succ fuel ih =>
    intro s
    cases h : step s with
    | mk ins charge => cases ins <;>
        simp [runTrace, execute, h, List.map_flatMap, list_sum_flatMap, ih,
          List.map_map, Function.comp_def]

variable {k n : ℕ} [Inhabited (Fin n)]
variable (R : Fin n → Fin n → Prop) [DecidableRel R] (cost : Fin k → Fin n → ℚ)

/-- Actual queried children of the measured self-reduction. The probe counter
is ignored here, but every decision outcome and stopping choice is retained. -/
def recoverMeasuredQueries (oracle : EagerState k n → Bool × ℕ) :
    ℕ → EagerState k n → List (EagerState k n)
  | 0, _ => []
  | fuel + 1, s =>
    if h : s.labels.Nonempty then
      let i := s.labels.min' h
      let choices := (s.rows[i]).sort (· ≤ ·)
      let p := fun v =>
        let child := eagerChild R cost s i v
        let answer := oracle child
        (answer.1, eagerChildWork s + answer.2)
      let queries := (firstYesTrace (fun v => (p v).1) choices).map (eagerChild R cost s i)
      match (probeMeasured p choices).1 with
      | none => queries
      | some v => queries ++ recoverMeasuredQueries oracle fuel (eagerChild R cost s i v)
    else []

theorem recoverMeasuredQueries_refinement
    (oracle : EagerState k n → Bool × ℕ) (old : State (Fin k) (Fin n) → Bool)
    (horacle : ∀ s, (oracle s).1 = old s.toState) :
    ∀ fuel s, (recoverMeasuredQueries R cost oracle fuel s).map EagerState.toState =
      recoverQueries R cost old fuel s.toState := by
  intro fuel
  induction fuel with
  | zero => intro s; rfl
  | succ fuel ih =>
    intro s
    by_cases h : s.labels.Nonempty
    · simp only [recoverMeasuredQueries, recoverQueries, EagerState.toState, dif_pos h]
      simp only [probeMeasured_value, horacle, eagerChild_refinement, ← firstYes_value]
      split <;> simp_all only [List.map_append, List.map_map, Function.comp_def,
        eagerChild_refinement, ih, EagerState.toState]
        <;> simp [eagerChild, EagerState.ofState, EagerState.toState]
    · simp [recoverMeasuredQueries, recoverQueries, EagerState.toState, h]

theorem residualInvariant_eagerChild
    {L : Finset (Fin k)} {A : Fin k → Finset (Fin n)} {B : ℚ} {s : EagerState k n}
    (hs : ResidualInvariant cost L A B s.toState)
    (i : Fin k) (hi : i ∈ s.labels) (v : Fin n) (hv : v ∈ s.rows[i]) :
    ResidualInvariant cost L A B (eagerChild R cost s i v).toState := by
  rw [eagerChild_refinement]
  exact hs.child R cost i hi v hv

variable (threshold : ℕ → ℕ)

theorem residualInvariant_eagerStep
    {L : Finset (Fin k)} {A : Fin k → Finset (Fin n)} {B : ℚ} {s : EagerState k n}
    (hs : ResidualInvariant cost L A B s.toState) (children : List (EagerState k n))
    (hstep : eagerStep R cost threshold s = .branch children) :
    ∀ t ∈ children, ResidualInvariant cost L A B t.toState := by
  have href := eagerStep_refinement R cost threshold s
  rw [hstep] at href
  intro t ht
  exact hs.prefixStep R cost costPrefixOperations threshold
    (children.map EagerState.toState) href.symm t.toState (List.mem_map_of_mem ht)


/-- The exact eager optimizer oracle inputs, retaining measured search and
self-reduction control flow. -/
def optimizeEagerQueries (L : Finset (Fin k)) (rows : Vector (Finset (Fin n)) k) :
    List (EagerState k n) :=
  let A := fun i => rows[i]
  let D := commonDenominator L A cost
  let U := upperBudget L A (scaledCosts L A cost)
  let initial := fun b : ℕ => EagerState.mk L rows ((b : ℚ) / D)
  let oracle := eagerDecide R cost threshold
  let p := fun b => oracle (initial b)
  (leastBudgetQueries (fun b => (p b).1) U).map initial ++
    match (leastBudgetMeasured p U).1 with
    | none => []
    | some b => recoverMeasuredQueries R cost oracle L.card (initial b)

theorem optimizeEagerQueries_refinement (L : Finset (Fin k))
    (rows : Vector (Finset (Fin n)) k) :
    (optimizeEagerQueries R cost threshold L rows).map EagerState.toState =
      optimizeQueries R cost costPrefixOperations threshold L (fun i => rows[i]) := by
  have ho := eagerDecide_refinement R cost threshold
  unfold optimizeEagerQueries optimizeQueries
  dsimp only
  rw [leastBudgetMeasured_value]
  simp only [List.map_append, List.map_map, Function.comp_def, ho, EagerState.toState,
    budgetState]
  split <;> simp_all only [List.map_nil, recoverMeasuredQueries_refinement R cost _ _ ho,
    EagerState.toState]

/-- Actual state expansions of every measured oracle invocation. -/
def optimizeEagerExecutionTrace (L : Finset (Fin k))
    (rows : Vector (Finset (Fin n)) k) : List (EagerState k n) :=
  (optimizeEagerQueries R cost threshold L rows).flatMap fun s =>
    runTrace (eagerStep R cost threshold) s.labels.card s

theorem optimizeEagerExecutionTrace_refinement (L : Finset (Fin k))
    (rows : Vector (Finset (Fin n)) k) :
    (optimizeEagerExecutionTrace R cost threshold L rows).map EagerState.toState =
      optimizeExecutionTrace R cost costPrefixOperations threshold L (fun i => rows[i]) := by
  unfold optimizeEagerExecutionTrace optimizeExecutionTrace
  rw [← optimizeEagerQueries_refinement R cost threshold L rows]
  simp only [List.map_flatMap, List.flatMap_map, Function.comp_def]
  apply List.flatMap_congr
  intro s hs
  exact runTrace_map_refinement (eagerStep R cost threshold)
    (prefixStep R cost costPrefixOperations threshold) EagerState.toState
    (eagerStep_refinement R cost threshold) s.labels.card s

theorem optimizeEagerExecutionTrace_invariant (L : Finset (Fin k))
    (rows : Vector (Finset (Fin n)) k) (s : EagerState k n)
    (hs : s ∈ optimizeEagerExecutionTrace R cost threshold L rows) :
    ∃ b ≤ upperBudget L (fun i => rows[i]) (scaledCosts L (fun i => rows[i]) cost),
      ResidualInvariant cost L (fun i => rows[i])
        ((b : ℚ) / commonDenominator L (fun i => rows[i]) cost) s.toState := by
  apply optimizeExecutionTrace_invariant R cost costPrefixOperations threshold L (fun i => rows[i])
  rw [← optimizeEagerExecutionTrace_refinement R cost threshold L rows]
  exact List.mem_map_of_mem hs

/-- All eagerly scanned rows, even inactive ones, are original-candidate
subsets. The finite encoded solver starts from all labels; their numeric
encoding therefore covers every row materialized by `eagerStepCounted`. -/
theorem optimizeEagerExecutionTrace_allRow_bits
    (rows : Vector (Finset (Fin n)) k) (s : EagerState k n)
    (hs : s ∈ optimizeEagerExecutionTrace R cost threshold Finset.univ rows)
    (i : Fin k) (v : Fin n) (hv : v ∈ s.rows[i]) :
    rationalBits (cost i v) ≤ numericSize Finset.univ (fun j => rows[j]) cost := by
  rcases optimizeEagerExecutionTrace_invariant R cost threshold Finset.univ rows s hs with
    ⟨b, hb, hs⟩
  exact rationalBits_le_numericSize Finset.univ (fun j => rows[j]) cost i
    (Finset.mem_univ _) v (hs.candidates_subset cost i hv)

/-- The eager machine has exactly the same active-state rational bounds,
including rejected negative budgets and tentative child subtractions. -/
theorem optimizeEagerExecutionTrace_operands_bits (nonneg : ∀ i v, 0 ≤ cost i v)
    (L : Finset (Fin k)) (rows : Vector (Finset (Fin n)) k) (s : EagerState k n)
    (hs : s ∈ optimizeEagerExecutionTrace R cost threshold L rows) :
    let S := numericSize L (fun i => rows[i]) cost
    rationalBits s.budget ≤ 4*S+2 ∧
    rationalBits (prefixTotal cost costPrefixOperations threshold s.toState) ≤ 4*S+2 ∧
    (∀ i ∈ s.labels, ∀ v ∈ s.rows[i], rationalBits (cost i v) ≤ S) ∧
    (∀ i ∈ s.labels, ∀ v ∈ s.rows[i], rationalBits (s.budget - cost i v) ≤ 4*S+2) := by
  apply optimizeExecutionTrace_operands_bits R cost threshold nonneg L (fun i => rows[i]) s.toState
  rw [← optimizeEagerExecutionTrace_refinement R cost threshold L rows]
  exact List.mem_map_of_mem hs

/-- Every measured prefix, including prefixes in inactive vector slots, has
a bounded maximum. Only the initial all-label condition is needed for this
extra eager-materialization work. -/
theorem optimizeEagerExecutionTrace_allPrefix_bits
    (rows : Vector (Finset (Fin n)) k) (s : EagerState k n)
    (hs : s ∈ optimizeEagerExecutionTrace R cost threshold Finset.univ rows)
    (i : Fin k) (t : ℕ) :
    rationalBits (measuredPrefix (cost i) (s.rows[i]) t).2.1 ≤
      4 * numericSize Finset.univ (fun j => rows[j]) cost + 2 := by
  rw [(measuredPrefix_spec (cost i) (s.rows[i]) t).2.1]
  rcases prefixMax_eq_zero_or_mem (cost i) (cheapPrefix (cost i) (s.rows[i]) t) with
    h | ⟨v, hv, heq⟩
  · rw [h, show rationalBits (0 : ℚ) = 2 from by decide]
    omega
  · rw [heq]
    have hcost := optimizeEagerExecutionTrace_allRow_bits R cost threshold rows s hs i v
      (cheapPrefix_subset _ _ _ hv)
    omega

/-- Likewise every prefix of a maximum scan over any stored row, active or
inactive, has a bounded accumulator before it is put in the prefix vector. -/
theorem optimizeEagerExecutionTrace_allMaximumAccumulator_bits
    (rows : Vector (Finset (Fin n)) k) (s : EagerState k n)
    (hs : s ∈ optimizeEagerExecutionTrace R cost threshold Finset.univ rows)
    (i : Fin k) (xs : List (Fin n)) (hn : xs.Nodup)
    (hx : ∀ v ∈ xs, v ∈ s.rows[i]) (j : ℕ) :
    rationalBits (((xs.take j).map (cost i)).foldl max 0) ≤
      4 * numericSize Finset.univ (fun a => rows[a]) cost + 2 := by
  rw [maximumScan_eq_prefixMax _ _ hn.take]
  rcases prefixMax_eq_zero_or_mem (cost i) (xs.take j).toFinset with h | ⟨v, hv, heq⟩
  · rw [h, show rationalBits (0 : ℚ) = 2 from by decide]
    omega
  · rw [heq]
    have hcost := optimizeEagerExecutionTrace_allRow_bits R cost threshold rows s hs i v
      (hx v (List.mem_of_mem_take (List.mem_toFinset.mp hv)))
    omega

end IndependentSetDiscovery.Algorithms
