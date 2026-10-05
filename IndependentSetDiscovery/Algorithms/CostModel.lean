import IndependentSetDiscovery.Algorithms.PrefixSearch
import IndependentSetDiscovery.Algorithms.Witness
import Mathlib.Algebra.BigOperators.Ring.List

/-!
# Intermediate finite-set charge-schedule algebra

This file alone is not an execution-cost certificate for arbitrary
`PrefixOperations`, cost functions, or adjacency procedures. The concrete
primitive refinements and eager finite-table machine are in `PrimitiveCosts`,
`EagerMachine`, `MeasuredExecution`, and `EagerBounds`. The definitions here
are retained as intermediate algebraic charge schedules.

Model: vertices, labels, and adjacency-table entries are machine words. Candidate
sets are explicit finite containers. A linear pass is charged once per entry;
a deterministic comparison sort or duplicate-removal pass on `n` entries is
charged `(n+1)^2` comparisons/moves (a conservative quadratic tariff). Exact
rational additions/subtractions/comparisons are counted as primitive arithmetic
operations here; the operand-size lemmas in `BitComplexity` refine these charges.

`nodeWork` is a compositional tariff for the actual finite operations in
`prefixStep`: labels, two sorts and prefix conversion per candidate set, maxima,
and materialization of every computed child. It is not a desired final runtime
used as a definition. `runWork` follows the same computed children as `run`.
-/

namespace IndependentSetDiscovery.Algorithms

variable {ι V : Type*} [LinearOrder ι] [LinearOrder V] [Inhabited V]
variable (R : V → V → Prop) [DecidableRel R] (cost : ι → V → ℚ)
variable (ops : PrefixOperations V) (threshold : ℕ → ℕ)

/-- Total explicitly represented residual entries, with one word for the budget. -/
def stateMass (s : State ι V) : ℕ := s.labels.card + totalCandidates s + 1

def instructionArity : Instruction σ → ℕ
  | .yes => 0
  | .no => 0
  | .branch children => children.length

/-- The operation tariff of one state, broken into the actual finite passes.
The factor eight pays for both ordered enumerations, cost sorting, prefix
conversion, maxima, empty/small tests and loop/control moves. -/
def nodeWork (s : State ι V) : ℕ :=
  8 + 8 * (s.labels.card + 1) ^ 2 +
  8 * (∑ i ∈ s.labels, ((s.candidates i).card + 1) ^ 2) +
  instructionArity (prefixStep R cost ops threshold s) *
    (4 * totalCandidates s + 2 * s.labels.card + 4)

/-- The sum of node tariffs on exactly the same execution tree as `run`. -/
def runWork (step : σ → Instruction σ) (charge : σ → ℕ) : ℕ → σ → ℕ
  | 0, s => charge s
  | fuel + 1, s =>
    match step s with
    | .yes => charge s
    | .no => charge s
    | .branch children => charge s + (children.map (runWork step charge fuel)).sum

theorem prefixBranches_le_candidates (s : State ι V) :
    (allPrefixBranches R cost ops threshold s).length ≤ totalCandidates s := by
  simp only [allPrefixBranches, List.length_flatMap, List.length_map, Finset.length_sort]
  rw [← List.sum_toFinset _ (s.labels.sort_nodup (· ≤ ·)), Finset.sort_toFinset]
  apply Finset.sum_le_sum
  intro i hi
  exact Finset.card_le_card (ops.subset _ _ _)

theorem stepArity_le_candidates (s : State ι V) :
    instructionArity (prefixStep R cost ops threshold s) ≤ totalCandidates s := by
  unfold prefixStep
  split_ifs with hb he hs ha
  · simp [instructionArity]
  · simp [instructionArity]
  · simp only [instructionArity, List.length_map, Finset.length_sort]
    apply Finset.single_le_sum (f := fun i => (s.candidates i).card)
    · intro _ _; omega
    · exact (Finset.mem_filter.mp ((smallLabels threshold s).min'_mem hs)).1
  · simp [instructionArity]
  · exact prefixBranches_le_candidates R cost ops threshold s

theorem candidate_card_le_mass (s : State ι V) (i : ι) (hi : i ∈ s.labels) :
    (s.candidates i).card ≤ stateMass s := by
  have h := Finset.single_le_sum (f := fun i => (s.candidates i).card)
    (fun _ _ => Nat.zero_le _) hi
  dsimp only at h
  dsimp [stateMass, totalCandidates]
  omega

theorem nodeWork_le_polynomial (s : State ι V) :
    nodeWork R cost ops threshold s ≤ 64 * (stateMass s + 1) ^ 3 := by
  have hsum : (∑ i ∈ s.labels, ((s.candidates i).card + 1) ^ 2) ≤
      s.labels.card * (stateMass s + 1) ^ 2 := by
    calc
      _ ≤ ∑ _i ∈ s.labels, (stateMass s + 1) ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        gcongr
        exact candidate_card_le_mass s i hi
      _ = _ := by simp
  have ha := stepArity_le_candidates R cost ops threshold s
  have hk : s.labels.card ≤ stateMass s := by dsimp [stateMass]; omega
  have hn : totalCandidates s ≤ stateMass s := by dsimp [stateMass]; omega
  have hsq : (s.labels.card + 1)^2 ≤ (stateMass s + 1)^2 := by gcongr
  have ha' := Nat.mul_le_mul ha
    (show 4 * totalCandidates s + 2 * s.labels.card + 4 ≤ 6 * stateMass s + 4 by omega)
  unfold nodeWork
  nlinarith [Nat.mul_le_mul_right ((stateMass s + 1)^2) hk,
    Nat.mul_le_mul_right (6 * stateMass s + 4) hn]

theorem child_mass_le (s : State ι V) (i : ι) (v : V) (hi : i ∈ s.labels) :
    stateMass (child R cost s i v) ≤ stateMass s := by
  have ht := totalCandidates_child_le R cost s i v hi
  have hk := child_rank_lt R cost s i v hi
  dsimp only [stateMass]
  omega

theorem prefixStep_mass_le (s : State ι V) (children : List (State ι V))
    (hs : prefixStep R cost ops threshold s = .branch children) :
    ∀ t ∈ children, stateMass t ≤ stateMass s := by
  unfold prefixStep at hs
  split_ifs at hs with hb he hsmall ha
  · injection hs with hc
    subst children
    intro t ht
    rcases List.mem_map.mp ht with ⟨v, hv, rfl⟩
    apply child_mass_le
    exact (Finset.mem_filter.mp ((smallLabels threshold s).min'_mem hsmall)).1
  · injection hs with hc
    subst children
    intro t ht
    rcases (mem_allPrefixBranches R cost ops threshold s t).mp ht with ⟨i, hi, v, hv, rfl⟩
    exact child_mass_le R cost s i v hi

/-- Every node charge is bounded by the root's explicit polynomial finite-set work. -/
theorem runWork_le_nodes (s : State ι V) : ∀ fuel,
    runWork (prefixStep R cost ops threshold) (nodeWork R cost ops threshold) fuel s ≤
      64 * (stateMass s + 1)^3 * (run (prefixStep R cost ops threshold) fuel s).2 := by
  intro fuel
  induction fuel generalizing s with
  | zero =>
    cases hs : prefixStep R cost ops threshold s <;>
      simpa [runWork, run, hs] using nodeWork_le_polynomial R cost ops threshold s
  | succ fuel ih =>
    cases hs : prefixStep R cost ops threshold s with
    | yes => simpa [runWork, run, hs] using nodeWork_le_polynomial R cost ops threshold s
    | no => simpa [runWork, run, hs] using nodeWork_le_polynomial R cost ops threshold s
    | branch children =>
      have hsum : (children.map (runWork (prefixStep R cost ops threshold)
          (nodeWork R cost ops threshold) fuel)).sum ≤
          64 * (stateMass s + 1)^3 *
            (children.map (fun t => (run (prefixStep R cost ops threshold) fuel t).2)).sum := by
        rw [← List.sum_map_mul_left]
        apply List.sum_le_sum
        intro t ht
        calc
          _ ≤ 64 * (stateMass t + 1)^3 * (run (prefixStep R cost ops threshold) fuel t).2 := ih t
          _ ≤ _ := by
            gcongr
            exact prefixStep_mass_le R cost ops threshold s children hs t ht
      simp only [runWork, run, hs, List.map_map, Function.comp_def]
      have hnode := nodeWork_le_polynomial R cost ops threshold s
      nlinarith

/-- Intermediate charge-schedule bound. Actual measured decision execution
is bounded by `EagerBounds.eagerDecide_cost_le`. -/
theorem decisionWork_le
    (symm : Symmetric R) (nonneg : ∀ i v, 0 ≤ cost i v)
    (positive : ∀ r, 0 < threshold r)
    (certificate : TransversalCertificate (ι := ι) R threshold)
    (k maxThreshold : ℕ) (hthreshold : ∀ r ≤ k, threshold r ≤ maxThreshold)
    (s : State ι V) (hs : s.labels.card ≤ k) :
    runWork (prefixStep R cost ops threshold) (nodeWork R cost ops threshold) s.labels.card s ≤
      64 * (stateMass s + 1)^3 * treeBound (k * maxThreshold) s.labels.card := by
  exact (runWork_le_nodes R cost ops threshold s _).trans
    (Nat.mul_le_mul_left _ (decidePrefix_cost_le R cost ops threshold symm nonneg
      positive certificate k maxThreshold hthreshold s hs))

end IndependentSetDiscovery.Algorithms
