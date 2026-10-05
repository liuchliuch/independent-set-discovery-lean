import IndependentSetDiscovery.Algorithms.PrimitiveCosts
import IndependentSetDiscovery.Algorithms.PrefixSearch
import IndependentSetDiscovery.Transversal.Certificates

/-!
# Concrete eager finite-table decision machine

Candidate rows are stored in vectors. Forming a child evaluates and stores every
row immediately, so subsequent candidate access is a vector lookup, never a
nested unevaluated chain of filters. Prefix computations use measured list
programs with kernel-checked value refinements and cost bounds.
-/
namespace IndependentSetDiscovery.Algorithms

structure EagerState (k n : ℕ) where
  labels : Finset (Fin k)
  rows : Vector (Finset (Fin n)) k
  budget : ℚ

def EagerState.toState (s : EagerState k n) : State (Fin k) (Fin n) :=
  ⟨s.labels, fun i => s.rows[i], s.budget⟩

def EagerState.ofState (s : State (Fin k) (Fin n)) : EagerState k n :=
  ⟨s.labels, Vector.ofFn s.candidates, s.budget⟩

@[simp] theorem EagerState.toState_ofState (s : State (Fin k) (Fin n)) :
    (EagerState.ofState s).toState = s := by
  cases s
  simp [EagerState.ofState, EagerState.toState]

variable (R : Fin n → Fin n → Prop) [DecidableRel R] (cost : Fin k → Fin n → ℚ)

def eagerChild (s : EagerState k n) (i : Fin k) (v : Fin n) : EagerState k n :=
  EagerState.ofState (child R cost s.toState i v)

@[simp] theorem eagerChild_refinement (s : EagerState k n) (i : Fin k) (v : Fin n) :
    (eagerChild R cost s i v).toState = child R cost s.toState i v := by
  simp [eagerChild]

/-- One budget subtraction, an erase traversal, and every explicit candidate-row
filter. Four primitive operations pay for row copying, compatibility, cost
lookup and budget comparison. -/
def eagerChildWork (s : EagerState k n) : ℕ :=
  1 + s.labels.card + ∑ i : Fin k, (4 * (s.rows[i]).card + 1)

theorem eagerChildWork_le (s : EagerState k n) :
    eagerChildWork s ≤ 1 + k + k * (4*n+1) := by
  have hs : (∑ i : Fin k, (4 * (s.rows[i]).card + 1)) ≤ k*(4*n+1) := by
    calc
      _ ≤ ∑ _i : Fin k, (4*n+1) := by
        apply Finset.sum_le_sum
        intro i hi
        have : (s.rows[i]).card ≤ n := by simpa using Finset.card_le_univ (s.rows[i])
        omega
      _ = _ := by simp
  have hl : s.labels.card ≤ k := by simpa using Finset.card_le_univ s.labels
  unfold eagerChildWork
  omega

/-- Every eagerly materialized row is exactly the measured filtering program
on the stored row representation. This connects the child bill to the actual
filter loop, rather than assigning a cost from the desired runtime bound. -/
theorem eagerChild_row_trace (s : EagerState k n) (i j : Fin k) (v : Fin n)
    (xs : List (Fin n)) (hxs : (xs : Multiset (Fin n)) = (s.rows[j]).val) :
    let p := fun u => decide (R v u ∧ cost j u ≤ s.budget-cost i v)
    ((filterCounted p xs).1 : Multiset (Fin n)) = ((eagerChild R cost s i v).rows[j]).val ∧
      (filterCounted p xs).2 = (s.rows[j]).card := by
  simpa [eagerChild, EagerState.ofState, EagerState.toState, child] using
    finset_filter_refinement (s.rows[j])
      (fun u => R v u ∧ cost j u ≤ s.budget-cost i v) xs hxs

/-- Child work is the sum of the actual row scans, one vector operation per
row, one erase scan over labels, and one residual-budget subtraction. -/
theorem eagerChildWork_trace (s : EagerState k n) (i : Fin k) (v : Fin n)
    (reps : Fin k → List (Fin n))
    (hreps : ∀ j, (reps j : Multiset (Fin n)) = (s.rows[j]).val) :
    eagerChildWork s = 1 + s.labels.card + ∑ j : Fin k,
      (4*(filterCounted (fun u => decide (R v u ∧ cost j u ≤ s.budget-cost i v)) (reps j)).2+1) := by
  unfold eagerChildWork
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [(eagerChild_row_trace R cost s i j v (reps j) (hreps j)).2]

/-- Map on instructions, used to express exact executable refinement. -/
def Instruction.map (f : σ → τ) : Instruction σ → Instruction τ
  | .yes => .yes
  | .no => .no
  | .branch children => .branch (children.map f)

/-- Common control/list passes before the prefix dichotomy. -/
def eagerBaseWork (s : EagerState k n) : ℕ :=
  8 + 4*(s.labels.card+1)^2 + (k+1)*(n+3)

/-- A concrete eager implementation of the cheap-prefix node.
Every child is materialized and every prefix comes from the measured program. -/
def eagerStepCounted (threshold : ℕ → ℕ) (s : EagerState k n) : Instruction (EagerState k n) × ℕ :=
  if s.budget < 0 then (.no, 1)
  else if s.labels = ∅ then (.yes, 2)
  else if h : (smallLabels threshold s.toState).Nonempty then
    let i := (smallLabels threshold s.toState).min' h
    let vertices := (s.rows[i]).sort (· ≤ ·)
    (.branch (vertices.map fun v => eagerChild R cost s i v),
      eagerBaseWork s + 4*(s.rows[i]).card^2 + vertices.length * (eagerChildWork s + 1))
  else
    let measured := Vector.ofFn fun i : Fin k =>
      measuredPrefix (cost i) (s.rows[i]) (threshold s.labels.card)
    let total := ∑ i ∈ s.labels, (measured[i]).2.1
    let prefixWork := ∑ i : Fin k, (measured[i]).2.2
    if total ≤ s.budget then (.yes, eagerBaseWork s + prefixWork + 2*s.labels.card + 1)
    else
      let choices := (s.labels.sort (· ≤ ·)).flatMap fun i =>
        ((measured[i]).1.sort (· ≤ ·)).map fun v => eagerChild R cost s i v
      (.branch choices, eagerBaseWork s + prefixWork + 2*s.labels.card + 1 +
        4*s.labels.card^2 + (∑ i ∈ s.labels, 4*(measured[i]).1.card^2) +
        choices.length*(eagerChildWork s+1))

def eagerStep (threshold : ℕ → ℕ) (s : EagerState k n) : Instruction (EagerState k n) :=
  (eagerStepCounted R cost threshold s).1

theorem eagerStep_refinement (threshold : ℕ → ℕ) (s : EagerState k n) :
    (eagerStep R cost threshold s).map EagerState.toState =
      prefixStep R cost costPrefixOperations threshold s.toState := by
  have hpeak (i : Fin k) := (measuredPrefix_spec (cost i) (s.rows[i])
    (threshold s.labels.card)).2.1
  have hpref (i : Fin k) := (measuredPrefix_spec (cost i) (s.rows[i])
    (threshold s.labels.card)).1
  have hvec (i : Fin k) : (Vector.ofFn fun j : Fin k =>
      measuredPrefix (cost j) (s.rows[j]) (threshold s.labels.card))[i] =
      measuredPrefix (cost i) (s.rows[i]) (threshold s.labels.card) := by simp
  unfold eagerStep eagerStepCounted prefixStep
  simp only [EagerState.toState, hvec, hpeak, hpref,
    prefixTotal, prefixes, costPrefixOperations]
  split_ifs with hb he hs ha
  · rfl
  · rfl
  · simp [Instruction.map, List.map_map, eagerChild, EagerState.ofState, EagerState.toState, Function.comp_def]
  · rfl
  · simp [Instruction.map, allPrefixBranches, List.map_flatMap, List.map_map,
      prefixes, costPrefixOperations, EagerState.toState, hvec, hpref, Function.comp_def,
      eagerChild, EagerState.ofState]

end IndependentSetDiscovery.Algorithms
