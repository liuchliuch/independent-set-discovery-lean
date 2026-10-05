import IndependentSetDiscovery.Algorithms.ShortestPaths
import IndependentSetDiscovery.Movement.Reduction

/-! # Executable graph-metric weighted instance

All source rows are materialized once in a vector. Candidate membership and
cost lookup then inspect stored path witnesses, rather than recomputing the
shortest-path recursion or consulting a noncomputable reachability predicate.
-/

namespace IndependentSetDiscovery
namespace ComputedMovement

open ShortestPaths Movement

variable {n : ℕ}

def allRows (a : MatrixGraph n) : Vector (Table n) n :=
  Vector.ofFn fun s => (shortestPaths a.graph s).1

def instanceFromRows (a : MatrixGraph n) (S : Finset (Fin n))
    (rows : Vector (Table n) n) : WeightedInstance S (Fin n) where
  graph := a.graph
  candidates := fun s => Finset.univ.filter fun v => rows[s.val][v].isSome
  cost := fun s v => ((rows[s.val][v].getD []).length : ℚ)
  nonneg := by intro _ _ _; positivity

def computedInstance (a : MatrixGraph n) (S : Finset (Fin n)) :
    WeightedInstance S (Fin n) :=
  instanceFromRows a S (allRows a)

instance (a : MatrixGraph n) (S : Finset (Fin n)) :
    DecidableRel (computedInstance a S).graph.Adj :=
  inferInstanceAs (DecidableRel a.graph.Adj)

@[simp] theorem allRows_get (a : MatrixGraph n) (s v : Fin n) :
    (allRows a)[s][v] = (shortestPaths a.graph s).1[v] := by
  simp [allRows]

theorem computed_candidates (a : MatrixGraph n) (S : Finset (Fin n))
    (s : S) (v : Fin n) :
    v ∈ (computedInstance a S).candidates s ↔ a.graph.Reachable s.val v := by
  change v ∈ Finset.univ.filter (fun v => (allRows a)[s.val][v].isSome) ↔ _
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, allRows_get]
  rw [← shortestPaths_exists_iff a.graph s.val v]
  cases h : (shortestPaths a.graph s.val).1[v] <;> simp

theorem computed_cost (a : MatrixGraph n) (S : Finset (Fin n))
    (s : S) (v : Fin n) :
    (computedInstance a S).cost s v = (a.graph.dist s.val v : ℚ) := by
  change (((allRows a)[s.val][v].getD []).length : ℚ) = _
  rw [allRows_get]
  cases h : (shortestPaths a.graph s.val).1[v] with
  | none =>
    have hr := (shortestPaths_none_iff a.graph s.val v).mp h
    simp [SimpleGraph.dist_eq_zero_of_not_reachable hr]
  | some p =>
    simpa using congrArg (fun m : ℕ => (m : ℚ))
      (shortestPaths_length_eq_dist a.graph s.val v h)

theorem computedInstance_eq_metric (a : MatrixGraph n) (S : Finset (Fin n)) :
    computedInstance a S = movementInstance a.graph S := by
  classical
  have hc : (computedInstance a S).candidates = (movementInstance a.graph S).candidates := by
    funext s
    ext v
    rw [computed_candidates, movementInstance_mem]
  have hw : (computedInstance a S).cost = (movementInstance a.graph S).cost := by
    funext s v
    exact computed_cost a S s v
  have hg : (computedInstance a S).graph = (movementInstance a.graph S).graph := rfl
  cases hI : computedInstance a S
  cases hJ : movementInstance a.graph S
  simp only [hI, hJ] at hc hw hg
  cases hg
  cases hc
  cases hw
  rfl

end ComputedMovement
end IndependentSetDiscovery
