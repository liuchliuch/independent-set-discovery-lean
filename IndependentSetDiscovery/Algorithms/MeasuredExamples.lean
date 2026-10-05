import IndependentSetDiscovery.Algorithms.EagerComplete
import IndependentSetDiscovery.Transversal.Certificates

namespace IndependentSetDiscovery.Algorithms.MeasuredExamples

private def exampleCost (i : Fin 2) (v : Fin 3) : ℚ :=
  if v=0 then 1/3 else if v=1 then (if i=0 then 5 else 1)/2 else 4

-- Expected: the same exact optimum [0,1] and cost 5/6, together with the
-- measured finite-table machine's nonzero work counter.
#eval (let result := optimizeEagerComplete (fun u v : Fin 3 => u ≠ v) exampleCost (balancedSearchThreshold 2) Finset.univ (Vector.ofFn fun _ : Fin 2 => Finset.univ);
  (result.1.map (fun x => (List.ofFn x, ∑ i, exampleCost i (x i))), result.2))

-- Expected: none. The shared singleton cannot be used by both labels.
#eval (let result := optimizeEagerComplete (fun u v : Fin 3 => u ≠ v) (fun _ : Fin 2 => fun _ : Fin 3 => (0 : ℚ)) (balancedSearchThreshold 2) Finset.univ (Vector.ofFn fun _ : Fin 2 => ({0} : Finset (Fin 3)));
  (result.1.map (fun x => List.ofFn x), result.2))

-- Expected: an empty optimal selection, with the complete preprocessing and
-- two small binary-search calls still included in the work counter.
#eval (let result := optimizeEagerComplete (fun u v : Fin 3 => u ≠ v) (fun _ : Fin 0 => fun _ : Fin 3 => (0 : ℚ)) (balancedSearchThreshold 2) Finset.univ (Vector.ofFn fun _ : Fin 0 => (∅ : Finset (Fin 3)));
  (result.1.map (fun x => List.ofFn x), result.2))

end IndependentSetDiscovery.Algorithms.MeasuredExamples
