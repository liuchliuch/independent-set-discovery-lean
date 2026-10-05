import IndependentSetDiscovery.Algorithms.WeightedSolver

/-! Executable regression checks, including overlap, infeasibility and rational costs. -/
namespace IndependentSetDiscovery.Algorithms.Examples

open IndependentSetDiscovery

private def overlap : WeightedInstance (Fin 2) (Fin 3) where
  graph := ⊥
  candidates := fun _ => {0, 1}
  cost := fun i v => if v = 0 then 0 else if i = 0 then 10 else 1
  nonneg := by intros; split_ifs <;> norm_num

private instance : DecidableRel overlap.graph.Adj := inferInstanceAs (DecidableRel (⊥ : SimpleGraph (Fin 3)).Adj)

-- Expected: false, true, some [0, 1]. Equality conflicts are essential here.
#eval overlap.decideBicliqueFree 2 0
#eval overlap.decideBicliqueFree 2 1
#eval (overlap.solveBicliqueFree 2).map (fun x => List.ofFn x)

private def impossible : WeightedInstance (Fin 2) (Fin 3) where
  graph := ⊥
  candidates := fun _ => {0}
  cost := fun _ _ => 0
  nonneg := by simp

private instance : DecidableRel impossible.graph.Adj := inferInstanceAs (DecidableRel (⊥ : SimpleGraph (Fin 3)).Adj)

-- Expected: none, despite both candidate sets being nonempty.
#eval (impossible.solveBicliqueFree 2).map (fun x => List.ofFn x)

private def fractions : WeightedInstance (Fin 2) (Fin 3) where
  graph := ⊥
  candidates := fun _ => {0, 1, 2}
  cost := fun i v => if v = 0 then (1 : ℚ) / 3 else if v = 1 then
      (if i = 0 then 5 else 1) / 2 else 4
  nonneg := by intros; split_ifs <;> norm_num

private instance : DecidableRel fractions.graph.Adj := inferInstanceAs (DecidableRel (⊥ : SimpleGraph (Fin 3)).Adj)

-- Expected: some [0, 1], with exact minimum cost 5/6.
#eval (fractions.solveBicliqueFree 2).map (fun x => (List.ofFn x, fractions.selectionCost x))

private def fullPrefixes : WeightedInstance (Fin 2) (Fin 64) where
  graph := ⊥
  candidates := fun _ => Finset.univ
  cost := fun _ _ => 0
  nonneg := by simp

private instance : DecidableRel fullPrefixes.graph.Adj := inferInstanceAs (DecidableRel (⊥ : SimpleGraph (Fin 64)).Adj)

-- Expected: true in one state, then a reconstructed selection some [0, 1].
#eval fullPrefixes.decideBicliqueFree 2 0
#eval fullPrefixes.decisionNodes 2 0
#eval (fullPrefixes.solveBicliqueFree 2).map (fun x => List.ofFn x)

private def zeroLabels : WeightedInstance (Fin 0) (Fin 3) where
  graph := ⊥
  candidates := fun _ => ∅
  cost := fun _ _ => 0
  nonneg := by simp

private instance : DecidableRel zeroLabels.graph.Adj := inferInstanceAs (DecidableRel (⊥ : SimpleGraph (Fin 3)).Adj)

-- Expected: some []; the empty instance has optimum zero.
#eval (zeroLabels.solveBicliqueFree 2).map (fun x => List.ofFn x)

end IndependentSetDiscovery.Algorithms.Examples
