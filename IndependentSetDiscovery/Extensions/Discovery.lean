import IndependentSetDiscovery.Main
import IndependentSetDiscovery.Extensions.Solvers
import IndependentSetDiscovery.Extensions.RationalMovement

/-! # Discovery and rational directed-movement extension entrypoints -/

namespace IndependentSetDiscovery

open Movement

variable {V : Type*} [Fintype V] [LinearOrder V] [Inhabited V]
section Undirected

variable (G : SimpleGraph V) (S : Finset V) [DecidableRel G.Adj]
local instance movementGraphDecidable : DecidableRel (movementInstance G S).graph.Adj := by
  change DecidableRel G.Adj
  infer_instance

theorem edge_solution_gives_optimal_discovery {x : S → V}
    (hx : (movementInstance G S).solveEdgeCount = some x) :
    ∃ T n, OptimalDiscovery G S T n ∧ n ≤ S.card * (Fintype.card V - 1) := by
  obtain ⟨T, n, hT, hs, _, hb, hm⟩ := optimal_selection_realizes_discovery
    ((movementInstance G S).solveEdgeCount_some hx)
  exact ⟨T, n, ⟨hs.card_eq, hT, hs, hm⟩, hb⟩

theorem edge_failure_iff_no_discovery :
    (movementInstance G S).solveEdgeCount = none ↔
      ¬ ∃ T n, Independent G T ∧ SlideSequence G S T n :=
  (movementInstance G S).solveEdgeCount_none_iff.trans (no_selection_iff_unreachable G S)

theorem degeneracy_solution_gives_optimal_discovery {a : ℕ} (hG : Degenerate G a)
    {x : S → V} (hx : (movementInstance G S).solveDegenerate a = some x) :
    ∃ T n, OptimalDiscovery G S T n ∧ n ≤ S.card * (Fintype.card V - 1) := by
  have hg : Degenerate (movementInstance G S).graph a := by simpa [movementInstance] using hG
  obtain ⟨T, n, hT, hs, _, hb, hm⟩ := optimal_selection_realizes_discovery
    ((movementInstance G S).solveDegenerate_some hg hx)
  exact ⟨T, n, ⟨hs.card_eq, hT, hs, hm⟩, hb⟩

theorem degeneracy_failure_iff_no_discovery {a : ℕ} (hG : Degenerate G a) :
    (movementInstance G S).solveDegenerate a = none ↔
      ¬ ∃ T n, Independent G T ∧ SlideSequence G S T n := by
  have hg : Degenerate (movementInstance G S).graph a := by simpa [movementInstance] using hG
  exact ((movementInstance G S).solveDegenerate_none_iff hg).trans
    (no_selection_iff_unreachable G S)

theorem codegree_solution_gives_optimal_discovery {s q : ℕ} (hs : 1 ≤ s)
    (hG : CodegreeBound G s q) {x : S → V}
    (hx : (movementInstance G S).solveCodegree s q = some x) :
    ∃ T n, OptimalDiscovery G S T n ∧ n ≤ S.card * (Fintype.card V - 1) := by
  have hg : CodegreeBound (movementInstance G S).graph s q := by
    simpa [movementInstance] using hG
  obtain ⟨T, n, hT, hseq, _, hb, hm⟩ := optimal_selection_realizes_discovery
    ((movementInstance G S).solveCodegree_some hs hg hx)
  exact ⟨T, n, ⟨hseq.card_eq, hT, hseq, hm⟩, hb⟩

theorem codegree_failure_iff_no_discovery {s q : ℕ} (hs : 1 ≤ s) (hG : CodegreeBound G s q) :
    (movementInstance G S).solveCodegree s q = none ↔
      ¬ ∃ T n, Independent G T ∧ SlideSequence G S T n := by
  have hg : CodegreeBound (movementInstance G S).graph s q := by
    simpa [movementInstance] using hG
  exact ((movementInstance G S).solveCodegree_none_iff hs hg).trans
    (no_selection_iff_unreachable G S)

theorem unbalanced_solution_gives_optimal_discovery {s t : ℕ} (hs : 1 ≤ s) (ht : 0 < t)
    (hG : BicliqueFree G s t) {x : S → V}
    (hx : (movementInstance G S).solveUnbalanced s t = some x) :
    ∃ T n, OptimalDiscovery G S T n ∧ n ≤ S.card * (Fintype.card V - 1) :=
  codegree_solution_gives_optimal_discovery G S hs
    ((bicliqueFree_iff_codegreeBound G s t ht).mp hG) hx

theorem unbalanced_failure_iff_no_discovery {s t : ℕ} (hs : 1 ≤ s) (ht : 0 < t)
    (hG : BicliqueFree G s t) :
    (movementInstance G S).solveUnbalanced s t = none ↔
      ¬ ∃ T n, Independent G T ∧ SlideSequence G S T n :=
  codegree_failure_iff_no_discovery G S hs
    ((bicliqueFree_iff_codegreeBound G s t ht).mp hG)

end Undirected

namespace WeightedDirected

variable (Gf : SimpleGraph V) (D : V → V → Prop) [DecidableRel D] (w : V → V → ℚ)

noncomputable def rationalMovementInstance (S : Finset V) : WeightedInstance S V :=
  WeightedDirected.movementInstance Gf D
    (fun u v => scalarizationBase S.card (Fintype.card V) * integerArcWeight D w u v + 1) S

theorem rational_solution_gives_lex_optimal {d : ℕ} (hd : 2 ≤ d)
    (hG : BicliqueFree Gf d d) (hnonneg : ∀ u v, D u v → 0 ≤ w u v)
    {S : Finset V} {x : S → V}
    [DecidableRel (rationalMovementInstance Gf D w S).graph.Adj]
    (hx : (rationalMovementInstance Gf D w S).solveBicliqueFree d = some x) :
    ∃ T c n, RationalLexOptimal Gf D w S T c n ∧ n ≤ S.card * (Fintype.card V - 1) := by
  have hg : BicliqueFree (rationalMovementInstance Gf D w S).graph d d := by
    simpa [rationalMovementInstance, WeightedDirected.movementInstance] using hG
  exact rational_optimal_selection_realizes_lex D w Gf hnonneg
    ((rationalMovementInstance Gf D w S).solveBicliqueFree_some hd hg hx)

theorem rational_no_selection_iff_unreachable (hnonneg : ∀ u v, D u v → 0 ≤ w u v)
    (S : Finset V) :
    (¬ ∃ x, (rationalMovementInstance Gf D w S).Selection x) ↔
      ¬ ∃ T c n, Independent Gf T ∧ RationalSlideSequence D w S T c n := by
  constructor
  · intro hn ⟨T, c, n, hT, hs⟩
    obtain ⟨a, ha, _⟩ := hs.integerize (integerArcWeight_cast D w hnonneg)
    obtain ⟨r, _⟩ := routing_of_directedSlideSequence
      (ha.scalarize (scalarizationBase S.card (Fintype.card V)))
    obtain ⟨x, hx, _⟩ := selection_of_routing hT r
    exact hn ⟨x, hx⟩
  · intro hn ⟨x, hx⟩
    obtain ⟨T, hT, r, _⟩ := routing_of_selection hx
    obtain ⟨a, n, _, hs⟩ := scalarized_routing_realize
      (w := integerArcWeight D w) (scalarizationBase S.card (Fintype.card V)) r
    obtain ⟨c, hc, _⟩ := hs.rationalize (integerArcWeight_cast D w hnonneg)
    exact hn ⟨T, c, n, hT, hc⟩

theorem rational_failure_iff_unreachable {d : ℕ} (hd : 2 ≤ d)
    (hG : BicliqueFree Gf d d) (hnonneg : ∀ u v, D u v → 0 ≤ w u v)
    (S : Finset V) [DecidableRel (rationalMovementInstance Gf D w S).graph.Adj] :
    (rationalMovementInstance Gf D w S).solveBicliqueFree d = none ↔
      ¬ ∃ T c n, Independent Gf T ∧ RationalSlideSequence D w S T c n := by
  have hg : BicliqueFree (rationalMovementInstance Gf D w S).graph d d := by
    simpa [rationalMovementInstance, WeightedDirected.movementInstance] using hG
  exact ((rationalMovementInstance Gf D w S).solveBicliqueFree_none_iff hd hg).trans
    (rational_no_selection_iff_unreachable Gf D w hnonneg S)

end WeightedDirected
end IndependentSetDiscovery
