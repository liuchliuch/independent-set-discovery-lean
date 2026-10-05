import IndependentSetDiscovery.Algorithms.WeightedSolver
import IndependentSetDiscovery.Extensions.AlgorithmCertificates

/-! # Exact executable weighted solvers for Theorems 5.2--5.5 -/

namespace IndependentSetDiscovery.WeightedInstance

variable {ι V : Type*} [Fintype ι] [LinearOrder ι]
  [Fintype V] [LinearOrder V] [Inhabited V]
variable (I : WeightedInstance ι V) [DecidableRel I.graph.Adj]

/-- Theorem 5.2's edge-count-sensitive optimizer. -/
def solveEdgeCount : Option (ι → V) :=
  I.solveWithThreshold (edgePrefixThreshold I.graph.edgeFinset.card)

theorem solveEdgeCount_some {x : ι → V} (hx : I.solveEdgeCount = some x) : I.Optimal x :=
  I.solveWithThreshold_some (edgePrefixThreshold_pos _)
    (edgeCount_transversalCertificate I.graph) hx

theorem solveEdgeCount_none_iff : I.solveEdgeCount = none ↔ ¬∃ x, I.Selection x :=
  I.solveWithThreshold_none_iff (edgePrefixThreshold_pos _)
    (edgeCount_transversalCertificate I.graph)

/-- Theorem 5.3's direct bounded-degeneracy optimizer. -/
def solveDegenerate (a : ℕ) : Option (ι → V) :=
  I.solveWithThreshold (degeneracyPrefixThreshold a)

theorem solveDegenerate_some {a : ℕ} (hG : Degenerate I.graph a)
    {x : ι → V} (hx : I.solveDegenerate a = some x) : I.Optimal x :=
  I.solveWithThreshold_some (degeneracyPrefixThreshold_pos a)
    (degeneracy_transversalCertificate I.graph hG) hx

theorem solveDegenerate_none_iff {a : ℕ} (hG : Degenerate I.graph a) :
    I.solveDegenerate a = none ↔ ¬∃ x, I.Selection x :=
  I.solveWithThreshold_none_iff (degeneracyPrefixThreshold_pos a)
    (degeneracy_transversalCertificate I.graph hG)

/-- Theorem 5.4's bounded-common-neighborhood optimizer. -/
def solveCodegree (s q : ℕ) : Option (ι → V) :=
  I.solveWithThreshold (codegreeSearchThreshold s q)

theorem solveCodegree_some {s q : ℕ} (hs : 1 ≤ s) (hG : CodegreeBound I.graph s q)
    {x : ι → V} (hx : I.solveCodegree s q = some x) : I.Optimal x :=
  I.solveWithThreshold_some (codegreeSearchThreshold_pos s q)
    (codegree_transversalCertificate I.graph hs hG) hx

theorem solveCodegree_none_iff {s q : ℕ} (hs : 1 ≤ s) (hG : CodegreeBound I.graph s q) :
    I.solveCodegree s q = none ↔ ¬∃ x, I.Selection x :=
  I.solveWithThreshold_none_iff (codegreeSearchThreshold_pos s q)
    (codegree_transversalCertificate I.graph hs hG)

/-- Corollary 5.5: the smaller forbidden-biclique side controls the threshold exponent. -/
def solveUnbalanced (s t : ℕ) : Option (ι → V) := I.solveCodegree s (t - 1)

theorem solveUnbalanced_some {s t : ℕ} (hs : 1 ≤ s) (ht : 0 < t)
    (hG : BicliqueFree I.graph s t)
    {x : ι → V} (hx : I.solveUnbalanced s t = some x) : I.Optimal x :=
  I.solveCodegree_some hs ((bicliqueFree_iff_codegreeBound I.graph s t ht).mp hG) hx

theorem solveUnbalanced_none_iff {s t : ℕ} (hs : 1 ≤ s) (ht : 0 < t)
    (hG : BicliqueFree I.graph s t) :
    I.solveUnbalanced s t = none ↔ ¬∃ x, I.Selection x :=
  I.solveCodegree_none_iff hs ((bicliqueFree_iff_codegreeBound I.graph s t ht).mp hG)

end IndependentSetDiscovery.WeightedInstance
