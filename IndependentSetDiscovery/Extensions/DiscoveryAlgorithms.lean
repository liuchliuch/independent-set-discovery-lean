import IndependentSetDiscovery.DiscoveryAlgorithm
import IndependentSetDiscovery.Extensions.AlgorithmCertificates

/-! # Executable discovery algorithms for all four sparsity extensions -/

namespace IndependentSetDiscovery

open ShortestPaths Movement

variable {n : ℕ} [NeZero n]

def solveEdgeDiscovery (a : MatrixGraph n) (S : Finset (Fin n)) :
    Option (DiscoveryResult a.graph S) :=
  solveDiscoveryWithThreshold a S (edgePrefixThreshold a.graph.edgeFinset.card)
    (edgePrefixThreshold_pos _) (edgeCount_transversalCertificate a.graph)

theorem solveEdgeDiscovery_none_iff (a : MatrixGraph n) (S : Finset (Fin n)) :
    solveEdgeDiscovery a S = none ↔
      ¬ ∃ T m, Independent a.graph T ∧ SlideSequence a.graph S T m :=
  solveDiscoveryWithThreshold_none_iff a S _ _ _

def solveDegenerateDiscovery (a : MatrixGraph n) (S : Finset (Fin n)) (d : ℕ)
    (hG : Degenerate a.graph d) : Option (DiscoveryResult a.graph S) :=
  solveDiscoveryWithThreshold a S (degeneracyPrefixThreshold d)
    (degeneracyPrefixThreshold_pos _) (degeneracy_transversalCertificate a.graph hG)

theorem solveDegenerateDiscovery_none_iff (a : MatrixGraph n) (S : Finset (Fin n)) (d : ℕ)
    (hG : Degenerate a.graph d) :
    solveDegenerateDiscovery a S d hG = none ↔
      ¬ ∃ T m, Independent a.graph T ∧ SlideSequence a.graph S T m :=
  solveDiscoveryWithThreshold_none_iff a S _ _ _

def solveCodegreeDiscovery (a : MatrixGraph n) (S : Finset (Fin n)) (s q : ℕ)
    (hs : 1 ≤ s) (hG : CodegreeBound a.graph s q) : Option (DiscoveryResult a.graph S) :=
  solveDiscoveryWithThreshold a S (codegreeSearchThreshold s q)
    (codegreeSearchThreshold_pos s q) (codegree_transversalCertificate a.graph hs hG)

theorem solveCodegreeDiscovery_none_iff (a : MatrixGraph n) (S : Finset (Fin n)) (s q : ℕ)
    (hs : 1 ≤ s) (hG : CodegreeBound a.graph s q) :
    solveCodegreeDiscovery a S s q hs hG = none ↔
      ¬ ∃ T m, Independent a.graph T ∧ SlideSequence a.graph S T m :=
  solveDiscoveryWithThreshold_none_iff a S _ _ _

def solveUnbalancedDiscovery (a : MatrixGraph n) (S : Finset (Fin n)) (s t : ℕ)
    (hs : 1 ≤ s) (ht : 0 < t) (hG : BicliqueFree a.graph s t) :
    Option (DiscoveryResult a.graph S) :=
  solveDiscoveryWithThreshold a S (codegreeSearchThreshold s (t - 1))
    (codegreeSearchThreshold_pos s (t - 1)) (unbalanced_transversalCertificate a.graph hs ht hG)

theorem solveUnbalancedDiscovery_none_iff (a : MatrixGraph n) (S : Finset (Fin n)) (s t : ℕ)
    (hs : 1 ≤ s) (ht : 0 < t) (hG : BicliqueFree a.graph s t) :
    solveUnbalancedDiscovery a S s t hs ht hG = none ↔
      ¬ ∃ T m, Independent a.graph T ∧ SlideSequence a.graph S T m :=
  solveDiscoveryWithThreshold_none_iff a S _ _ _

end IndependentSetDiscovery
