# Paper-to-source index

This index identifies the source declarations implementing the paper's numbered
results. It is a navigation aid, not a substitute for a clean build, axiom audit,
runtime-model review, or release verification.

All names below are under `IndependentSetDiscovery` unless another namespace is
shown. Definitions of the actual input representation and measured algorithms
are separated from mathematical specifications, so noncomputable graph-distance
specifications are not mistaken for executable preprocessing.

## Definitions and conventions

- Definition 2.1: `Configuration`, `TokenSlide`, `SlideSequence` in `Basic.lean`.
- Definition 2.2: `DiscoveryWithin` in `Basic.lean`; minimum assignment and slide
  distances in `Movement/Assignment.lean`; `OptimalDiscovery` in `Main.lean`.
- Definition 2.3: `WeightedInstance`, `.Selection`, `.selectionCost`, `.Within`,
  `.Optimal` in `Weighted.lean`.
- The paper's `ℕ` means positive integers; its `ℕ₀` means Lean's `Nat`.
  Corresponding positive-domain hypotheses are explicit in Lean. In particular,
  the `t > 0` hypothesis of the transversal criterion is part of the paper, not
  a repair to a false zero-size statement.
- The empty-label and one-label boundary cases are supported by the weighted
  implementation. Forbidden bicliques are non-induced subgraphs.

## The 16 numbered conclusions

1. **Theorem 1.2, main theorem.**
   `MeasuredDiscovery.solveBinary`, `binary_some_spec`, `binary_none_iff`,
   and `binary_bound` in `MeasuredDiscovery.lean` are the final measured
   implementation and complete binary-cost theorem. The bound is
   `2^(30*d*k*(log2 k+1))*(n+m+1)^25`, with universal constants.
   Successful `Movement.DiscoveryResult` output includes an actual move list,
   independence, replay validity, global optimality, and length proofs.
   `BudgetedDiscovery.lean` proves the binary-budget decision consequence.
   `DiscoveryAlgorithm.lean` retains a simpler executable correctness entry.

2. **Lemma 3.1, assignment-distance equality.**
   `Movement.assignmentDistance_eq_slideDistance` in
   `Movement/Assignment.lean`. The constructive first-empty-vertex exchange is
   `Movement.Routing.progress` and `Movement.Routing.realize` in
   `Movement/Routing.lean`. Infinite distances and unattained reachability are
   treated explicitly, not dropped by a connectedness assumption.

3. **Corollary 3.2, static endpoint formulation.**
   `Movement.discoveryWithin_iff_matching` and
   `Movement.static_endpoint_formulation` in `Movement/Assignment.lean` give
   the budget equivalence. `Movement.discoveryDistance_eq_staticEndpoint`
   states the literal extended-natural optimum equation (1), and
   `Movement.discoveryDistance_eq_top_iff` characterizes infinite optimum.

4. **Corollary 3.3, algorithmic transfer.**
   `GenericTransfer.runWithTariff`, `run_none_iff`, `run_some_spec`,
   `metric_inputBits_le`, `runWithTariff_cost_additive`, and
   `corollary_3_3_binary` in `GenericTransfer.lean` implement the conditional
   transfer, including input-dependent parameters. Its explicit supplied
   optimizer hypothesis is discharged by the concrete main and family drivers.
   `Movement/Reduction.lean` proves the exact metric-instance semantics;
   `ComputedMovement`, `EncodedMovement`, `PathDecoder`, and cached movement
   reconstruction provide the actual preprocessing and output.

5. **Theorem 4.1, Wanless–Wood.**
   `Transversal.wanlessWood` and `Transversal.wanlessWood_equal` in
   `Transversal/Counting.lean`. The finite counting proof is included, rather
   than assumed as a new axiom. `Transversal/Independent.lean` converts conflict
   representatives to distinct nonadjacent graph vertices.

6. **Lemma 4.2, biclique-free transversal.**
   `biclique_free_transversal_arbitrary_threshold` in `PaperStructural.lean`.
   The copied adjacency graph and equality conflicts are formalized in
   `Extremal/Basic.lean`; exact KST dependencies are proved in
   `Extremal/Counting.lean` and `Extremal/RealBounds.lean`.

7. **Lemma 4.3, exact prefix threshold.**
   `balancedThreshold` and `balancedThreshold_certificate` in
   `Extremal/Threshold.lean`, plus the literal real-valued density inequality
   `balancedThreshold_density_certificate` in `Extremal/RealBounds.lean`.

8. **Theorem 4.4, weighted algorithm.**
   Final binary endpoints are `Algorithms.EncodedInput.solveBinary`,
   `solveBinary_some`, `solveBinary_none_iff`, and `solveBinary_certified` in
   `Algorithms/EagerBitWork.lean`.
   `WeightedInstance.solveBicliqueFree_some`,
   `WeightedInstance.solveBicliqueFree_none_iff`, and
   `WeightedInstance.decideBicliqueFree_correct` in
   `Algorithms/WeightedSolver.lean`. The finite-table entrypoint is
   `Algorithms.EncodedInput.solveMeasured` (its first projection is `.solve`).
   Denominator scaling, integral binary search and witness construction appear
   in `Algorithms/Scaling.lean`, `BinarySearch.lean`, `Optimization.lean`,
   `EagerOptimization.lean`, and the measured-execution modules.

9. **Lemma 4.5, cheap-prefix dichotomy.**
   `cheap_prefix_affordable` and `cheap_prefix_overbudget` in
   `Transversal/Dichotomy.lean` expose the literal prefix-membership witness
   and universal over-budget conclusion. `Algorithms.affordable_prefixes` and
   `Algorithms.overbudget_meets_prefix` in `Algorithms/PrefixSearch.lean`
   are their residual-state algorithmic counterparts.
   Actual sorted prefixes and their cost-order properties are in
   `Transversal/CheapPrefix.lean`.

10. **Lemma 4.6, recursive correctness.**
    `Algorithms.prefixStep_correct` and `Algorithms.decidePrefix_correct` in
    `Algorithms/PrefixSearch.lean`, with legal-child semantics in
    `Algorithms/State.lean` and the decreasing-rank search driver in
    `Algorithms/SearchTree.lean`.

11. **Lemma 5.1, sparse-prefix transfer.**
    `SparseTable.lemma_5_1` in `SparseTable.lean` combines the actual finite
    threshold-vector solver, optimality/nonexistence, and complete binary bound.
    `solveBinaryVector_cost_inputBits` gives the explicit fixed input polynomial.
    Thresholds need not be monotone; the maximum is exactly over ranks 2 to k.
    Raw threshold bit scans are charged during eager preparation, before search
    uses capped finite-table lookups. `PaperStructural` and `SparseTransfer`
    prove the generic density certificate and nonmonotone maximum lemmas.

12. **Theorem 5.2, edge-sensitive XP.**
    Final measured transfer: `FamilyDiscovery.solveBinary` at `.edge m`,
    `binary_some_spec`, `binary_none_iff`, and `edge_binary` in
    `FamilyDiscovery.lean`.
    `Extensions/SparseGraphs.lean`: `card_adjacencyPairs_le_twice_edges`.
    `Extensions/ThresholdIdentities.lean`: `edgePrefixThreshold_eq_paper`.
    `Extensions/Solvers.lean`: `WeightedInstance.solveEdgeCount` and its
    correctness/failure theorems. `Extensions/DiscoveryAlgorithms.lean`:
    `solveEdgeDiscovery`, which returns actual optimal slide data.
    `Extensions/Growth.lean`: `edge_search_factor_sq_le_exp` and
    `edge_search_factor_le_real`; the latter states the real exponent `k/2`,
    including odd `k`. Capped counted preparation is in
    `Algorithms/EdgeThresholdPreparation.lean`; runtime composition is in
    `Algorithms/EagerFamilyBounds.lean`.

13. **Theorem 5.3, bounded degeneracy.**
    Final measured transfer: `FamilyDiscovery.solveBinary` at `.degeneracy a`
    and `degeneracy_binary`, with exact `(a+1)^k` factor.
    `Degenerate` is the hereditary minimum-degree definition in
    `Extensions/SparseGraphs.lean`; `.card_adjacencyPairs_le` and
    `.card_adjacencyPairs_two_sets_le` prove the required edge estimate.
    `WeightedInstance.solveDegenerate` and `solveDegenerateDiscovery` are the
    weighted and actual-movement entrypoints. The uniform factor is
    `degeneracy_search_factor_le_exp` in `Extensions/Growth.lean`.

14. **Theorem 5.4, bounded s-codegree.**
    Final measured transfer: `FamilyDiscovery.solveBinary` at `.codegree s q`
    and `codegree_binary`.
    `CodegreeBound`, `sCodegree`, and `sCodegree_le_iff` in
    `Extremal/Basic.lean`; `asymmetric_kst` in `Extremal/RealBounds.lean`;
    `codegreeThreshold_certificate` in `Extremal/Threshold.lean`.
    `WeightedInstance.solveCodegree` and `solveCodegreeDiscovery` are the
    concrete entrypoints. `codegree_search_factor_le_exp` in
    `Extremal/Growth.lean` gives the exact parameter dependence.

15. **Corollary 5.5, unbalanced bicliques.**
    Final measured transfer: `FamilyDiscovery.solveBinary` at `.unbalanced s t`
    and `unbalanced_binary`.
    `bicliqueFree_iff_codegreeBound` in `Extremal/Basic.lean`;
    `WeightedInstance.solveUnbalanced` and `solveUnbalancedDiscovery`;
    `unbalanced_search_factor_le_exp` in `Extremal/Growth.lean`.

16. **Corollary 5.6, rational directed movement on a separate graph.**
    Final retained-matrix endpoint:
    `WeightedDirected.RationalMatrixInput.solveBinaryMeasured`, with
    `solveBinaryMeasured_none_iff` and `solveBinaryMeasured_paper_bound` in
    `Extensions/DirectedBitComplexity.lean`. The complete binary bound is
    `2^(16*d*k*(log2 k+1))` times a fixed original-input polynomial.
    The executable reference-correctness entrypoint is
    `WeightedDirected.solveRationalMatrixDiscovery` in
    `Extensions/RationalDiscoveryAlgorithm.lean`, with an exact `none` iff
    nonreachability theorem. Returned `RationalDiscoveryResult` data includes
    an actual directed move list and rational lexicographic optimality.
    `Algorithms/RationalMatrixInput.lean` explicitly materializes denominator-
    cleared and scalarized weights. `Algorithms/WeightedShortestPaths.lean`,
    `WeightedPathDecoder.lean`, `WeightedCachedReduction.lean`,
    `WeightedEncodedReduction.lean` and `WeightedSelectedPaths.lean` provide
    computed, cached paths and the concrete static optimizer.
    `Extensions/DirectedRouting.lean`, `DirectedAssignment.lean`,
    `DirectedPaths.lean`, `DirectedOptimal.lean`, `DirectedReduction.lean` and
    `RationalMovement.lean` prove the semantic transfer.
    `DirectedExecutable.lean`, `DirectedPlanTable.lean` and
    `DirectedReconstructionBridge.lean` implement dual-budget cached
    reconstruction. `DirectedPreprocessing.lean` and `DirectedComplexity.lean`
    provide the final counted preprocessing and runtime-composition layer.

## Regression checks

- `Tests/Exhaustive.lean`: independent exhaustive assignment oracle over
  1,536 measured encoded inputs and 9,216 budget comparisons, plus boundary
  and full-prefix branch tests.

- `Tests/DiscoveryOutput.lean`: reference and final measured/binary unweighted moves are independently
  replayed and the independent endpoint and optimum length are checked.
- `Tests/RationalDiscovery.lean`: fractional costs `1/3` versus `1/2`,
  zero-weight directed movement with a minimum-slide secondary objective, and
  an unreachable instance with no movement arcs. Both reference and final
  retained-matrix scalar/binary drivers are tested with original-arc replay.

Historical Open Problem 1.1 and the introduction's cited context results are
not additional numbered mathematical conclusions of this paper.
