# Reconstruction cost refinement

The production reconstruction used by `reconstructOptimalSelection` is
`reconstructCached`, not the unmaterialized reference function `reconstruct`.
The input consists of explicit computed paths. Their shortest-path computation
and initial source-cache construction are accounted for separately.

## Representation and primitive operations

- Vertices are `Fin n`. A vertex comparison and a vector access are word-RAM
  operations. A finite-set membership test is charged for a linear scan of at
  most `n` vertex comparisons.
- `PlanTable` stores each target, natural budget, and actual graph walk in an
  eagerly constructed `Vector`. Dependent casts carry proofs only and erase at
  runtime. The next state never looks up a route by recursively executing the
  previous states' function-update closures.
- Walks are immutable linked data. Returning an existing suffix or copying a
  stored path reference is constant-time. Constructing a prefix or appending a
  prefix visits its cells. Computing a walk length visits all its cells.
- The bounds are conservative charged operation counts in this model, not
  processor timings or an exact count of Lean VM instructions. Integer values
  occurring in reconstruction have polynomially bounded bit lengths.

## Counted implementation

1. `scan` returns the number of predicates actually evaluated. The empty-target
   and assigned-source searches each evaluate at most `n` predicates.
2. `findExit` returns its actual number of visited walk cells. It constructs one
   prefix cell per recursive visit. The visit count is bounded by the input
   walk length, and therefore by the remaining total route budget `M`.
3. `PlanStep.work` combines these counters and an allowance of `2*n+1` for the
   finite-set replacement and assignment bookkeeping. Multiplication by
   `2*n+8` pays for the membership comparisons, cached lookups, branches, and
   walk-cell construction in these primitive requests.
4. `materializePlanWithWork` really executes a `Vector.ofFn` callback for every
   vertex. The callback `planVertexCell` evaluates its state once and returns
   that state together with `n + 12 + 4*L`, where `L` is the length of the actual
   returned path. This allowance pays for membership, fixed table operations,
   length traversal, and possible prefix copying.
5. The callback for an updated route refers only to the immediately preceding
   materialized table. At the exchanged source it may append the selected
   prefix once; the prefix length is at most the resulting path length. The
   special budget computations traverse that prefix or the selected suffix.
   Thus the four-per-cell allowance covers these operations as well as the
   length traversal used by the counter. Other entries use cached path data.
6. The materialization counter is `8*n+1` plus the sum of the counters actually
   returned by the vector callbacks. The extra allowance covers construction,
   mapping, and summation. It is not defined to be its final polynomial bound.
   Every path is traversed by the counted callback, including all `n` entries;
   off-configuration entries contain the empty walk.
7. `reconstructTable` adds the actual scan/update counter, the actual counted
   materialization result, and the recursive counter. `reconstructCached`
   additionally pays for the initial materialization.

## Kernel-checked refinements

- `scan_cost_le` and `findExit_work_le` bound the executed scans.
- `planVertex_length_le_total` bounds every materialized path by `M`.
- `materializePlanWithWork_bound` bounds the actual vector callback sum by
  `16*(n+1)*(n+M+2)`, conservatively including `n` path traversals.
- `materialized_step_cost_le` bounds one complete update by
  `reconstructionStepBudget n M = 64*(n+1)*(n+M+1)`.
- `reconstructCached_polynomial_bound` uses strict budget decrease at every
  slide. Its total bound is `(M+1)*64*(n+1)*(n+M+1)`.
- For shortest input routes, `M ≤ k*(n-1)`, including `k=0`. Hence the
  reconstruction work is polynomial in `n` and `k`.

All validity, budget-decrease, table-equivalence, and counter inequalities are
proved in Lean. The standard word-RAM costs of the listed primitive list and
array operations are the explicitly stated execution model.
