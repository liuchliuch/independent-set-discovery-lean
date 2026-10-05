# Scope and correspondence

The reference is Liu and Meng, *Independent Set Discovery on Biclique-Free
Graphs Is Fixed-Parameter Tractable*, arXiv:2609.27837v1. The
[result index](RESULT_INDEX.md) maps its 16 numbered theorem, lemma, and
corollary statements to declarations. The historical Open Problem 1.1 is
resolved by Theorem 1.2; it is not a seventeenth theorem.

## Mathematical interpretation

- Configurations are finite sets. A move removes an occupied vertex and inserts
  an unoccupied neighbor. Initial and intermediate configurations need not be
  independent. `ValidMoves` additionally checks an explicit returned move list.
- Assignment and slide distances take values in extended naturals, including
  infinity. Failure means that no independent terminal configuration is
  reachable, rather than merely that a particular target cannot be reached.
- A weighted selection chooses one original candidate per label. Candidates
  may overlap; equality and adjacency are separate conflicts. Rational costs
  are exact and nonnegative on candidates. Costs outside candidates are
  normalized to zero only for implementation convenience.
- Forbidden bicliques are non-induced. Degeneracy is hereditary minimum
  degree; the codegree promise bounds every common neighborhood of an
  `s`-element set, including the vacuous case when fewer than `s` vertices exist.
- The paper uses positive natural numbers for some structural parameters.
  Their positivity assumptions are explicit in Lean. The Wanless–Wood theorem
  supports unequal block sizes, not just the equal-size application.
- The sparse-prefix interface accepts a finite vector of positive thresholds
  at ranks 2 through `k`. It uses their maximum over precisely those ranks and
  imposes no monotonicity assumption.
- In the directed extension, the feasibility graph and movement relation are
  separate. Arc weights are shared by all tokens, may be zero, and are exact
  nonnegative rationals on movement arcs. Optimality compares all legal
  sequences lexicographically by total original rational cost and slide count.

Some statements are stronger than the paper's domain restrictions. For
example, the assignment-distance identity does not require equal cardinality
as a premise: unequal-cardinality configurations have infinite distance. The
unbalanced solver does not need `s ≤ t`; specializing to that inequality gives
the paper's smaller-side bound. The directed implementation's nonempty-vertex
instance is automatic on the paper's `k ≥ 2` domain.

## Algorithms and complexity

The public measured endpoints are the finite-table weighted optimizer,
`MeasuredDiscovery`, `FamilyDiscovery`, `SparseTable`, and
`WeightedDirected.RationalMatrixInput.solveBinaryMeasured`.
Successful discovery outputs include actual legal moves, endpoint
independence, global optimality, and the bound `k*(n-1)` on output length.
The main budgeted consequence compares the optimum with a binary budget;
it does not perform a loop of length equal to the budget's numeric value.

The implementation follows the paper's proof while choosing explicit
representations and equivalent algorithms:

- Vertices and labels are finite indices; graph, cost, and incidence data are
  dense vectors. Converting standard explicit sparse input to this
  representation has polynomial overhead.
- A finite shortest-path dynamic program replaces breadth-first search. This
  changes the polynomial factor, not the parameter dependence.
- The decision proof uses residual-completion semantics. It proves correctness
  for arbitrary residual states; the full partial assignment need not be
  stored as a separate search-state field.
- Candidate rows, capped thresholds, selected targets, and reconstruction
  paths are materialized. Cheap-prefix certificates do not execute a
  nonconstructive transversal choice; self-reduction recovers a witness.
- Rational optimization clears denominators and searches an integer interval
  logarithmically. Scalarization in the directed proof is justified with the
  bounded secondary coordinate of simple-path assignments, not arbitrary
  unbounded walks.

The complexity statements use an explicit padded binary-RAM/list cost model.
Measured source programs count scalar, table, and list operations. Arithmetic
operand bounds justify a uniform polynomial bit tariff. Cost counters are
analysis instrumentation; evaluating or printing those counters is not itself
included in the algorithm being analyzed. These are not wall-clock bounds or
a verification of Lean's compiler-generated instructions.

The final bounds retain the paper's parameter dependence: balanced bicliques
give `2^(O(d*k*log k))`; edge count gives the real exponent `(m+1)^(k/2)`, also
for odd `k`; degeneracy gives exactly `(a+1)^k`; and codegree/unbalanced
bicliques retain the smaller-side exponent. Explicit fixed-degree input
polynomials and constants replace asymptotic notation. Input-bit measures and
parameter-reading charges are stated by the respective bound, rather than
being an implicit unit-cost convention for arbitrarily large integers.

Corollary 3.3 is conditional, exactly as in the paper: its supplied weighted
optimizer must satisfy correctness and a measured cost contract. The concrete
main, family, and directed algorithms instantiate an implemented optimizer;
they do not assume an efficient optimization oracle. Structural graph promises
are erased proof arguments, not promise-recognition algorithms.

## What verification establishes

The development proves the Kővári–Sós–Turán estimates and Wanless–Wood counting
criterion it uses. They are not additional axioms. The allowed foundational
axioms are `propext`, `Classical.choice`, and `Quot.sound`.

A clean Lean build checks proofs of their formal statements. Axiom auditing
checks their trusted dependencies. Executable regressions independently replay
small returned solutions. Paper-contract comparison checks agreement between
the explicitly written challenge statements and proof adapters. These checks
serve different purposes: none mechanically determines whether natural-language
mathematics was translated correctly. The definitions, domains, output
quantifiers, and complexity scope therefore also require the paper-to-source
review summarized here. Reproduction commands are in [verification instructions](../docs/VERIFICATION.md).

`StatementContracts/Challenge.lean` contains intentional specification holes
for the comparator. It is not imported by the proof library or counted as
proved mathematics. `StatementContracts/Solution.lean` must discharge those
statements without holes and is included in the proof audit.
