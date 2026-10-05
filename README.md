# Independent set discovery on biclique-free graphs

[![Lean checks](https://github.com/liuchliuch/independent-set-discovery-lean/actions/workflows/lean.yml/badge.svg)](https://github.com/liuchliuch/independent-set-discovery-lean/actions/workflows/lean.yml)

Lean 4 formalization of [*Independent Set Discovery on Biclique-Free Graphs Is Fixed-Parameter Tractable*](https://arxiv.org/abs/2609.27837v1).

The paper’s 16 numbered results: collision-free token movement, weighted independent transversals, the cheap-prefix algorithm, and sparse-graph and directed rational-cost extensions.

The concrete discovery driver returns an optimal independent target and a shortest legal slide list, or reports infeasibility. Complexity certificates use the explicit padded binary-RAM/list cost model; they do not certify Lean compiler output or wall-clock performance. Bicliques are non-induced, candidate sets may overlap, and directed arc costs may be zero.

## Build and verify

Lean **4.24.0**, Mathlib and every transitive Git dependency are pinned.
Install [elan](https://github.com/leanprover/elan), then run:

```sh
elan toolchain install leanprover/lean4:v4.24.0
lake exe cache get
lake build
python3 scripts/verify.py
```

The verification command rebuilds the complete project library, audits originating declarations and their transitive axioms, and runs the retained regressions. Pinned Mathlib caches may be reused. Do not update `lake-manifest.json` when reproducing this version.

## Statements and proofs

16 paper contracts are stated separately from their bridge proofs. The specification uses the documented concrete model definitions; the Comparator checks their declaration dependencies as well as the target types.

The [official Comparator](https://github.com/leanprover/comparator) runs in a separate Linux CI job with Landrun and the upstream systemd restriction. It compares target types and fixed declaration dependencies, enforces the axiom policy, and replays the exported solution through Lean’s default kernel. Rejection controls test the checking path. See [verification instructions](docs/VERIFICATION.md) for commands, pins and scope.

## Read the formalization

- [Result index](paper/RESULT_INDEX.md)
- [Mathematical scope](paper/SCOPE.md)
- [Discovery driver](IndependentSetDiscovery/MeasuredDiscovery.lean)
- [Statement contracts](StatementContracts/Challenge.lean)
- [Contract proofs](StatementContracts/Solution.lean)

The source distribution contains the mathematical library, statement specifications, retained tests, pinned configuration and verification tools. Generated logs, dependencies and build caches are excluded; CI publishes its reports as workflow artifacts.

No project license has been selected. The cited paper and upstream dependencies retain their own licensing terms.
