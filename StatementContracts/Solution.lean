import IndependentSetDiscovery

/-!
Paper-facing statement contracts, authored separately from the proof implementations.
Every numbered paper conclusion has an explicit proposition below. Shared graph,
input, output, and cost-model definitions are part of the trusted statement context.
They must be reviewed and frozen together with this file.
-/
namespace ISDContracts
open IndependentSetDiscovery
open IndependentSetDiscovery.ShortestPaths
open IndependentSetDiscovery.Algorithms
open IndependentSetDiscovery.Movement
open Finset
set_option maxHeartbeats 0
set_option maxRecDepth 4096

/-- Theorem 1.2: actual optimal moves, exact failure, uniform binary work. -/
theorem paper_1_2
    {n : ℕ} (a : MatrixGraph n) (S : Finset (Fin n)) (d : ℕ)
    (hd : 2 ≤ d) (hG : BicliqueFree a.graph d d) :
    ((∀ budget : ℕ,
      (BudgetedDiscovery.decideMeasured a S d hd hG budget).1 = true ↔
        DiscoveryWithin a.graph S budget) ∧
    (∀ (_hk : 2 ≤ S.card) (budget m : ℕ),
      (BudgetedDiscovery.decideMeasured a S d hd hG budget).2 ≤
        2^(30*d*S.card*(S.card.log2+1))*(n+m+1)^25 +
        4*(n^2+1)*binaryScalarTariff
          (binaryRegisterWidth 0 0 (n^2) (binaryLength budget)) + 1)) ∧
    ((∀ out : DiscoveryResult a.graph S, (MeasuredDiscovery.solveBinary a S d hd hG).1 = some out →
      Independent a.graph out.target ∧ Movement.ValidMoves a.graph S out.moves out.target ∧
      out.target.card = S.card ∧
      (∀ T ℓ, Independent a.graph T → SlideSequence a.graph S T ℓ → out.moves.length ≤ ℓ) ∧
      out.moves.length ≤ S.card * (n - 1)) ∧
    ((MeasuredDiscovery.solveBinary a S d hd hG).1 = none ↔
      ¬ ∃ T ℓ, Independent a.graph T ∧ SlideSequence a.graph S T ℓ) ∧
    (∀ (_hk : 2 ≤ S.card) (m : ℕ),
      (MeasuredDiscovery.solveBinary a S d hd hG).2 ≤
        2^(30*d*S.card*(S.card.log2+1)) * (n+m+1)^25)) := by
  constructor
  ·
    exact ⟨fun budget => BudgetedDiscovery.decideMeasured_correct a S d hd hG budget,
      fun hk budget m => BudgetedDiscovery.decideMeasured_work a S d hd hk hG budget m⟩
  ·
    exact ⟨fun out h => MeasuredDiscovery.binary_some_spec a S d hd hG out h,
      MeasuredDiscovery.binary_none_iff a S d hd hG,
      fun hk m => MeasuredDiscovery.binary_bound a S d hd hk hG m⟩

/-- Lemma 3.1: extended-natural assignment and slide minima, including infinity. -/
theorem paper_3_1
    {V : Type*} [DecidableEq V] (G : SimpleGraph V) (S T : Finset V) :
    (⨅ f : Matching S T, ∑ s ∈ S, G.edist s (f.target s)) =
      (⨅ ℓ : {ℓ : ℕ // SlideSequence G S T ℓ}, (ℓ.val : ℕ∞)) ∧
    ((⨅ f : Matching S T, ∑ s ∈ S, G.edist s (f.target s)) = ⊤ ↔
      ¬ ∃ ℓ, SlideSequence G S T ℓ) := by
  exact ⟨assignmentDistance_eq_slideDistance G S T,
    assignmentDistance_eq_top_iff G S T⟩

/-- Corollary 3.2: the static endpoint formulation at every budget. -/
theorem paper_3_2
    {V : Type*} [DecidableEq V] (G : SimpleGraph V) (S : Finset V) (b : ℕ) :
    ((∃ T ℓ, Independent G T ∧ SlideSequence G S T ℓ ∧ ℓ ≤ b) ↔
      ∃ f : V → V, Set.InjOn f (↑S : Set V) ∧ Independent G (S.image f) ∧
        (∑ s ∈ S, G.edist s (f s)) ≤ b) ∧
    (⨅ T : {T : Finset V // Independent G T}, slideDistance G S T.val) =
      (⨅ f : {f : V → V // Set.InjOn f (↑S : Set V) ∧ Independent G (S.image f)},
        ∑ s ∈ S, G.edist s (f.val s)) := by
  exact ⟨static_endpoint_formulation (G := G), discoveryDistance_eq_staticEndpoint G S⟩

/-- Corollary 3.3: conditional transfer with its supplied-optimizer premise visible. -/
theorem paper_3_3
    {P : Type*} {n : ℕ}
    {promise : P → {n : ℕ} → MatrixGraph n → Prop}
    (solver : GenericTransfer.WeightedOptimizer P promise)
    (f : ℕ → P → ℕ) (q : ℕ)
    (hcost : ∀ {p : P} {k n : ℕ} (E : EncodedInput k n), promise p E.graphData →
      (solver.run p E).2 ≤ f k p * E.inputBits^q)
    (p : P) (a : MatrixGraph n) (S : Finset (Fin n)) (hG : promise p a) :
    (∀ out : DiscoveryResult a.graph S, (GenericTransfer.runWithTariff solver p a S hG (GenericTransfer.auxiliaryBinaryTariff n)).1 = some out →
      Independent a.graph out.target ∧ Movement.ValidMoves a.graph S out.moves out.target ∧
      out.target.card = S.card ∧
      (∀ T ℓ, Independent a.graph T → SlideSequence a.graph S T ℓ → out.moves.length ≤ ℓ) ∧
      out.moves.length ≤ S.card * (n - 1)) ∧
    ((GenericTransfer.runWithTariff solver p a S hG (GenericTransfer.auxiliaryBinaryTariff n)).1 = none ↔
      ¬ ∃ T ℓ, Independent a.graph T ∧ SlideSequence a.graph S T ℓ) ∧
    (∀ (_hf : 1 ≤ f S.card p) (m : ℕ),
      (GenericTransfer.runWithTariff solver p a S hG (GenericTransfer.auxiliaryBinaryTariff n)).2 ≤
        f S.card p * (8^q + 206*(64*257^3)) * (n+m+1)^(3*q+11)) := by
  refine ⟨?_, ?_, fun hf m => GenericTransfer.corollary_3_3_binary solver f q hcost p a S hG hf m⟩
  · intro out h
    rw [GenericTransfer.runWithTariff_value] at h
    exact GenericTransfer.run_some_spec solver p a S hG out h
  · rw [GenericTransfer.runWithTariff_value]
    exact GenericTransfer.run_none_iff solver p a S hG

/-- Theorem 4.1: a genuine independent transversal of a vertex partition; positive size. -/
theorem paper_4_1
    {ι V : Type*} [Fintype ι] [Fintype V] [DecidableEq ι] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (A : ι → Finset V)
    (hdisjoint : Pairwise (fun i j => Disjoint (A i) (A j)))
    (_hcover : ∀ v : V, ∃ i, v ∈ A i)
    (t : ℕ) (ht : 0 < t) (hsize : ∀ i, t ≤ (A i).card)
    (hcross : ∀ i, 4 * (∑ j ∈ univ.erase i, (Transversal.pairs A H.Adj i j).card) ≤
      t * (A i).card) :
    ∃ x : ι → V, (∀ i, x i ∈ A i) ∧ Function.Injective x ∧
      Pairwise (fun i j => ¬ H.Adj (x i) (x j)) := by
  obtain ⟨x,hx,hpair⟩ := Transversal.wanlessWood A H.Adj H.symm t ht hsize hcross
  refine ⟨x,hx,?_,hpair⟩
  intro i j he
  by_contra hij
  exact Finset.disjoint_left.mp (hdisjoint hij) (hx i) (he.symm ▸ hx j)

/-- Lemma 4.2: overlapping candidates and equality conflicts at arbitrary threshold. -/
theorem paper_4_2
    {ι V : Type*} [Fintype ι] [Fintype V] [DecidableEq ι] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {d t : ℕ}
    (hd : 2 ≤ d) (ht : 0 < t) (hr : 2 ≤ Fintype.card ι)
    (hG : BicliqueFree G d d) (A : ι → Finset V) (hsize : ∀ i, (A i).card = t)
    (hdensity : 4 * ((Fintype.card ι - 1 : ℕ) : ℝ) * codegreeDensity d (d-1) t < 1) :
    ∃ x : ι → V, (∀ i, x i ∈ A i) ∧
      Pairwise (fun i j => x i ≠ x j ∧ ¬ G.Adj (x i) (x j)) := by
  exact biclique_free_transversal_arbitrary_threshold G hd ht hr hG A hsize hdensity

/-- Lemma 4.3: the literal threshold expression satisfies the density inequality. -/
theorem paper_4_3
    {d r : ℕ} (hd : 2 ≤ d) (hr : 2 ≤ r) :
    balancedThreshold d r = (d-1)*(4*(r-1))^d + 4*d^2*(r-1) ∧
    (4*(r-1) : ℕ) *
      codegreeDensity d (d-1) ((d-1)*(4*(r-1))^d + 4*d^2*(r-1)) < (1 : ℝ) := by
  exact ⟨rfl, balancedThreshold_density_certificate hd hr⟩

/-- Theorem 4.4: exact rational optimization and certified binary costs. -/
theorem paper_4_4
    {k n : ℕ} (E : EncodedInput k n) (d : ℕ)
    (hd : 2 ≤ d) (hG : BicliqueFree E.graph d d) :
    (∀ budget : ℚ,
      (∃ x, (E.solveBinary d).1 = some x ∧
        E.toWeightedInstance.selectionCost x ≤ budget) ↔
      E.toWeightedInstance.Within budget) ∧
    ((∀ x, (E.solveBinary d).1 = some x →
      E.toWeightedInstance.Selection x ∧
      ∀ y, E.toWeightedInstance.Selection y →
        (∑ i, E.toWeightedInstance.cost i (x i)) ≤ (∑ i, E.toWeightedInstance.cost i (y i))) ∧
    ((E.solveBinary d).1 = none ↔ ¬ ∃ x, E.toWeightedInstance.Selection x) ∧
    (∀ (_hk : 2 ≤ k), (E.solveBinary d).2 ≤
      2^(10*d*k*(k.log2+1)) *
        (EncodedInput.measuredInputPolynomial k n E.inputBits *
          binaryScalarTariff (binaryRegisterWidth E.inputBits k n (binaryLength d)))) ∧
    (∀ (M : ℕ) (_hM : ∀ r ≤ k, balancedSearchThreshold d r ≤ M),
      (E.solveBinary d).2 ≤
        (EncodedInput.scalarWorkPolynomial E.inputBits k n *
          binaryScalarTariff (binaryRegisterWidth E.inputBits k n (binaryLength d))) * treeBound (k*M) k)) := by
  constructor
  ·
    intro budget
    constructor
    · rintro ⟨x, hx, hb⟩
      exact ⟨x, (E.solveBinary_some hd hG hx).1, hb⟩
    · rintro ⟨x, hx, hb⟩
      cases hout : (E.solveBinary d).1 with
      | none =>
        exact False.elim ((E.solveBinary_none_iff hd hG).mp hout ⟨x, hx⟩)
      | some y =>
        exact ⟨y, rfl, ((E.solveBinary_some hd hG hout).2 x hx).trans hb⟩
  ·
    refine ⟨fun _ h => E.solveBinary_some hd hG h, E.solveBinary_none_iff hd hG, ?_, ?_⟩
    · intro hk
      exact E.solveBinary_le_exp hd hk
    · intro M hM
      exact E.solveBinary_cost_le d M hM

/-- Lemma 4.5: affordable prefixes contain a witness; every cheap witness meets overbudget prefixes. -/
theorem paper_4_5
    {ι V : Type*} [Fintype ι] [Fintype V] [DecidableEq ι] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ} (hd : 2 ≤ d)
    (hG : BicliqueFree G d d) (hr : 2 ≤ Fintype.card ι)
    (A : ι → Finset V) (c : ι → V → ℚ) (B : ℚ)
    (hsize : ∀ i, balancedThreshold d (Fintype.card ι) ≤ (A i).card)
    (hc : ∀ i v, v ∈ A i → 0 ≤ c i v) :
    ((∑ i, prefixMax (c i) (cheapPrefix (c i) (A i) (balancedThreshold d (Fintype.card ι)))) ≤ B →
      ∃ x : ι → V,
        (∀ i, x i ∈ cheapPrefix (c i) (A i) (balancedThreshold d (Fintype.card ι))) ∧
        Pairwise (fun i j => x i ≠ x j ∧ ¬ G.Adj (x i) (x j)) ∧ (∑ i, c i (x i)) ≤ B) ∧
    (B < (∑ i, prefixMax (c i) (cheapPrefix (c i) (A i) (balancedThreshold d (Fintype.card ι)))) →
      ∀ x : ι → V, (∀ i, x i ∈ A i) → (∑ i, c i (x i)) ≤ B →
        ∃ i, x i ∈ cheapPrefix (c i) (A i) (balancedThreshold d (Fintype.card ι))) := by
  exact ⟨fun hB => cheap_prefix_affordable G hd hG hr A c B hsize hB,
    fun hB x hx hcost => cheap_prefix_overbudget A c _ B hc hB x hx hcost⟩

/-- Lemma 4.6: the actual decreasing-rank cheap-prefix recursive decision procedure. -/
theorem paper_4_6
    {ι V : Type*} [Fintype ι] [Fintype V] [LinearOrder ι] [LinearOrder V] [Inhabited V]
    (I : WeightedInstance ι V) [DecidableRel I.graph.Adj]
    (d : ℕ) (hd : 2 ≤ d) (hG : BicliqueFree I.graph d d) :
    (∀ s : State ι V,
      decidePrefix (Compatible I.graph) I.normalizedCost costPrefixOperations
        (balancedSearchThreshold d) s = true ↔
      Feasible (Compatible I.graph) I.normalizedCost s) ∧
    (∀ (s : State ι V) children,
      prefixStep (Compatible I.graph) I.normalizedCost costPrefixOperations
        (balancedSearchThreshold d) s = .branch children →
      children.length ≤ s.labels.card * balancedSearchThreshold d s.labels.card) := by
  exact ⟨fun s => decidePrefix_correct (Compatible I.graph) I.normalizedCost
    costPrefixOperations (balancedSearchThreshold d) (compatible_symm I.graph)
    I.normalizedCost_nonneg (balancedSearchThreshold_pos hd)
    (balanced_transversalCertificate I.graph hd hG) s,
    fun s children h => prefixStep_branching (Compatible I.graph) I.normalizedCost
      costPrefixOperations (balancedSearchThreshold d) s children h⟩

/-- Lemma 5.1: nonmonotone threshold table; local sparsity premises are expanded. -/
theorem paper_5_1
    {k n : ℕ} (E : EncodedInput k n) (hk : 2 ≤ k)
    (L : Vector ℕ (k+1)) (γ : ℕ → ℝ)
    (hpositive : ∀ r : Fin (k+1), 2 ≤ r.val → 0 < L[r])
    (hlocal : ∀ t, 0 < t → ∀ U W : Finset (Fin n), U.card = t → W.card = t →
      ((adjacencyPairs E.graph U W).card : ℝ) ≤ γ t * (t : ℝ)^2)
    (hdensity : ∀ r : Fin (k+1), 2 ≤ r.val →
      4 * ((r.val-1 : ℕ) : ℝ) * (γ L[r] + 1 / (L[r] : ℝ)) < 1) :
    (∀ budget : ℚ,
      (∃ targets, (SparseTable.solveBinaryVector E L).1 = some targets ∧
        E.toWeightedInstance.selectionCost (fun i => targets[i]) ≤ budget) ↔
      E.toWeightedInstance.Within budget) ∧
    ((∀ targets, (SparseTable.solveBinaryVector E L).1 = some targets →
      E.toWeightedInstance.Selection (fun i => targets[i]) ∧
      ∀ y, E.toWeightedInstance.Selection y →
        (∑ i, E.toWeightedInstance.cost i targets[i]) ≤ (∑ i, E.toWeightedInstance.cost i (y i))) ∧
    ((SparseTable.solveBinaryVector E L).1 = none ↔ ¬ ∃ x, E.toWeightedInstance.Selection x) ∧
    (SparseTable.solveBinaryVector E L).2 ≤
      (k * SparseTable.maxThreshold L)^k * SparseTable.inputPolynomial E.inputBits k n) := by
  constructor
  ·
    exact fun budget => SparseTable.solveBinaryVector_within_iff E hk L γ
      hpositive hlocal hdensity budget
  ·
    exact SparseTable.lemma_5_1 E hk L γ hpositive hlocal hdensity

/-- Theorem 5.2: edge-sensitive binary bound with the real exponent k/2. Both weighted and discovery outputs are included. -/
theorem paper_5_2
    {n : ℕ} (a : MatrixGraph n) (S : Finset (Fin n))
    (m : ℕ) (hG : a.graph.edgeFinset.card = m) :
    (∀ {k N : ℕ} (E : EncodedInput k N) (_hE : E.graph.edgeFinset.card = m),
      (∀ targets, (FamilyDiscovery.weightedBinaryRun (.edge m) E).1 = some targets →
        E.toWeightedInstance.Selection (fun i => targets[i]) ∧
        ∀ y, E.toWeightedInstance.Selection y →
          (∑ i, E.toWeightedInstance.cost i targets[i]) ≤ (∑ i, E.toWeightedInstance.cost i (y i))) ∧
      ((FamilyDiscovery.weightedBinaryRun (.edge m) E).1 = none ↔
        ¬ ∃ x, E.toWeightedInstance.Selection x) ∧
      (∀ (_hk : 2 ≤ k),
        (FamilyDiscovery.weightedBinaryRun (.edge m) E).2 ≤
          5*(k*edgePrefixThreshold m k)^k * FamilyDiscovery.inputPolynomial (.edge m) k N E.inputBits *
            FamilyDiscovery.coreBinaryTariff (.edge m) k N E.inputBits ∧
        (((k * edgePrefixThreshold m k)^k : ℕ) : ℝ) ≤ 2^(13*k*(k.log2+1)) * (m+1 : ℝ)^((k : ℝ)/2))) ∧
    (∀ out : DiscoveryResult a.graph S, (FamilyDiscovery.solveBinary (.edge m) a S hG).1 = some out →
      Independent a.graph out.target ∧ Movement.ValidMoves a.graph S out.moves out.target ∧
      out.target.card = S.card ∧
      (∀ T ℓ, Independent a.graph T → SlideSequence a.graph S T ℓ → out.moves.length ≤ ℓ) ∧
      out.moves.length ≤ S.card * (n - 1)) ∧
    ((FamilyDiscovery.solveBinary (.edge m) a S hG).1 = none ↔
      ¬ ∃ T ℓ, Independent a.graph T ∧ SlideSequence a.graph S T ℓ) ∧
    (∀ (_hk : 2 ≤ S.card),
      ((FamilyDiscovery.solveBinary (.edge m) a S hG).2 : ℝ) ≤
        (2 : ℝ)^64 * 2^(13*S.card*(S.card.log2+1)) *
          (m+1 : ℝ)^((S.card : ℝ)/2) * (n+m+1 : ℝ)^25) := by
  constructor
  · intro k N E hE
    refine ⟨fun targets h => FamilyDiscovery.binaryWeightedOptimizer.some_optimal (p := (.edge m)) E hE h,
      FamilyDiscovery.binaryWeightedOptimizer.none_iff (p := (.edge m)) E hE, ?_⟩
    intro hk
    exact ⟨FamilyDiscovery.weighted_binary_cost (.edge m) E hk, edge_search_factor_le_real (m := m) (k := k) (by omega)⟩
  ·
    exact ⟨fun out h => FamilyDiscovery.binary_some_spec (.edge m) a S hG out h,
      FamilyDiscovery.binary_none_iff (.edge m) a S hG,
      fun hk => FamilyDiscovery.edge_binary a S m hG hk⟩

/-- Theorem 5.3: hereditary degeneracy, preserving (a+1)^k. Both weighted and discovery outputs are included. -/
theorem paper_5_3
    {n : ℕ} (a : MatrixGraph n) (S : Finset (Fin n))
    (δ : ℕ) (hG : Degenerate a.graph δ) :
    (∀ {k N : ℕ} (E : EncodedInput k N) (_hE : Degenerate E.graph δ),
      (∀ targets, (FamilyDiscovery.weightedBinaryRun (.degeneracy δ) E).1 = some targets →
        E.toWeightedInstance.Selection (fun i => targets[i]) ∧
        ∀ y, E.toWeightedInstance.Selection y →
          (∑ i, E.toWeightedInstance.cost i targets[i]) ≤ (∑ i, E.toWeightedInstance.cost i (y i))) ∧
      ((FamilyDiscovery.weightedBinaryRun (.degeneracy δ) E).1 = none ↔
        ¬ ∃ x, E.toWeightedInstance.Selection x) ∧
      (∀ (_hk : 2 ≤ k),
        (FamilyDiscovery.weightedBinaryRun (.degeneracy δ) E).2 ≤
          5*(k*degeneracyPrefixThreshold δ k)^k * FamilyDiscovery.inputPolynomial (.degeneracy δ) k N E.inputBits *
            FamilyDiscovery.coreBinaryTariff (.degeneracy δ) k N E.inputBits ∧
        (k * degeneracyPrefixThreshold δ k)^k ≤ 2^(7*k*(k.log2+1)) * (δ+1)^k)) ∧
    (∀ out : DiscoveryResult a.graph S, (FamilyDiscovery.solveBinary (.degeneracy δ) a S hG).1 = some out →
      Independent a.graph out.target ∧ Movement.ValidMoves a.graph S out.moves out.target ∧
      out.target.card = S.card ∧
      (∀ T ℓ, Independent a.graph T → SlideSequence a.graph S T ℓ → out.moves.length ≤ ℓ) ∧
      out.moves.length ≤ S.card * (n - 1)) ∧
    ((FamilyDiscovery.solveBinary (.degeneracy δ) a S hG).1 = none ↔
      ¬ ∃ T ℓ, Independent a.graph T ∧ SlideSequence a.graph S T ℓ) ∧
    (∀ (_hk : 2 ≤ S.card) (m : ℕ),
      (FamilyDiscovery.solveBinary (.degeneracy δ) a S hG).2 ≤
        2^64 * 2^(7*S.card*(S.card.log2+1)) * (δ+1)^S.card * (n+m+1)^25) := by
  constructor
  · intro k N E hE
    refine ⟨fun targets h => FamilyDiscovery.binaryWeightedOptimizer.some_optimal (p := (.degeneracy δ)) E hE h,
      FamilyDiscovery.binaryWeightedOptimizer.none_iff (p := (.degeneracy δ)) E hE, ?_⟩
    intro hk
    exact ⟨FamilyDiscovery.weighted_binary_cost (.degeneracy δ) E hk, degeneracy_search_factor_le_exp (a := δ) (k := k) (by omega)⟩
  ·
    exact ⟨fun out h => FamilyDiscovery.binary_some_spec (.degeneracy δ) a S hG out h,
      FamilyDiscovery.binary_none_iff (.degeneracy δ) a S hG,
      fun hk m => FamilyDiscovery.degeneracy_binary a S δ hG hk m⟩

/-- Theorem 5.4: s-codegree, including s=1 and q=0. Both weighted and discovery outputs are included. -/
theorem paper_5_4
    {n : ℕ} (a : MatrixGraph n) (S : Finset (Fin n))
    (s q : ℕ) (hs : 1 ≤ s) (hG : CodegreeBound a.graph s q) :
    (∀ {k N : ℕ} (E : EncodedInput k N) (_hE : CodegreeBound E.graph s q),
      (∀ targets, (FamilyDiscovery.weightedBinaryRun (.codegree s q) E).1 = some targets →
        E.toWeightedInstance.Selection (fun i => targets[i]) ∧
        ∀ y, E.toWeightedInstance.Selection y →
          (∑ i, E.toWeightedInstance.cost i targets[i]) ≤ (∑ i, E.toWeightedInstance.cost i (y i))) ∧
      ((FamilyDiscovery.weightedBinaryRun (.codegree s q) E).1 = none ↔
        ¬ ∃ x, E.toWeightedInstance.Selection x) ∧
      (∀ (_hk : 2 ≤ k),
        (FamilyDiscovery.weightedBinaryRun (.codegree s q) E).2 ≤
          5*(k*codegreeSearchThreshold s q k)^k * FamilyDiscovery.inputPolynomial (.codegree s q) k N E.inputBits *
            FamilyDiscovery.coreBinaryTariff (.codegree s q) k N E.inputBits ∧
        (k * codegreeSearchThreshold s q k)^k ≤ 2^(10*s*k*(k.log2+1)+k*((q+1).log2+1)))) ∧
    (∀ out : DiscoveryResult a.graph S, (FamilyDiscovery.solveBinary (.codegree s q) a S ⟨hs,hG⟩).1 = some out →
      Independent a.graph out.target ∧ Movement.ValidMoves a.graph S out.moves out.target ∧
      out.target.card = S.card ∧
      (∀ T ℓ, Independent a.graph T → SlideSequence a.graph S T ℓ → out.moves.length ≤ ℓ) ∧
      out.moves.length ≤ S.card * (n - 1)) ∧
    ((FamilyDiscovery.solveBinary (.codegree s q) a S ⟨hs,hG⟩).1 = none ↔
      ¬ ∃ T ℓ, Independent a.graph T ∧ SlideSequence a.graph S T ℓ) ∧
    (∀ (_hk : 2 ≤ S.card) (m : ℕ),
      (FamilyDiscovery.solveBinary (.codegree s q) a S ⟨hs,hG⟩).2 ≤
        2^64 * 2^(10*s*S.card*(S.card.log2+1)+S.card*((q+1).log2+1)) * (n+m+1)^25) := by
  constructor
  · intro k N E hE
    refine ⟨fun targets h => FamilyDiscovery.binaryWeightedOptimizer.some_optimal (p := (.codegree s q)) E ⟨hs,hE⟩ h,
      FamilyDiscovery.binaryWeightedOptimizer.none_iff (p := (.codegree s q)) E ⟨hs,hE⟩, ?_⟩
    intro hk
    exact ⟨FamilyDiscovery.weighted_binary_cost (.codegree s q) E hk, codegree_search_factor_le_exp (s := s) (q := q) (k := k) hs (by omega)⟩
  ·
    exact ⟨fun out h => FamilyDiscovery.binary_some_spec (.codegree s q) a S ⟨hs,hG⟩ out h,
      FamilyDiscovery.binary_none_iff (.codegree s q) a S ⟨hs,hG⟩,
      fun hk m => FamilyDiscovery.codegree_binary a S s q hs hG hk m⟩

/-- Corollary 5.5: unbalanced bicliques, keeping the smaller-side exponent. Both weighted and discovery outputs are included. -/
theorem paper_5_5
    {n : ℕ} (a : MatrixGraph n) (S : Finset (Fin n))
    (s t : ℕ) (hs : 1 ≤ s) (ht : 0 < t) (hG : BicliqueFree a.graph s t) :
    (∀ {k N : ℕ} (E : EncodedInput k N) (_hE : BicliqueFree E.graph s t),
      (∀ targets, (FamilyDiscovery.weightedBinaryRun (.unbalanced s t) E).1 = some targets →
        E.toWeightedInstance.Selection (fun i => targets[i]) ∧
        ∀ y, E.toWeightedInstance.Selection y →
          (∑ i, E.toWeightedInstance.cost i targets[i]) ≤ (∑ i, E.toWeightedInstance.cost i (y i))) ∧
      ((FamilyDiscovery.weightedBinaryRun (.unbalanced s t) E).1 = none ↔
        ¬ ∃ x, E.toWeightedInstance.Selection x) ∧
      (∀ (_hk : 2 ≤ k),
        (FamilyDiscovery.weightedBinaryRun (.unbalanced s t) E).2 ≤
          5*(k*codegreeSearchThreshold s (t-1) k)^k * FamilyDiscovery.inputPolynomial (.unbalanced s t) k N E.inputBits *
            FamilyDiscovery.coreBinaryTariff (.unbalanced s t) k N E.inputBits ∧
        (k * codegreeSearchThreshold s (t-1) k)^k ≤ 2^(10*s*k*(k.log2+1)+k*(t.log2+1)))) ∧
    (∀ out : DiscoveryResult a.graph S, (FamilyDiscovery.solveBinary (.unbalanced s t) a S ⟨hs,ht,hG⟩).1 = some out →
      Independent a.graph out.target ∧ Movement.ValidMoves a.graph S out.moves out.target ∧
      out.target.card = S.card ∧
      (∀ T ℓ, Independent a.graph T → SlideSequence a.graph S T ℓ → out.moves.length ≤ ℓ) ∧
      out.moves.length ≤ S.card * (n - 1)) ∧
    ((FamilyDiscovery.solveBinary (.unbalanced s t) a S ⟨hs,ht,hG⟩).1 = none ↔
      ¬ ∃ T ℓ, Independent a.graph T ∧ SlideSequence a.graph S T ℓ) ∧
    (∀ (_hk : 2 ≤ S.card) (m : ℕ),
      (FamilyDiscovery.solveBinary (.unbalanced s t) a S ⟨hs,ht,hG⟩).2 ≤
        2^64 * 2^(10*s*S.card*(S.card.log2+1)+S.card*(t.log2+1)) * (n+m+1)^25) := by
  constructor
  · intro k N E hE
    refine ⟨fun targets h => FamilyDiscovery.binaryWeightedOptimizer.some_optimal (p := (.unbalanced s t)) E ⟨hs,ht,hE⟩ h,
      FamilyDiscovery.binaryWeightedOptimizer.none_iff (p := (.unbalanced s t)) E ⟨hs,ht,hE⟩, ?_⟩
    intro hk
    exact ⟨FamilyDiscovery.weighted_binary_cost (.unbalanced s t) E hk, by simpa only [Nat.sub_add_cancel ht] using codegree_search_factor_le_exp (s := s) (q := t-1) (k := k) hs (by omega)⟩
  ·
    exact ⟨fun out h => FamilyDiscovery.binary_some_spec (.unbalanced s t) a S ⟨hs,ht,hG⟩ out h,
      FamilyDiscovery.binary_none_iff (.unbalanced s t) a S ⟨hs,ht,hG⟩,
      fun hk m => FamilyDiscovery.unbalanced_binary a S s t hs ht hG hk m⟩

/-- Corollary 5.6: separate directed rational movement and lexicographic optimality. -/
theorem paper_5_6
    {n : ℕ} [NeZero n] (A : WeightedDirected.RationalMatrixInput n)
    (a : MatrixGraph n) (S : Finset (Fin n)) (d : ℕ)
    (hd : 2 ≤ d) (hG : BicliqueFree a.graph d d) :
    (∀ out : RationalDiscoveryResult a.graph A.relation A.weight S,
      (A.solveBinaryMeasured a S d hd hG).1 = some out →
      WeightedDirected.ValidMoves A.relation S out.moves out.target ∧
      Independent a.graph out.target ∧
      RationalSlideSequence A.relation A.weight S out.target
        (rationalMovesCost A.weight out.moves) out.moves.length ∧
      (∀ T c ℓ, Independent a.graph T →
        RationalSlideSequence A.relation A.weight S T c ℓ →
          rationalMovesCost A.weight out.moves ≤ c ∧
          (rationalMovesCost A.weight out.moves = c → out.moves.length ≤ ℓ)) ∧
      out.moves.length ≤ S.card*(n-1)) ∧
    ((A.solveBinaryMeasured a S d hd hG).1 = none ↔
      ¬ ∃ T c ℓ, Independent a.graph T ∧
        RationalSlideSequence A.relation A.weight S T c ℓ) ∧
    (∀ (_hk : 2 ≤ S.card), (A.solveBinaryMeasured a S d hd hG).2 ≤
      2^(16*d*S.card*(S.card.log2+1)) * A.directedPureInputPolynomial S.card) := by
  refine ⟨?_, A.solveBinaryMeasured_none_iff a S d hd hG,
    fun hk => A.solveBinaryMeasured_paper_bound a S d hd hk hG⟩
  intro out _h
  exact ⟨out.valid, out.optimal.1, out.optimal.2.1, out.optimal.2.2,
    by simpa using out.length_le⟩

end ISDContracts
