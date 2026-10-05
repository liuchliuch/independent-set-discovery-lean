import IndependentSetDiscovery.GenericTransfer
import IndependentSetDiscovery.Algorithms.EncodedBounds
import IndependentSetDiscovery.Extensions.AlgorithmCertificates

/-!
# Concrete measured discovery algorithms for Theorems 5.2--5.5

The conditional optimizer of Corollary 3.3 is instantiated here with the
actual capped-threshold, finite-table weighted solver. The only promises are
the graph hypotheses in the paper; there is no optimizer or operation oracle.
-/
namespace IndependentSetDiscovery.FamilyDiscovery

open ShortestPaths Algorithms Movement GenericTransfer

/-- The four concrete structural bounds used by the paper. -/
inductive Family where
  | edge (m : ℕ)
  | degeneracy (a : ℕ)
  | codegree (s q : ℕ)
  | unbalanced (s t : ℕ)

def Family.threshold : Family → ℕ → ℕ
  | .edge m => edgePrefixThreshold m
  | .degeneracy a => degeneracyPrefixThreshold a
  | .codegree s q => codegreeSearchThreshold s q
  | .unbalanced s t => codegreeSearchThreshold s (t-1)

def Family.prepare (family : Family) (k n : ℕ) : Vector ℕ (k+1) × ℕ :=
  match family with
  | .edge m => ThresholdPreparation.edgeTable k n m
  | .degeneracy a => ThresholdPreparation.degeneracyTable k n a
  | .codegree s q => ThresholdPreparation.codegreeTable k n s q
  | .unbalanced s t => ThresholdPreparation.codegreeTable k n s (t-1)

def Family.edgeParameter : Family → ℕ
  | .edge m => m
  | _ => 0

def Family.promise (family : Family) {n : ℕ} (a : MatrixGraph n) : Prop :=
  match family with
  | .edge m => a.graph.edgeFinset.card = m
  | .degeneracy d => Degenerate a.graph d
  | .codegree s q => 1 ≤ s ∧ CodegreeBound a.graph s q
  | .unbalanced s t => 1 ≤ s ∧ 0 < t ∧ BicliqueFree a.graph s t

theorem Family.positive (family : Family) (r : ℕ) : 0 < family.threshold r := by
  cases family with
  | edge m => exact edgePrefixThreshold_pos m r
  | degeneracy a => exact degeneracyPrefixThreshold_pos a r
  | codegree s q => exact codegreeSearchThreshold_pos s q r
  | unbalanced s t => exact codegreeSearchThreshold_pos s (t-1) r

theorem Family.monotone (family : Family) : Monotone family.threshold := by
  cases family with
  | edge m => exact edgePrefixThreshold_mono m
  | degeneracy a => exact degeneracyPrefixThreshold_mono a
  | codegree s q => exact codegreeSearchThreshold_mono s q
  | unbalanced s t => exact codegreeSearchThreshold_mono s (t-1)

theorem Family.prepared_value (family : Family) (k n : ℕ) (r : Fin (k+1)) :
    (family.prepare k n).1[r] = min (n+1) (family.threshold r) := by
  cases family with
  | edge m => exact (ThresholdPreparation.edgeTable_spec k n m).1 r
  | degeneracy a => exact (ThresholdPreparation.degeneracyTable_spec k n a).1 r
  | codegree s q => exact (ThresholdPreparation.codegreeTable_spec k n s q).1 r
  | unbalanced s t => exact (ThresholdPreparation.codegreeTable_spec k n s (t-1)).1 r

/-- A single input polynomial covers all finite threshold producers. -/
def preparationBound (family : Family) (k n : ℕ) : ℕ :=
  (k+1)*(144*family.edgeParameter*k+6*(n+1)+41)

theorem Family.prepared_work (family : Family) (k n : ℕ) :
    (family.prepare k n).2 ≤ preparationBound family k n := by
  cases family with
  | edge m =>
    have h := (ThresholdPreparation.edgeTable_spec k n m).2
    unfold Family.prepare preparationBound Family.edgeParameter
    nlinarith
  | degeneracy a =>
    have h := (ThresholdPreparation.degeneracyTable_spec k n a).2
    unfold Family.prepare preparationBound Family.edgeParameter
    nlinarith
  | codegree s q =>
    simpa [Family.prepare, preparationBound, Family.edgeParameter] using
      (ThresholdPreparation.codegreeTable_spec k n s q).2
  | unbalanced s t =>
    simpa [Family.prepare, preparationBound, Family.edgeParameter] using
      (ThresholdPreparation.codegreeTable_spec k n s (t-1)).2

/-- The zero-vertex branch needs no inhabitant. A positive candidate-size
requirement on a nonempty label set is already impossible there. -/
theorem Family.certificate (family : Family) {k n : ℕ} (a : MatrixGraph n)
    (hG : family.promise a) :
    TransversalCertificate (ι := Fin k) (Compatible a.graph) family.threshold := by
  by_cases hn : n = 0
  · subst n
    intro L A hL hsize
    obtain ⟨i, hi⟩ := hL
    have he : A i = ∅ := by ext v; exact Fin.elim0 v
    have hp := family.positive L.card
    have hs := hsize i hi
    rw [he, Finset.card_empty] at hs
    omega
  · letI : NeZero n := ⟨hn⟩
    cases family with
    | edge m =>
      have h := edgeCount_transversalCertificate (ι := Fin k) a.graph
      change a.graph.edgeFinset.card = m at hG
      change TransversalCertificate (Compatible a.graph) (edgePrefixThreshold m)
      rw [← hG]
      exact h
    | degeneracy d => exact degeneracy_transversalCertificate a.graph hG
    | codegree s q => exact codegree_transversalCertificate a.graph hG.1 hG.2
    | unbalanced s t => exact unbalanced_transversalCertificate a.graph hG.1 hG.2.1 hG.2.2

/-- This is a concrete implementation, not a supplied correctness/cost premise. -/
def weightedOptimizer : WeightedOptimizer Family Family.promise where
  run := fun family {k n} E => E.solveUsingPreparationVector (fun _ => family.prepare k n)
  some_optimal := by
    intro family k n E hG targets h
    exact E.solveUsingPreparationVector_some family.threshold _
      (family.prepared_value k n) family.positive (family.certificate E.graphData hG) h
  none_iff := by
    intro family k n E hG
    exact E.solveUsingPreparationVector_none_iff family.threshold _
      (family.prepared_value k n) family.positive (family.certificate E.graphData hG)

/-- Actual target, shortest slide list, and entire primitive-operation count. -/
def solve (family : Family) {n : ℕ} (a : MatrixGraph n) (S : Finset (Fin n))
    (hG : family.promise a) : Option (DiscoveryResult a.graph S) × ℕ :=
  GenericTransfer.run weightedOptimizer family a S hG

theorem none_iff (family : Family) {n : ℕ} (a : MatrixGraph n) (S : Finset (Fin n))
    (hG : family.promise a) :
    (solve family a S hG).1 = none ↔
      ¬ ∃ T m, Independent a.graph T ∧ SlideSequence a.graph S T m :=
  GenericTransfer.run_none_iff weightedOptimizer family a S hG

theorem some_spec (family : Family) {n : ℕ} (a : MatrixGraph n) (S : Finset (Fin n))
    (hG : family.promise a) (out : DiscoveryResult a.graph S)
    (hout : (solve family a S hG).1 = some out) :
    Independent a.graph out.target ∧ ValidMoves a.graph S out.moves out.target ∧
    out.target.card = S.card ∧
    (∀ T m, Independent a.graph T → SlideSequence a.graph S T m → out.moves.length ≤ m) ∧
    out.moves.length ≤ S.card*(n-1) :=
  GenericTransfer.run_some_spec weightedOptimizer family a S hG out hout

def Family.treeFactor (family : Family) (k : ℕ) : ℕ := (k*family.threshold k)^k

theorem Family.treeFactor_pos (family : Family) {k : ℕ} (hk : 2 ≤ k) :
    1 ≤ family.treeFactor k := by
  have hp := family.positive k
  exact Nat.one_le_pow _ _ (by nlinarith)

def inputPolynomial (family : Family) (k n B : ℕ) : ℕ :=
  8*eagerInputPolynomial k n B + preparationBound family k n +
    5*k*(n+1)+k*(k+2)+2

theorem runPreparedVector_cost (family : Family) {k n : ℕ} [NeZero n]
    (E : EncodedInput k n) (hk : 2 ≤ k) :
    (E.runPreparedVector (family.prepare k n).1).2 ≤
      5*k*(n+1)+8*(eagerInputPolynomial k n E.inputBits*family.treeFactor k)+k*(k+2) := by
  have hc := eagerComplete_cached_le_factor (Compatible E.graph) E.normalizedCost
    family.threshold family.positive family.monotone (family.prepare k n).1
    (family.prepared_value k n) hk Finset.univ E.candidateTableCounted.1
  have hn : numericSize Finset.univ (fun i => E.candidateTableCounted.1[i])
      E.normalizedCost ≤ E.inputBits := by
    rw [E.candidateTableCounted_value]
    exact E.normalized_numericSize_le
  have hp : eagerInputPolynomial k n
      (numericSize Finset.univ (fun i => E.candidateTableCounted.1[i]) E.normalizedCost) ≤
        eagerInputPolynomial k n E.inputBits := by
    unfold eagerInputPolynomial
    gcongr
  have hb := hc.trans (Nat.mul_le_mul_right _ hp)
  unfold EncodedInput.runPreparedVector
  dsimp only
  rw [E.candidateTableCounted_work]
  split_ifs <;> dsimp only [Family.treeFactor] <;>
    nlinarith only [hb, Nat.zero_le (k*(k+2))]

theorem weighted_cost (family : Family) {k n : ℕ} (E : EncodedInput k n) (hk : 2 ≤ k) :
    (weightedOptimizer.run family E).2 ≤ family.treeFactor k*inputPolynomial family k n E.inputBits := by
  have hk0 : k ≠ 0 := by omega
  have hf := family.treeFactor_pos hk
  have hpoly : 2 ≤ inputPolynomial family k n E.inputBits := by
    unfold inputPolynomial; omega
  by_cases hn : n = 0
  · simp only [weightedOptimizer, EncodedInput.solveUsingPreparationVector, dif_neg hk0, dif_pos hn]
    exact hpoly.trans (Nat.le_mul_of_pos_left _ hf)
  · letI : NeZero n := ⟨hn⟩
    have hc := runPreparedVector_cost family E hk
    have hp := family.prepared_work k n
    have hrest := Nat.mul_le_mul_right
      (preparationBound family k n+5*k*(n+1)+k*(k+2)+2) hf
    simp only [weightedOptimizer, EncodedInput.solveUsingPreparationVector, dif_neg hk0, dif_neg hn]
    unfold inputPolynomial
    nlinarith only [hc, hp, hrest]

/-- A graph-size polynomial with fixed universal degree, including edge-threshold
preparation. The edge parameter contributes to `n+m`, not to the exponent. -/
theorem inputPolynomial_graph_bound (family : Family) (k n B : ℕ)
    (hkn : k ≤ n) (hB : B ≤ 8*(n+1)^3) :
    inputPolynomial family k n B ≤ 2^18*(n+family.edgeParameter+1)^7 := by
  let N := n+family.edgeParameter+1
  have hn : n+1 ≤ N := by dsimp [N]; omega
  have hk : k+1 ≤ N := by omega
  have hm : family.edgeParameter ≤ N := by dsimp [N]; omega
  have hN : 1 ≤ N := by omega
  have h13 : 1 ≤ N^3 := Nat.one_le_pow _ _ hN
  have h23 : N^2 ≤ N^3 := Nat.pow_le_pow_right hN (by omega)
  have h27 : N^2 ≤ N^7 := Nat.pow_le_pow_right hN (by omega)
  have h37 : N^3 ≤ N^7 := Nat.pow_le_pow_right hN (by omega)
  have h17 : 1 ≤ N^7 := Nat.one_le_pow _ _ hN
  have hB' : B ≤ 8*N^3 := hB.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hn 3))
  have hprod : (k+1)*(n+1) ≤ N^2 := by simpa [pow_two] using Nat.mul_le_mul hk hn
  have hbase : 6*B+6+(k+1)*(n+1) ≤ 55*N^3 := by omega
  have hcore : eagerInputPolynomial k n B ≤ 14080*N^7 := by
    unfold eagerInputPolynomial
    calc
      _ ≤ (55*N^3)*256*N^2*N^2 := by gcongr
      _ = _ := by ring
  have hmk : family.edgeParameter*k ≤ N^2 := by
    simpa [pow_two] using Nat.mul_le_mul hm (show k ≤ N by omega)
  have hN2 : N ≤ N^2 := Nat.le_self_pow (by decide) N
  have hprep : preparationBound family k n ≤ 191*N^3 := by
    unfold preparationBound
    calc
      _ ≤ N*(191*N^2) := by
        apply Nat.mul_le_mul hk
        nlinarith
      _ = _ := by ring
  have hc : 5*k*(n+1) ≤ 5*N^2 := by nlinarith only [hprod]
  have ho : k*(k+2) ≤ 2*N^2 := by nlinarith only [hk, Nat.zero_le ((N-k-1)^2)]
  unfold inputPolynomial
  change _ ≤ 2^18*N^7
  norm_num
  nlinarith only [hcore, hprep, hc, ho, h27, h37, h17]

theorem ram_tree_bound (family : Family) {n : ℕ} (a : MatrixGraph n)
    (S : Finset (Fin n)) (hG : family.promise a) (hk : 2 ≤ S.card) :
    (solve family a S hG).2 ≤
      2^19*family.treeFactor S.card*(n+family.edgeParameter+1)^7 := by
  have hc := weighted_cost family (GenericTransfer.prepare a S).1 hk
  have hb : (GenericTransfer.prepare a S).1.inputBits ≤ 8*(n+1)^3 := by
    rw [prepare_value]; exact metric_inputBits_le a S
  have hkn : S.card ≤ n := by simpa using Finset.card_le_univ S
  have hp := inputPolynomial_graph_bound family S.card n _ hkn hb
  have hs := hc.trans (Nat.mul_le_mul_left _ hp)
  have ha := run_cost_additive weightedOptimizer family a S hG
  have hf := family.treeFactor_pos hk
  have h57 : (n+1)^5 ≤ (n+family.edgeParameter+1)^7 :=
    (Nat.pow_le_pow_left (by omega) 5).trans (Nat.pow_le_pow_right (by omega) (by omega))
  have haux : 206*(n+1)^5 ≤ 206*family.treeFactor S.card*(n+family.edgeParameter+1)^7 := by
    have h := Nat.mul_le_mul hf h57
    nlinarith only [h]
  change (solve family a S hG).2 ≤ _ at ha
  norm_num at hs ⊢
  nlinarith only [ha, hs, haux]

/-- Theorem 5.3 with exactly `(a+1)^k` dependence. -/
theorem degeneracy_ram {n : ℕ} (a : MatrixGraph n) (S : Finset (Fin n))
    (d : ℕ) (hG : Degenerate a.graph d) (hk : 2 ≤ S.card) (m : ℕ) :
    (solve (.degeneracy d) a S hG).2 ≤
      2^19*2^(7*S.card*(S.card.log2+1))*(d+1)^S.card*(n+m+1)^7 := by
  have hr := ram_tree_bound (.degeneracy d) a S hG hk
  have hf := degeneracy_search_factor_le_exp (a := d) (k := S.card) (by omega)
  calc
    _ ≤ 2^19*((2^(7*S.card*(S.card.log2+1)))*(d+1)^S.card)*(n+1)^7 := by
      apply hr.trans
      simpa only [Family.treeFactor, Family.threshold, Family.edgeParameter, Nat.add_zero] using
        Nat.mul_le_mul_right ((n+1)^7) (Nat.mul_le_mul_left (2^19) hf)
    _ ≤ _ := by
      calc
        _ = (2^19*2^(7*S.card*(S.card.log2+1))*(d+1)^S.card)*(n+1)^7 := by ring
        _ ≤ _ := Nat.mul_le_mul_left _
          (Nat.pow_le_pow_left (show n+1 ≤ n+m+1 by omega) 7)

/-- Theorem 5.4, uniform in the supplied codegree parameters. -/
theorem codegree_ram {n : ℕ} (a : MatrixGraph n) (S : Finset (Fin n))
    (s q : ℕ) (hs : 1 ≤ s) (hG : CodegreeBound a.graph s q)
    (hk : 2 ≤ S.card) (m : ℕ) :
    (solve (.codegree s q) a S ⟨hs,hG⟩).2 ≤
      2^19*2^(10*s*S.card*(S.card.log2+1)+S.card*((q+1).log2+1))*(n+m+1)^7 := by
  have hr := ram_tree_bound (.codegree s q) a S ⟨hs,hG⟩ hk
  have hf := codegree_search_factor_le_exp (s := s) (q := q) (k := S.card) hs (by omega)
  calc
    _ ≤ 2^19*2^(10*s*S.card*(S.card.log2+1)+S.card*((q+1).log2+1))*(n+1)^7 := by
      apply hr.trans
      simpa only [Family.treeFactor, Family.threshold, Family.edgeParameter, Nat.add_zero, codegreeSearchThreshold] using
        Nat.mul_le_mul_right ((n+1)^7) (Nat.mul_le_mul_left (2^19) hf)
    _ ≤ _ := by gcongr; omega

/-- Theorem 5.5: the smaller biclique side controls the `k log k` term. -/
theorem unbalanced_ram {n : ℕ} (a : MatrixGraph n) (S : Finset (Fin n))
    (s t : ℕ) (hs : 1 ≤ s) (ht : 0 < t) (hG : BicliqueFree a.graph s t)
    (hk : 2 ≤ S.card) (m : ℕ) :
    (solve (.unbalanced s t) a S ⟨hs,ht,hG⟩).2 ≤
      2^19*2^(10*s*S.card*(S.card.log2+1)+S.card*(t.log2+1))*(n+m+1)^7 := by
  have hr := ram_tree_bound (.unbalanced s t) a S ⟨hs,ht,hG⟩ hk
  have hf := codegree_search_factor_le_exp (s := s) (q := t-1) (k := S.card) hs (by omega)
  have ht' : t-1+1 = t := Nat.sub_add_cancel ht
  calc
    _ ≤ 2^19*2^(10*s*S.card*(S.card.log2+1)+S.card*(t.log2+1))*(n+1)^7 := by
      apply hr.trans
      simpa only [Family.treeFactor, Family.threshold, Family.edgeParameter, Nat.add_zero,
        codegreeSearchThreshold, ht'] using
        Nat.mul_le_mul_right ((n+1)^7) (Nat.mul_le_mul_left (2^19) hf)
    _ ≤ _ := by gcongr; omega

/-- Theorem 5.2 keeps the genuine real square-root exponent, including odd `k`. -/
theorem edge_ram {n : ℕ} (a : MatrixGraph n) (S : Finset (Fin n))
    (m : ℕ) (hm : a.graph.edgeFinset.card = m) (hk : 2 ≤ S.card) :
    ((solve (.edge m) a S hm).2 : ℝ) ≤
      (2 : ℝ)^19*2^(13*S.card*(S.card.log2+1))*(m+1 : ℝ)^((S.card : ℝ)/2)*(n+m+1 : ℝ)^7 := by
  have hr := ram_tree_bound (.edge m) a S hm hk
  have hf := edge_search_factor_le_real (m := m) (k := S.card) (by omega)
  have hr' : ((solve (.edge m) a S hm).2 : ℝ) ≤
      (2 : ℝ)^19*((S.card*edgePrefixThreshold m S.card)^S.card : ℕ)*(n+m+1 : ℝ)^7 := by
    exact_mod_cast hr
  apply hr'.trans
  have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hf
    (show (0 : ℝ) ≤ 2^19 from pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) 19)) (show (0 : ℝ) ≤ (n+m+1 : ℝ)^7 from
      pow_nonneg (by positivity : (0 : ℝ) ≤ (n+m+1 : ℝ)) 7)
  simpa only [mul_assoc] using h

/-- Only these parameter words may exceed graph-polynomial size. The edge
count is graph data and is already included in the bounded core width. -/
def Family.rawParameterBits : Family → ℕ
  | .edge _ => 0
  | .degeneracy a => binaryLength a
  | .codegree s q => binaryLength s + binaryLength q
  | .unbalanced s t => binaryLength s + binaryLength t

theorem Family.threshold_le_treeFactor (family : Family) {k : ℕ} (hk : 2 ≤ k) :
    family.threshold k ≤ family.treeFactor k := by
  have hp := family.positive k
  exact (show family.threshold k ≤ k*family.threshold k by nlinarith).trans
    (Nat.le_self_pow (by omega) _)

/-- Linear raw-parameter scanning is absorbed additively by the same search
factor; in particular it never introduces an extra `(a+1)` power. -/
theorem Family.rawParameterBits_le (family : Family) {k : ℕ} (hk : 2 ≤ k) :
    family.rawParameterBits+1 ≤ 4*family.treeFactor k := by
  have ht := family.threshold_le_treeFactor hk
  have hf := family.treeFactor_pos hk
  have hR : 1 ≤ k-1 := by omega
  cases family with
  | edge m => simpa [Family.rawParameterBits] using (show 1 ≤ 4*(Family.edge m).treeFactor k by omega)
  | degeneracy a =>
    have hb := binaryLength_le_succ a
    change binaryLength a+1 ≤ _
    change 4*(k-1)*(4*a+1)+1 ≤ _ at ht
    nlinarith
  | codegree s q =>
    have hs := binaryLength_le_succ s
    have hq := binaryLength_le_succ q
    have hpow : 1 ≤ (8*(k-1))^s := Nat.one_le_pow _ _ (by omega)
    change binaryLength s+binaryLength q+1 ≤ _
    change q*(8*(k-1))^s+8*s*(k-1)+1 ≤ _ at ht
    nlinarith
  | unbalanced s t =>
    have hs := binaryLength_le_succ s
    have hq := binaryLength_le_succ t
    have hpow : 1 ≤ (8*(k-1))^s := Nat.one_le_pow _ _ (by omega)
    have ht' : t ≤ (t-1)+1 := by omega
    change binaryLength s+binaryLength t+1 ≤ _
    change (t-1)*(8*(k-1))^s+8*s*(k-1)+1 ≤ _ at ht
    nlinarith

def coreBinaryTariff (family : Family) (k n B : ℕ) : ℕ :=
  binaryScalarTariff (binaryRegisterWidth B k (n+family.edgeParameter) 0)

/-- The actual family search's arithmetic operands fit its parameter-free
padded registers. This instantiates the complete eager-execution certificate
with the computed capped table, including all intermediate budget arithmetic. -/
theorem eager_certificate (family : Family) {k n : ℕ} [NeZero n]
    (E : EncodedInput k n) :
    EagerOperandCertificate (Compatible E.graph) E.normalizedCost
      (cachedThreshold (family.prepare k n).1) E.candidateTable
      (binaryRegisterWidth E.inputBits k (n+family.edgeParameter) 0) := by
  let B := numericSize Finset.univ (fun i => E.candidateTable[i]) E.normalizedCost
  have hB : B ≤ E.inputBits := E.normalized_numericSize_le
  have ht : ∀ r ≤ k, cachedThreshold (family.prepare k n).1 r ≤ n+1 := by
    apply cachedThreshold_le
    intro r
    rw [family.prepared_value k n r]
    exact Nat.min_le_left _ _
  have h := eagerOperandCertificate (Compatible E.graph) E.normalizedCost
    E.normalizedCost_nonneg _ E.candidateTable ht (family.edgeParameter+(E.inputBits-B))
  have heq : B+k+n+(family.edgeParameter+(E.inputBits-B))+1 =
      E.inputBits+k+(n+family.edgeParameter)+0+1 := by omega
  change EagerOperandCertificate _ _ _ _
    (32*(B+k+n+(family.edgeParameter+(E.inputBits-B))+1)^2) at h
  simpa only [heq, binaryRegisterWidth] using h

/-- Binary realization of the actual weighted driver. Threshold preparation
uses the raw parameters only in comparison/minimum or predecessor operations;
saturating arithmetic clips multiplicands and exponents first. A linear scan
of raw parameter bits is therefore charged separately. All search operations
use the bounded-width table model with no oversized parameter word. -/
def weightedBinaryRun (family : Family) {k n : ℕ} (E : EncodedInput k n) :
    Option (Vector (Fin n) k) × ℕ :=
  if hk : k = 0 then (some (Vector.ofFn (E.emptySelection hk)), 1)
  else if hn : n = 0 then (none, 2)
  else
    letI : NeZero n := ⟨hn⟩
    let prepared := family.prepare k n
    let out := E.runPreparedVector prepared.1
    (out.1, (out.2+prepared.2*(family.rawParameterBits+1)+2)*
      coreBinaryTariff family k n E.inputBits)

theorem weightedBinaryRun_value (family : Family) {k n : ℕ} (E : EncodedInput k n) :
    (weightedBinaryRun family E).1 = (weightedOptimizer.run family E).1 := by
  unfold weightedBinaryRun weightedOptimizer EncodedInput.solveUsingPreparationVector
  dsimp only
  split_ifs <;> rfl

def binaryWeightedOptimizer : WeightedOptimizer Family Family.promise where
  run := weightedBinaryRun
  some_optimal := by
    intro family k n E hG targets h
    rw [weightedBinaryRun_value] at h
    exact weightedOptimizer.some_optimal E hG h
  none_iff := by
    intro family k n E hG
    rw [weightedBinaryRun_value]
    exact weightedOptimizer.none_iff E hG

def solveBinary (family : Family) {n : ℕ} (a : MatrixGraph n) (S : Finset (Fin n))
    (hG : family.promise a) : Option (DiscoveryResult a.graph S) × ℕ :=
  GenericTransfer.runWithTariff binaryWeightedOptimizer family a S hG (auxiliaryBinaryTariff n)

theorem binary_none_iff (family : Family) {n : ℕ} (a : MatrixGraph n) (S : Finset (Fin n))
    (hG : family.promise a) :
    (solveBinary family a S hG).1 = none ↔
      ¬ ∃ T m, Independent a.graph T ∧ SlideSequence a.graph S T m := by
  rw [solveBinary, runWithTariff_value]
  exact GenericTransfer.run_none_iff binaryWeightedOptimizer family a S hG

theorem binary_some_spec (family : Family) {n : ℕ} (a : MatrixGraph n) (S : Finset (Fin n))
    (hG : family.promise a) (out : DiscoveryResult a.graph S)
    (hout : (solveBinary family a S hG).1 = some out) :
    Independent a.graph out.target ∧ ValidMoves a.graph S out.moves out.target ∧
    out.target.card = S.card ∧
    (∀ T m, Independent a.graph T → SlideSequence a.graph S T m → out.moves.length ≤ m) ∧
    out.moves.length ≤ S.card*(n-1) := by
  rw [solveBinary, runWithTariff_value] at hout
  exact GenericTransfer.run_some_spec binaryWeightedOptimizer family a S hG out hout

theorem coreBinaryTariff_pos (family : Family) (k n B : ℕ) :
    1 ≤ coreBinaryTariff family k n B := by
  unfold coreBinaryTariff binaryScalarTariff
  have : 1 ≤ (binaryRegisterWidth B k (n+family.edgeParameter) 0+1)^3 :=
    Nat.one_le_pow _ _ (by omega)
  omega

theorem weighted_binary_cost (family : Family) {k n : ℕ} (E : EncodedInput k n)
    (hk : 2 ≤ k) :
    (weightedBinaryRun family E).2 ≤
      5*family.treeFactor k*inputPolynomial family k n E.inputBits*
        coreBinaryTariff family k n E.inputBits := by
  have hc := weighted_cost family E hk
  have hf := family.treeFactor_pos hk
  have hraw := family.rawParameterBits_le hk
  have ht := coreBinaryTariff_pos family k n E.inputBits
  have hp : preparationBound family k n ≤ inputPolynomial family k n E.inputBits := by
    unfold inputPolynomial; omega
  have hp2 : 2 ≤ inputPolynomial family k n E.inputBits := by unfold inputPolynomial; omega
  have hk0 : k ≠ 0 := by omega
  by_cases hn : n = 0
  · simp only [weightedBinaryRun, dif_neg hk0, dif_pos hn]
    have h := Nat.mul_le_mul hf hp2
    have h' := Nat.mul_le_mul_right (5*family.treeFactor k*inputPolynomial family k n E.inputBits) ht
    nlinarith only [h, h']
  · letI : NeZero n := ⟨hn⟩
    have hp' := family.prepared_work k n
    have hprod := Nat.mul_le_mul (hp'.trans hp) hraw
    simp only [weightedOptimizer, EncodedInput.solveUsingPreparationVector,
      dif_neg hk0, dif_neg hn] at hc
    simp only [weightedBinaryRun, dif_neg hk0, dif_neg hn]
    apply Nat.mul_le_mul_right _
    nlinarith only [hc, hprod]

theorem coreBinaryTariff_graph_bound (family : Family) (k n B : ℕ)
    (hkn : k ≤ n) (hB : B ≤ 8*(n+1)^3) :
    coreBinaryTariff family k n B ≤ 2^42*(n+family.edgeParameter+1)^18 := by
  let N := n+family.edgeParameter+1
  have hn : n+1 ≤ N := by dsimp [N]; omega
  have hk : k ≤ N := by omega
  have h1 : 1 ≤ N := by omega
  have h13 : N ≤ N^3 := Nat.le_self_pow (by decide) N
  have hB' := hB.trans (Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left hn 3))
  have hbase : B+k+(n+family.edgeParameter)+0+1 ≤ 10*N^3 := by dsimp [N] at *; omega
  have hW : binaryRegisterWidth B k (n+family.edgeParameter) 0 ≤ 3200*N^6 := by
    unfold binaryRegisterWidth
    calc
      _ ≤ 32*(10*N^3)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hbase 2)
      _ = _ := by ring
  have h16 : 1 ≤ N^6 := Nat.one_le_pow _ _ h1
  have hW' : binaryRegisterWidth B k (n+family.edgeParameter) 0+1 ≤ 3201*N^6 := by omega
  unfold coreBinaryTariff binaryScalarTariff
  calc
    _ ≤ 64*(3201*N^6)^3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hW' 3)
    _ = (64*3201^3)*N^18 := by rw [mul_pow, ← pow_mul]; exact (Nat.mul_assoc _ _ _).symm
    _ ≤ _ := Nat.mul_le_mul_right _ (by norm_num)

private theorem collectPowers (a b x r s : ℕ) :
    (a*x^r)*(b*x^s) = (a*b)*x^(r+s) := by
  rw [pow_add]
  ring

/-- All four binary implementations have the same graph-polynomial degree.
The parameter-bit scan was charged before search and absorbed additively, so
the family-specific factor is unchanged from the RAM bound. -/
theorem binary_tree_bound (family : Family) {n : ℕ} (a : MatrixGraph n)
    (S : Finset (Fin n)) (hG : family.promise a) (hk : 2 ≤ S.card) :
    (solveBinary family a S hG).2 ≤
      2^64*family.treeFactor S.card*(n+family.edgeParameter+1)^25 := by
  let N := n+family.edgeParameter+1
  have hc := weighted_binary_cost family (GenericTransfer.prepare a S).1 hk
  have hb : (GenericTransfer.prepare a S).1.inputBits ≤ 8*(n+1)^3 := by
    rw [prepare_value]; exact metric_inputBits_le a S
  have hkn : S.card ≤ n := by simpa using Finset.card_le_univ S
  have hp := inputPolynomial_graph_bound family S.card n _ hkn hb
  have ht := coreBinaryTariff_graph_bound family S.card n _ hkn hb
  have hs : (weightedBinaryRun family (GenericTransfer.prepare a S).1).2 ≤
      (5*2^60)*family.treeFactor S.card*N^25 := by
    calc
      _ ≤ 5*family.treeFactor S.card*(2^18*N^7)*(2^42*N^18) :=
        hc.trans (Nat.mul_le_mul (Nat.mul_le_mul_left _ hp) ht)
      _ = (5*family.treeFactor S.card)*((2^18*N^7)*(2^42*N^18)) :=
        Nat.mul_assoc _ _ _
      _ = (5*family.treeFactor S.card)*((2^18*2^42)*N^(7+18)) := by
        rw [collectPowers (2^18) (2^42) N 7 18]
      _ = _ := by
        rw [show (2:ℕ)^18*2^42 = 2^60 from (pow_add 2 18 42).symm]
        simp only [Nat.reduceAdd]
        rw [← Nat.mul_assoc (5*family.treeFactor S.card) (2^60) (N^25)]
        exact congrArg (· * N^25) (Nat.mul_right_comm 5 (family.treeFactor S.card) (2^60))
  have ha := runWithTariff_cost_additive binaryWeightedOptimizer family a S hG (auxiliaryBinaryTariff n)
  have hf := family.treeFactor_pos hk
  have hN : n+1 ≤ N := by dsimp [N]; omega
  have hN1 : 1 ≤ N := by omega
  have h1125 : (n+1)^11 ≤ N^25 := (Nat.pow_le_pow_left hN 11).trans
    (Nat.pow_le_pow_right hN1 (by omega))
  have haux : 206*(n+1)^5*auxiliaryBinaryTariff n ≤
      2^38*family.treeFactor S.card*N^25 := by
    calc
      _ ≤ 206*(n+1)^5*((64*257^3)*(n+1)^6) := Nat.mul_le_mul_left _ auxiliaryBinaryTariff_le
      _ = (206*(64*257^3))*(n+1)^11 := collectPowers _ _ _ _ _
      _ ≤ 2^38*N^25 := Nat.mul_le_mul (by norm_num) h1125
      _ ≤ _ := by nlinarith only [Nat.mul_le_mul_right (2^38*N^25) hf]
  change (solveBinary family a S hG).2 ≤
    (weightedBinaryRun family (GenericTransfer.prepare a S).1).2+_ at ha
  change _ ≤ 2^64*family.treeFactor S.card*N^25
  calc
    _ ≤ (5*2^60)*family.treeFactor S.card*N^25 + 2^38*family.treeFactor S.card*N^25 :=
      ha.trans (Nat.add_le_add hs haux)
    _ = (5*2^60+2^38)*family.treeFactor S.card*N^25 := by rw [Nat.add_mul, Nat.add_mul]
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num))

/-- Binary-cost Theorem 5.3, with unchanged degeneracy exponent. -/
theorem degeneracy_binary {n : ℕ} (a : MatrixGraph n) (S : Finset (Fin n))
    (d : ℕ) (hG : Degenerate a.graph d) (hk : 2 ≤ S.card) (m : ℕ) :
    (solveBinary (.degeneracy d) a S hG).2 ≤
      2^64*2^(7*S.card*(S.card.log2+1))*(d+1)^S.card*(n+m+1)^25 := by
  have hr := binary_tree_bound (.degeneracy d) a S hG hk
  have hf := degeneracy_search_factor_le_exp (a := d) (k := S.card) (by omega)
  calc
    _ ≤ 2^64*(2^(7*S.card*(S.card.log2+1))*(d+1)^S.card)*(n+1)^25 := by
      apply hr.trans
      simpa only [Family.treeFactor, Family.threshold, Family.edgeParameter, Nat.add_zero] using
        Nat.mul_le_mul_right ((n+1)^25) (Nat.mul_le_mul_left (2^64) hf)
    _ = (2^64*2^(7*S.card*(S.card.log2+1))*(d+1)^S.card)*(n+1)^25 := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 25)

/-- Binary-cost Theorem 5.4, uniform in `s,q`, with no parameter-bit factor
multiplying the recursive search. -/
theorem codegree_binary {n : ℕ} (a : MatrixGraph n) (S : Finset (Fin n))
    (s q : ℕ) (hs : 1 ≤ s) (hG : CodegreeBound a.graph s q)
    (hk : 2 ≤ S.card) (m : ℕ) :
    (solveBinary (.codegree s q) a S ⟨hs,hG⟩).2 ≤
      2^64*2^(10*s*S.card*(S.card.log2+1)+S.card*((q+1).log2+1))*(n+m+1)^25 := by
  have hr := binary_tree_bound (.codegree s q) a S ⟨hs,hG⟩ hk
  have hf := codegree_search_factor_le_exp (s := s) (q := q) (k := S.card) hs (by omega)
  calc
    _ ≤ 2^64*2^(10*s*S.card*(S.card.log2+1)+S.card*((q+1).log2+1))*(n+1)^25 := by
      apply hr.trans
      simpa only [Family.treeFactor, Family.threshold, Family.edgeParameter, Nat.add_zero,
        codegreeSearchThreshold] using
        Nat.mul_le_mul_right ((n+1)^25) (Nat.mul_le_mul_left (2^64) hf)
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 25)

/-- Binary-cost Theorem 5.5, retaining the smaller-side exponent. -/
theorem unbalanced_binary {n : ℕ} (a : MatrixGraph n) (S : Finset (Fin n))
    (s t : ℕ) (hs : 1 ≤ s) (ht : 0 < t) (hG : BicliqueFree a.graph s t)
    (hk : 2 ≤ S.card) (m : ℕ) :
    (solveBinary (.unbalanced s t) a S ⟨hs,ht,hG⟩).2 ≤
      2^64*2^(10*s*S.card*(S.card.log2+1)+S.card*(t.log2+1))*(n+m+1)^25 := by
  have hr := binary_tree_bound (.unbalanced s t) a S ⟨hs,ht,hG⟩ hk
  have hf := codegree_search_factor_le_exp (s := s) (q := t-1) (k := S.card) hs (by omega)
  have ht' : t-1+1 = t := Nat.sub_add_cancel ht
  calc
    _ ≤ 2^64*2^(10*s*S.card*(S.card.log2+1)+S.card*(t.log2+1))*(n+1)^25 := by
      apply hr.trans
      simpa only [Family.treeFactor, Family.threshold, Family.edgeParameter, Nat.add_zero,
        codegreeSearchThreshold, ht'] using
        Nat.mul_le_mul_right ((n+1)^25) (Nat.mul_le_mul_left (2^64) hf)
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 25)

private theorem realFactorTransfer (A C F N d : ℕ) (b : ℝ)
    (hA : A ≤ C*F*N^d) (hF : (F : ℝ) ≤ b) :
    (A : ℝ) ≤ (C : ℝ)*b*(N : ℝ)^d := by
  have hcast : (A : ℝ) ≤ (C : ℝ)*(F : ℝ)*(N : ℝ)^d := by exact_mod_cast hA
  exact hcast.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hF (Nat.cast_nonneg C)) (pow_nonneg (Nat.cast_nonneg N) d))

/-- Binary-cost Theorem 5.2, including the half-integral edge exponent. -/
theorem edge_binary {n : ℕ} (a : MatrixGraph n) (S : Finset (Fin n))
    (m : ℕ) (hm : a.graph.edgeFinset.card = m) (hk : 2 ≤ S.card) :
    ((solveBinary (.edge m) a S hm).2 : ℝ) ≤
      (2 : ℝ)^64*2^(13*S.card*(S.card.log2+1))*(m+1 : ℝ)^((S.card : ℝ)/2)*(n+m+1 : ℝ)^25 := by
  have hr := binary_tree_bound (.edge m) a S hm hk
  have hf := edge_search_factor_le_real (m := m) (k := S.card) (by omega)
  have h := realFactorTransfer _ (2^64) ((S.card*edgePrefixThreshold m S.card)^S.card)
    (n+m+1) 25 _ hr hf
  simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one, mul_assoc] using h

end IndependentSetDiscovery.FamilyDiscovery
