import IndependentSetDiscovery.Extensions.DirectedComplexity
import IndependentSetDiscovery.Extensions.DirectedReconstructionBits

/-!
# Certified binary realization of the complete directed driver

All measured scalar instructions, including matrix integerization, caches,
path decoding and reconstruction, are charged at the padded-register tariff
from `EagerBitWork`. Counters are ghost instrumentation. This is a finite
RAM/list binary-cost model, not a claim about Lean VM or compiler timings.
-/
namespace IndependentSetDiscovery.WeightedDirected.RationalMatrixInput

open Algorithms WeightedShortestPaths Finset
variable {n : ℕ} (A : RationalMatrixInput n)

def scalarArcExponent : ℕ := n^2 + 2*A.numericBits + 3
def reconstructionExponent : ℕ := 2*n + A.scalarArcExponent

def directedRegisterWidth (d : ℕ) : ℕ :=
  binaryRegisterWidth A.encodedBitsEnvelope n n (binaryLength d)

theorem preprocessingBits_le_envelope : A.preprocessingBits ≤ A.encodedBitsEnvelope := by
  have hm : A.preprocessingBits+2 ≤ 4*(n+1)^2*(A.preprocessingBits+2) :=
    Nat.le_mul_of_pos_left _ (by positivity)
  unfold encodedBitsEnvelope
  omega

theorem reconstructionExponent_le_width [NeZero n] (d : ℕ) :
    A.reconstructionExponent+2 ≤ A.directedRegisterWidth d := by
  have hn : 0 < n := NeZero.pos n
  have hs : 1 ≤ n^2 := Nat.one_le_pow _ _ hn
  have hm := Nat.le_mul_of_pos_left (n^2+2*A.numericBits+4) hs
  have he := A.preprocessingBits_le_envelope
  have hw := binaryRegisterWidth_large A.encodedBitsEnvelope n n (binaryLength d)
  unfold directedRegisterWidth reconstructionExponent scalarArcExponent
  unfold preprocessingBits at he
  omega

theorem scalar_arc_le (S : Finset (Fin n)) (Z : MatrixInput n)
    (hz : Z.weight = integerArcWeight A.relation A.weight) (u v : Fin n) :
    scalarizationBase S.card n * Z.weight u v + 1 ≤ 2^A.scalarArcExponent := by
  have h := A.scalarMatrix_weight_le (scalarizationBase S.card n) u v
  rw [A.scalarMatrix_weight, ← hz] at h
  have hC := scalarizationBase_binaryLength S
  exact h.trans (Nat.pow_le_pow_right (by decide) (by dsimp [scalarArcExponent]; omega))

/-- The concrete selected-route plan starts with a weight total of polynomial
binary length; this is independent of the numeric magnitude of rational weights. -/
theorem initial_plan_weight_bound {Gf : SimpleGraph (Fin n)} (S : Finset (Fin n))
    (Z : MatrixInput n) (hz : Z.weight = integerArcWeight A.relation A.weight)
    (x : S → Fin n)
    (hx : (movementInstance Gf A.relation
      (fun u v => scalarizationBase S.card n * Z.weight u v+1) S).Selection x)
    (paths : ∀ s : S, {p : DWalk A.relation s.val (x s) //
      p.cost (fun u v => scalarizationBase S.card n * Z.weight u v+1) =
        (distance A.relation (fun u v => scalarizationBase S.card n * Z.weight u v+1) s.val (x s)).toNat ∧
      p.length ≤ Fintype.card (Fin n)-1}) :
    (planOfSelection x hx paths).weightTotal ≤ 2^A.reconstructionExponent := by
  have h := planOfSelection_weightTotal_le x hx paths (fun u v _ => A.scalar_arc_le S Z hz u v)
  have hS : S.card ≤ n := by simpa using Finset.card_le_univ S
  have hcoef : S.card*(n-1) ≤ 2^(2*n) := by
    calc
      _ ≤ n*n := Nat.mul_le_mul hS (Nat.sub_le n 1)
      _ ≤ 2^n*2^n := Nat.mul_le_mul Nat.lt_two_pow_self.le Nat.lt_two_pow_self.le
      _ = _ := by rw [← pow_add]; congr 1; omega
  calc
    _ ≤ S.card*(n-1)*2^A.scalarArcExponent := h
    _ ≤ 2^(2*n)*2^A.scalarArcExponent := Nat.mul_le_mul_right _ hcoef
    _ = _ := by rw [← pow_add]; rfl

/-- The same bound applies to every unnormalized partial denominator product. -/
theorem denominator_partial_bits [NeZero n] (d : ℕ) (T : Finset (Fin n × Fin n)) :
    binaryLength (∏ p ∈ T, (A.denominatorCell p).1) ≤ A.directedRegisterWidth d := by
  have h := binaryLength_le_of_le_pow
    ((A.denominator_partial_le T).trans A.arcDenominator_le_numeric_pow)
  have hw := A.reconstructionExponent_le_width d
  unfold reconstructionExponent scalarArcExponent at hw
  omega

/-- Raw integerization and scalarization operands fit before any normalization. -/
theorem raw_preparation_bits [NeZero n] (d : ℕ) (S : Finset (Fin n))
    (Z : MatrixInput n) (hz : Z.weight = integerArcWeight A.relation A.weight)
    (u v : Fin n) :
    binaryLength (A.weight u v).num.toNat ≤ A.directedRegisterWidth d ∧
    binaryLength (A.weight u v).den ≤ A.directedRegisterWidth d ∧
    binaryLength (arcDenominator A.relation A.weight / (A.weight u v).den) ≤ A.directedRegisterWidth d ∧
    binaryLength (Z.weight u v) ≤ A.directedRegisterWidth d ∧
    binaryLength (scalarizationBase S.card n*Z.weight u v) ≤ A.directedRegisterWidth d ∧
    binaryLength (scalarizationBase S.card n*Z.weight u v+1) ≤ A.directedRegisterWidth d := by
  have hn : (A.weight u v).num.toNat ≤ (A.weight u v).num.natAbs := by
    have := Int.toNat_add_toNat_neg_eq_natAbs (A.weight u v).num
    omega
  have hnum := numerator_le_numeric_pow (univ : Finset (Fin n)) (fun _ => univ)
    A.weight u (mem_univ _) v (mem_univ _)
  have hden := rational_den_le_pow (A.weight u v)
  have hr := rationalBits_le_numericSize (univ : Finset (Fin n)) (fun _ => univ)
    A.weight u (mem_univ _) v (mem_univ _)
  have hnB := binaryLength_le_of_le_pow (hn.trans hnum)
  have hdB := binaryLength_le_of_le_pow (hden.trans (Nat.pow_le_pow_right (by decide) hr))
  have hqB := binaryLength_le_of_le_pow ((Nat.div_le_self (arcDenominator A.relation A.weight) (A.weight u v).den).trans A.arcDenominator_le_numeric_pow)
  have hzB : binaryLength (Z.weight u v) ≤ 2*A.numericBits+1 := by
    apply binaryLength_le_of_le_pow
    rw [hz, ← A.integerMatrix_weight]
    exact A.integerMatrix_weight_le u v
  have hs := A.scalar_arc_le S Z hz u v
  have hsB := binaryLength_le_of_le_pow hs
  have hmB := binaryLength_le_of_le_pow ((Nat.le_succ _).trans hs)
  have hw := A.reconstructionExponent_le_width d
  change binaryLength (A.weight u v).num.toNat ≤ A.numericBits+1 at hnB
  change binaryLength (A.weight u v).den ≤ A.numericBits+1 at hdB
  unfold reconstructionExponent scalarArcExponent at hw hsB hmB
  omega

/-- Every tentative Bellman--Ford extension fits before the minimum is chosen. -/
theorem shortest_candidate_bits [NeZero n] (d : ℕ) (S : Finset (Fin n))
    (Z : MatrixInput n) (hz : Z.weight = integerArcWeight A.relation A.weight)
    {s v : Fin n} {p : Route n}
    (hp : Valid A.relation (fun u v => scalarizationBase S.card n*Z.weight u v+1) s v p)
    (hlen : p.vertices.length ≤ n+1) : binaryLength p.score ≤ A.directedRegisterWidth d := by
  have hscore := valid_score_le A.relation _ hp (fun u v _ => A.scalar_arc_le S Z hz u v)
  have hb : p.score ≤ 2^(n+1+A.scalarArcExponent) := by
    calc
      _ ≤ p.vertices.length*2^A.scalarArcExponent := hscore
      _ ≤ (n+1)*2^A.scalarArcExponent := Nat.mul_le_mul_right _ hlen
      _ ≤ 2^(n+1)*2^A.scalarArcExponent := Nat.mul_le_mul_right _ Nat.lt_two_pow_self.le
      _ = _ := (pow_add _ _ _).symm
  have hbits := binaryLength_le_of_le_pow hb
  have hw := A.reconstructionExponent_le_width d
  unfold reconstructionExponent at hw
  omega

/-- Signed numerator magnitudes, the shared denominator, and scalarization
factor are covered as inputs, not only after arithmetic normalization. -/
theorem preparation_input_bits [NeZero n] (d : ℕ) (S : Finset (Fin n)) (u v : Fin n) :
    binaryLength (A.weight u v).num.natAbs ≤ A.directedRegisterWidth d ∧
    binaryLength (arcDenominator A.relation A.weight) ≤ A.directedRegisterWidth d ∧
    binaryLength (scalarizationBase S.card n) ≤ A.directedRegisterWidth d := by
  have hn := binaryLength_le_of_le_pow
    (numerator_le_numeric_pow (univ : Finset (Fin n)) (fun _ => univ)
      A.weight u (mem_univ _) v (mem_univ _))
  have hd := binaryLength_le_of_le_pow A.arcDenominator_le_numeric_pow
  have hc := scalarizationBase_binaryLength S
  have hw := A.reconstructionExponent_le_width d
  change binaryLength (A.weight u v).num.natAbs ≤ A.numericBits+1 at hn
  unfold reconstructionExponent scalarArcExponent at hw
  omega

/-- The optimizer phase is certified at the same width as all auxiliary stages. -/
theorem encoded_eager_certificate [NeZero n] (d : ℕ) (S : Finset (Fin n))
    (P : PreparedRows A.relation (fun u v => scalarizationBase S.card n *
      integerArcWeight A.relation A.weight u v+1)) (a : ShortestPaths.MatrixGraph n) :
    let E := (P.encodeMeasured a S).1
    EagerOperandCertificate (Compatible E.graph) E.normalizedCost
      (cachedThreshold (ThresholdPreparation.balancedTable S.card n d).1) E.candidateTable
      (A.directedRegisterWidth d) := by
  let E := (P.encodeMeasured a S).1
  let B := numericSize univ (fun i => E.candidateTable[i]) E.normalizedCost
  have hB : B ≤ A.encodedBitsEnvelope :=
    E.normalized_numericSize_le.trans (A.measured_encoded_inputBits_le S P a)
  have hS : S.card ≤ n := by simpa using Finset.card_le_univ S
  have ht : ∀ r ≤ S.card,
      cachedThreshold (ThresholdPreparation.balancedTable S.card n d).1 r ≤ n+1 := by
    apply cachedThreshold_le
    intro r
    rw [(ThresholdPreparation.balancedTable_spec S.card n d).1 r]
    exact Nat.min_le_left _ _
  have h := eagerOperandCertificate (Compatible E.graph) E.normalizedCost E.normalizedCost_nonneg
    _ E.candidateTable ht (binaryLength d+(A.encodedBitsEnvelope-B)+(n-S.card))
  have he : B+S.card+n+(binaryLength d+(A.encodedBitsEnvelope-B)+(n-S.card))+1 =
      A.encodedBitsEnvelope+n+n+binaryLength d+1 := by omega
  change EagerOperandCertificate _ _ _ _
    (32*(B+S.card+n+(binaryLength d+(A.encodedBitsEnvelope-B)+(n-S.card))+1)^2) at h
  simpa only [he, directedRegisterWidth, binaryRegisterWidth, E] using h

theorem encoded_threshold_certificate (d : ℕ) (S : Finset (Fin n)) :
    ThresholdOperandCertificate S.card n (binaryLength d) (A.directedRegisterWidth d) := by
  have hS : S.card ≤ n := by simpa using Finset.card_le_univ S
  have h := thresholdOperandCertificate (A.encodedBitsEnvelope+(n-S.card)) S.card n (binaryLength d)
  have he : A.encodedBitsEnvelope+(n-S.card)+S.card+n+binaryLength d+1 =
      A.encodedBitsEnvelope+n+n+binaryLength d+1 := by omega
  simpa only [binaryRegisterWidth, he, directedRegisterWidth] using h

/-- All reached cached reconstruction plans fit the same padded registers. -/
theorem reconstruction_trace_bits [NeZero n] (d : ℕ)
    {Q T : Finset (Fin n)} {sw : Fin n → Fin n → ℕ} (r : RoutePlan A.relation sw Q T)
    (hweight : r.weightTotal ≤ 2^A.reconstructionExponent) (hlen : r.total ≤ n^2)
    (z : Σ R : Finset (Fin n), RoutePlan A.relation sw R T)
    (hz : z ∈ reconstructionStates (materializePlan r)) :
    z.2.total ≤ n^2 ∧ z.2.weightTotal ≤ 2^A.reconstructionExponent ∧
    (∀ s ∈ z.1, binaryLength (z.2.weightBudget s) ≤ A.directedRegisterWidth d) ∧
    (∀ s ∈ z.1, ∀ u ∈ z.1, s ≠ u → ∀ p ≤ z.2.weightBudget s,
      binaryLength (p+z.2.weightBudget u) ≤ A.directedRegisterWidth d) := by
  have h := reconstructionStates_operand_bounds r hweight hlen z hz
  have hw := A.reconstructionExponent_le_width d
  exact ⟨h.1,h.2.1,fun s hs => (h.2.2.1 s hs).1.trans (by omega),
    fun s hs u hu hne p hp => (h.2.2.2 s hs u hu hne p hp).trans (by omega)⟩

/-- Every partial path-cost fold at every reached reconstruction state fits.
The split equality identifies the actual prefix/suffix of a stored walk. -/
theorem reconstruction_partial_sum_bits [NeZero n] (d : ℕ)
    {Q T : Finset (Fin n)} {sw : Fin n → Fin n → ℕ} (r : RoutePlan A.relation sw Q T)
    (hweight : r.weightTotal ≤ 2^A.reconstructionExponent)
    (z : Σ R : Finset (Fin n), RoutePlan A.relation sw R T)
    (hz : z ∈ reconstructionStates (materializePlan r))
    {s u : Fin n} (hs : s ∈ z.1)
    (p : DWalk A.relation s u) (q : DWalk A.relation u (z.2.target s))
    (he : (z.2.paths s hs).val = p.append q) :
    binaryLength (p.cost sw) ≤ A.directedRegisterWidth d ∧
    binaryLength (q.cost sw) ≤ A.directedRegisterWidth d := by
  have ht := (reconstructionStates_bounds (materializePlan r) z hz).2
  rw [materializePlan_weightTotal] at ht
  have hw := ht.trans hweight
  have hpq := z.2.path_parts_bound hs p q he
  have hp := binaryLength_le_of_le_pow (hpq.1.trans hw)
  have hq := binaryLength_le_of_le_pow (hpq.2.trans hw)
  have hW := A.reconstructionExponent_le_width d
  constructor <;> omega

/-- Binary realization rescales every actual instruction of the complete
retained-matrix driver, including all auxiliary stages, at one certified width. -/
def solveBinaryMeasured [NeZero n] (a : ShortestPaths.MatrixGraph n) (S : Finset (Fin n))
    (d : ℕ) (hd : 2 ≤ d) (hG : BicliqueFree a.graph d d) :
    Option (RationalDiscoveryResult a.graph A.relation A.weight S) × ℕ :=
  let result := A.solveMeasured a S d hd hG
  (result.1, result.2*binaryScalarTariff (A.directedRegisterWidth d))

@[simp] theorem solveBinaryMeasured_value [NeZero n] (a : ShortestPaths.MatrixGraph n)
    (S : Finset (Fin n)) (d : ℕ) (hd : 2 ≤ d) (hG : BicliqueFree a.graph d d) :
    (A.solveBinaryMeasured a S d hd hG).1 = (A.solveMeasured a S d hd hG).1 := rfl

/-- The final explicit `2^{O(d k log k)} poly(input bits)` bound for rational
directed motion on a separately constrained terminal graph. -/
theorem solveBinaryMeasured_cost [NeZero n] (a : ShortestPaths.MatrixGraph n)
    (S : Finset (Fin n)) (d : ℕ) (hd : 2 ≤ d) (hk : 2 ≤ S.card)
    (hG : BicliqueFree a.graph d d) :
    (A.solveBinaryMeasured a S d hd hG).2 ≤
      2^(10*d*S.card*(S.card.log2+1)) *
        (A.directedInputPolynomial S.card * binaryScalarTariff (A.directedRegisterWidth d)) := by
  exact (Nat.mul_le_mul_right _ (A.solveMeasured_cost a S d hd hk hG)).trans (le_of_eq (by ring))


/-- Failure reporting is exact for the final binary-cost driver too. -/
theorem solveBinaryMeasured_none_iff [NeZero n] (a : ShortestPaths.MatrixGraph n)
    (S : Finset (Fin n)) (d : ℕ) (hd : 2 ≤ d) (hG : BicliqueFree a.graph d d) :
    (A.solveBinaryMeasured a S d hd hG).1 = none ↔
      ¬ ∃ T c k, Independent a.graph T ∧ RationalSlideSequence A.relation A.weight S T c k := by
  rw [A.solveBinaryMeasured_value]
  exact A.solveMeasured_none_iff a S d hd hG



/-- Absorb binary parameter-reading overhead into the allowed parameter factor;
the remaining input polynomial contains no graph-class parameter. -/
theorem directed_tariff_le (d : ℕ) :
    binaryScalarTariff (A.directedRegisterWidth d) ≤
      2^(6*d) * (64*33^3*(A.encodedBitsEnvelope+2*n+2)^6) := by
  let X := A.encodedBitsEnvelope+2*n+2
  let T := A.encodedBitsEnvelope+n+n+binaryLength d+1
  have hb : binaryLength d ≤ 2^d := by
    have hl := Nat.log2_le_self d
    have hp : d+1 ≤ 2^d := Nat.lt_two_pow_self
    unfold binaryLength
    omega
  have hp : 1 ≤ 2^d := Nat.one_le_pow _ _ (by decide)
  have hm := Nat.mul_le_mul_left (A.encodedBitsEnvelope+2*n+1) hp
  have ht : T ≤ 2^d*X := by dsimp [T,X]; nlinarith only [hb,hm]
  have htpos : 1 ≤ T := by dsimp [T]; omega
  have hsq : 1 ≤ T^2 := Nat.one_le_pow _ _ htpos
  have hplus : 32*T^2+1 ≤ 33*T^2 := by omega
  change 64*(32*T^2+1)^3 ≤ _
  calc
    _ ≤ 64*(33*T^2)^3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hplus 3)
    _ = 64*33^3*T^6 := by rw [mul_pow, ← pow_mul]; ring
    _ ≤ 64*33^3*(2^d*X)^6 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ht 6)
    _ = _ := by rw [mul_pow, ← pow_mul]; dsimp [X]; ring

def directedPureInputPolynomial (k : ℕ) : ℕ :=
  A.directedInputPolynomial k * (64*33^3*(A.encodedBitsEnvelope+2*n+2)^6)

/-- Paper-form Corollary 5.6: every factor outside the exponential is a fixed
polynomial in graph size, label count and original rational-input bits only. -/
theorem solveBinaryMeasured_paper_bound [NeZero n] (a : ShortestPaths.MatrixGraph n)
    (S : Finset (Fin n)) (d : ℕ) (hd : 2 ≤ d) (hk : 2 ≤ S.card)
    (hG : BicliqueFree a.graph d d) :
    (A.solveBinaryMeasured a S d hd hG).2 ≤
      2^(16*d*S.card*(S.card.log2+1)) * A.directedPureInputPolynomial S.card := by
  have hmul : 6*d ≤ 6*d*(S.card*(S.card.log2+1)) :=
    Nat.le_mul_of_pos_right _ (by positivity)
  have he : 10*d*S.card*(S.card.log2+1)+6*d ≤ 16*d*S.card*(S.card.log2+1) := by
    nlinarith only [hmul]
  calc
    _ ≤ 2^(10*d*S.card*(S.card.log2+1)) *
        (A.directedInputPolynomial S.card * binaryScalarTariff (A.directedRegisterWidth d)) :=
      A.solveBinaryMeasured_cost a S d hd hk hG
    _ ≤ 2^(10*d*S.card*(S.card.log2+1)) *
        (A.directedInputPolynomial S.card *
          (2^(6*d)*(64*33^3*(A.encodedBitsEnvelope+2*n+2)^6))) := by
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (A.directed_tariff_le d))
    _ = 2^(10*d*S.card*(S.card.log2+1)+6*d) * A.directedPureInputPolynomial S.card := by
      rw [pow_add]
      unfold directedPureInputPolynomial
      ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) he)

end IndependentSetDiscovery.WeightedDirected.RationalMatrixInput
