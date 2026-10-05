import IndependentSetDiscovery.GenericTransfer
import IndependentSetDiscovery.Algorithms.EncodedBounds

/-!
# Theorem 1.2: the concrete measured discovery algorithm

The supplied-optimizer premise of Corollary 3.3 is discharged here by the
implemented finite-table biclique-free optimizer. Every successful result
contains its actual shortest collision-free move list. The operation bound
has universal constants and a graph-size polynomial of fixed degree.
-/

namespace IndependentSetDiscovery.MeasuredDiscovery

open ShortestPaths Algorithms Movement GenericTransfer

def promise (d : ℕ) {n : ℕ} (a : MatrixGraph n) : Prop :=
  2 ≤ d ∧ BicliqueFree a.graph d d

def weightedOptimizer : WeightedOptimizer ℕ promise where
  run := fun d {k n} E => E.solveMeasuredVector d
  some_optimal := by
    intro d k n E hG targets h
    exact E.solveMeasuredVector_some hG.1 hG.2 h
  none_iff := by
    intro d k n E hG
    exact E.solveMeasuredVector_none_iff hG.1 hG.2

/-- Concrete total driver. The graph promise is erased proof data; no
optimization, movement, or transversal oracle is accepted by this entrypoint. -/
def solve {n : ℕ} (a : MatrixGraph n) (S : Finset (Fin n)) (d : ℕ)
    (hd : 2 ≤ d) (hG : BicliqueFree a.graph d d) : Option (DiscoveryResult a.graph S) × ℕ :=
  GenericTransfer.run weightedOptimizer d a S ⟨hd, hG⟩

theorem none_iff {n : ℕ} (a : MatrixGraph n) (S : Finset (Fin n)) (d : ℕ)
    (hd : 2 ≤ d) (hG : BicliqueFree a.graph d d) :
    (solve a S d hd hG).1 = none ↔
      ¬ ∃ T m, Independent a.graph T ∧ SlideSequence a.graph S T m :=
  GenericTransfer.run_none_iff weightedOptimizer d a S ⟨hd, hG⟩

theorem some_spec {n : ℕ} (a : MatrixGraph n) (S : Finset (Fin n)) (d : ℕ)
    (hd : 2 ≤ d) (hG : BicliqueFree a.graph d d) (out : DiscoveryResult a.graph S)
    (hout : (solve a S d hd hG).1 = some out) :
    Independent a.graph out.target ∧ ValidMoves a.graph S out.moves out.target ∧
    out.target.card = S.card ∧
    (∀ T m, Independent a.graph T → SlideSequence a.graph S T m → out.moves.length ≤ m) ∧
    out.moves.length ≤ S.card*(n-1) :=
  GenericTransfer.run_some_spec weightedOptimizer d a S ⟨hd, hG⟩ out hout

theorem inputPolynomial_graph_bound (k n B : ℕ) (hkn : k ≤ n) (hB : B ≤ 8*(n+1)^3) :
    EncodedInput.measuredInputPolynomial k n B ≤ 2^17 * (n+1)^7 := by
  have hN : 1 ≤ (n+1)^3 := Nat.one_le_pow _ _ (by omega)
  have hN2 : (n+1)^2 ≤ (n+1)^3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hkn' : (k+1)*(n+1) ≤ (n+1)^2 := by nlinarith
  have hbase : 6*B+6+(k+1)*(n+1) ≤ 55*(n+1)^3 := by omega
  have hcore : eagerInputPolynomial k n B ≤ 14080*(n+1)^7 := by
    unfold eagerInputPolynomial
    calc
      _ ≤ (55*(n+1)^3)*256*(n+1)^2*(n+1)^2 := by gcongr
      _ = _ := by ring
  have ht : (k+1)*(12*(n+1)+38) ≤ 50*(n+1)^2 := by nlinarith
  have hc : 5*k*(n+1) ≤ 5*(n+1)^2 := by nlinarith
  have ho : k*(k+2) ≤ 2*(n+1)^2 := by nlinarith
  have h27 : (n+1)^2 ≤ (n+1)^7 := Nat.pow_le_pow_right (by omega) (by omega)
  have h17 : 1 ≤ (n+1)^7 := Nat.one_le_pow _ _ (by omega)
  unfold EncodedInput.measuredInputPolynomial
  norm_num
  nlinarith

/-- Full algorithm, including measured encoding, optimization, finite target
decoding, selected paths, and cached collision-free reconstruction. -/
theorem ram_bound {n : ℕ} (a : MatrixGraph n) (S : Finset (Fin n)) (d : ℕ)
    (hd : 2 ≤ d) (hk : 2 ≤ S.card) (hG : BicliqueFree a.graph d d) (m : ℕ) :
    (solve a S d hd hG).2 ≤
      2^(15*d*S.card*(S.card.log2+1)) * (n+m+1)^7 := by
  have hc := (prepare a S).1.solveMeasuredVector_le_exp hd hk
  have hb : (prepare a S).1.inputBits ≤ 8*(n+1)^3 := by
    rw [prepare_value]
    exact metric_inputBits_le a S
  have hkn : S.card ≤ n := by simpa using Finset.card_le_univ S
  have hp := inputPolynomial_graph_bound S.card n _ hkn hb
  have hs : ((prepare a S).1.solveMeasuredVector d).2 ≤
      2^(10*d*S.card*(S.card.log2+1)) * (2^17*(n+1)^7) :=
    hc.trans (Nat.mul_le_mul_left _ hp)
  have ha := run_cost_additive weightedOptimizer d a S ⟨hd,hG⟩
  change (solve a S d hd hG).2 ≤ _ at ha
  change _ ≤ ((prepare a S).1.solveMeasuredVector d).2 + 206*(n+1)^5 at ha
  have h57 : (n+1)^5 ≤ (n+1)^7 := Nat.pow_le_pow_right (by omega) (by omega)
  have hF : 1 ≤ 2^(10*d*S.card*(S.card.log2+1)) := Nat.one_le_pow _ _ (by omega)
  have haux : 206*(n+1)^5 ≤ 206*2^(10*d*S.card*(S.card.log2+1))*(n+1)^7 := by
    calc
      _ ≤ 206*(n+1)^7 := Nat.mul_le_mul_left _ h57
      _ ≤ _ := by nlinarith only [Nat.mul_le_mul_right (206*(n+1)^7) hF]
  have hscalar : (solve a S d hd hG).2 ≤
      2^18 * 2^(10*d*S.card*(S.card.log2+1)) * (n+1)^7 := by
    norm_num at hs ⊢
    nlinarith only [ha, hs, haux]
  have hexp : 18 + 10*d*S.card*(S.card.log2+1) ≤ 15*d*S.card*(S.card.log2+1) := by
    have hA : 4 ≤ d*S.card*(S.card.log2+1) := by
      have hdk : 4 ≤ d*S.card := by simpa using Nat.mul_le_mul hd hk
      simpa using Nat.mul_le_mul hdk (show 1 ≤ S.card.log2+1 by omega)
    nlinarith
  calc
    _ ≤ 2^18 * 2^(10*d*S.card*(S.card.log2+1)) * (n+1)^7 := hscalar
    _ = 2^(18+10*d*S.card*(S.card.log2+1)) * (n+1)^7 := by rw [pow_add]
    _ ≤ 2^(15*d*S.card*(S.card.log2+1)) * (n+1)^7 :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) hexp)
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 7)

/-- The same implemented optimizer in the padded-width binary primitive model.
Its vector answer is unchanged; only the attached instruction cost is refined. -/
def binaryWeightedOptimizer : WeightedOptimizer ℕ promise where
  run := fun d {k n} E =>
    let out := E.solveMeasuredVector d
    (out.1, out.2 * binaryScalarTariff (binaryRegisterWidth E.inputBits k n (binaryLength d)))
  some_optimal := by
    intro d k n E hG targets h
    exact E.solveMeasuredVector_some hG.1 hG.2 h
  none_iff := by
    intro d k n E hG
    exact E.solveMeasuredVector_none_iff hG.1 hG.2

def solveBinary {n : ℕ} (a : MatrixGraph n) (S : Finset (Fin n)) (d : ℕ)
    (hd : 2 ≤ d) (hG : BicliqueFree a.graph d d) : Option (DiscoveryResult a.graph S) × ℕ :=
  GenericTransfer.runWithTariff binaryWeightedOptimizer d a S ⟨hd,hG⟩ (auxiliaryBinaryTariff n)

theorem binary_none_iff {n : ℕ} (a : MatrixGraph n) (S : Finset (Fin n)) (d : ℕ)
    (hd : 2 ≤ d) (hG : BicliqueFree a.graph d d) :
    (solveBinary a S d hd hG).1 = none ↔
      ¬ ∃ T m, Independent a.graph T ∧ SlideSequence a.graph S T m := by
  rw [solveBinary, runWithTariff_value]
  exact GenericTransfer.run_none_iff binaryWeightedOptimizer d a S ⟨hd,hG⟩

theorem binary_some_spec {n : ℕ} (a : MatrixGraph n) (S : Finset (Fin n)) (d : ℕ)
    (hd : 2 ≤ d) (hG : BicliqueFree a.graph d d) (out : DiscoveryResult a.graph S)
    (hout : (solveBinary a S d hd hG).1 = some out) :
    Independent a.graph out.target ∧ ValidMoves a.graph S out.moves out.target ∧
    out.target.card = S.card ∧
    (∀ T m, Independent a.graph T → SlideSequence a.graph S T m → out.moves.length ≤ m) ∧
    out.moves.length ≤ S.card*(n-1) := by
  rw [solveBinary, runWithTariff_value] at hout
  exact GenericTransfer.run_some_spec binaryWeightedOptimizer d a S ⟨hd,hG⟩ out hout

theorem binaryTariff_graph_bound (k n B d : ℕ) (hkn : k ≤ n) (hB : B ≤ 8*(n+1)^3) :
    binaryScalarTariff (binaryRegisterWidth B k n (binaryLength d)) ≤
      2^44 * (d+1)^6 * (n+1)^18 := by
  have hbits := binaryLength_le_succ d
  have h1 : 1 ≤ (n+1)^3 := Nat.one_le_pow _ _ (by omega)
  have hn : n ≤ (n+1)^3 := by simpa using DiscoveryComplexity.power_envelope n 1 3 (by omega)
  have hsum : B+k+n+binaryLength d+1 ≤ 12*(d+1)*(n+1)^3 := by
    calc
      _ ≤ 8*(n+1)^3 + 2*n + d+2 := by omega
      _ ≤ 8*(n+1)^3 + 2*(n+1)^3 + (d+2)*(n+1)^3 := by
        nlinarith only [hn, Nat.mul_le_mul_left (d+2) h1]
      _ = (d+12)*(n+1)^3 := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
  have hw : binaryRegisterWidth B k n (binaryLength d) ≤ 4608*(d+1)^2*(n+1)^6 := by
    calc
      _ ≤ 32*(12*(d+1)*(n+1)^3)^2 := Nat.mul_le_mul_left 32 (Nat.pow_le_pow_left hsum 2)
      _ = _ := by ring
  have hfactor : 1 ≤ (d+1)^2*(n+1)^6 := by
    simpa using Nat.mul_le_mul (Nat.one_le_pow 2 (d+1) (by omega))
      (Nat.one_le_pow 6 (n+1) (by omega))
  have hw' : binaryRegisterWidth B k n (binaryLength d)+1 ≤ 4609*(d+1)^2*(n+1)^6 := by
    nlinarith only [hw, hfactor]
  calc
    _ ≤ 64*(4609*(d+1)^2*(n+1)^6)^3 :=
      Nat.mul_le_mul_left 64 (Nat.pow_le_pow_left hw' 3)
    _ = (64*4609^3)*(d+1)^6*(n+1)^18 := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num : 64*4609^3 ≤ 2^44))

/-- Explicit binary-work form of Theorem 1.2. Both the exponential constant
30 and the graph-polynomial degree 25 are universal. -/
theorem binary_bound {n : ℕ} (a : MatrixGraph n) (S : Finset (Fin n)) (d : ℕ)
    (hd : 2 ≤ d) (hk : 2 ≤ S.card) (hG : BicliqueFree a.graph d d) (m : ℕ) :
    (solveBinary a S d hd hG).2 ≤
      2^(30*d*S.card*(S.card.log2+1)) * (n+m+1)^25 := by
  let A := d*S.card*(S.card.log2+1)
  let t := 10*d*S.card*(S.card.log2+1)+6*d+61
  have hb : (prepare a S).1.inputBits ≤ 8*(n+1)^3 := by
    rw [prepare_value]
    exact metric_inputBits_le a S
  have hkn : S.card ≤ n := by simpa using Finset.card_le_univ S
  have hp := inputPolynomial_graph_bound S.card n _ hkn hb
  have hc := (prepare a S).1.solveMeasuredVector_le_exp hd hk
  have ht := binaryTariff_graph_bound S.card n _ d hkn hb
  have hsearch : (binaryWeightedOptimizer.run d (prepare a S).1).2 ≤
      2^t * (n+1)^25 := by
    have hpow : (d+1)^6 ≤ 2^(6*d) := by
      have hh : d+1 ≤ 2^d := Nat.succ_le_of_lt Nat.lt_two_pow_self
      calc
        _ ≤ (2^d)^6 := Nat.pow_le_pow_left hh 6
        _ = _ := by rw [← pow_mul]; congr 1; omega
    change ((prepare a S).1.solveMeasuredVector d).2 * _ ≤ _
    calc
      _ ≤ (2^(10*d*S.card*(S.card.log2+1)) * (2^17*(n+1)^7)) *
          (2^44*(d+1)^6*(n+1)^18) :=
        Nat.mul_le_mul (hc.trans (Nat.mul_le_mul_left _ hp)) ht
      _ = 2^(10*d*S.card*(S.card.log2+1)+61) * (d+1)^6 * (n+1)^25 := by
        rw [pow_add]; norm_num; ring
      _ ≤ 2^(10*d*S.card*(S.card.log2+1)+61) * 2^(6*d) * (n+1)^25 := by gcongr
      _ = _ := by rw [← pow_add]; unfold t; congr 2; omega
  have haux : 206*(n+1)^5*auxiliaryBinaryTariff n ≤ 2^t*(n+1)^25 := by
    have ht' := auxiliaryBinaryTariff_le (n := n)
    have h1125 : (n+1)^11 ≤ (n+1)^25 := Nat.pow_le_pow_right (by omega) (by omega)
    have h38 : 38 ≤ t := by unfold t; omega
    calc
      _ ≤ 206*(n+1)^5*((64*257^3)*(n+1)^6) := Nat.mul_le_mul_left _ ht'
      _ = (206*64*257^3)*(n+1)^11 := by ring
      _ ≤ 2^38*(n+1)^11 := Nat.mul_le_mul_right _ (by norm_num)
      _ ≤ 2^t*(n+1)^25 := Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) h38) h1125
  have ha := runWithTariff_cost_additive binaryWeightedOptimizer d a S ⟨hd,hG⟩
    (auxiliaryBinaryTariff n)
  have htotal : (solveBinary a S d hd hG).2 ≤ 2^(t+1)*(n+1)^25 := by
    change (solveBinary a S d hd hG).2 ≤ _ at ha
    rw [pow_succ]
    nlinarith only [ha,hsearch,haux]
  have hA : 4 ≤ A := by
    have hdk : 4 ≤ d*S.card := by simpa using Nat.mul_le_mul hd hk
    simpa [A] using Nat.mul_le_mul hdk (show 1 ≤ S.card.log2+1 by omega)
  have hdA : 2*d ≤ A := by
    have hdk := Nat.mul_le_mul_left d hk
    have h := Nat.mul_le_mul_right (d*S.card) (show 1 ≤ S.card.log2+1 by omega)
    dsimp [A]
    nlinarith only [hdk,h]
  have hexp : t+1 ≤ 30*d*S.card*(S.card.log2+1) := by
    unfold t A at *
    nlinarith only [hA,hdA]
  exact htotal.trans (Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) hexp)
    (Nat.pow_le_pow_left (by omega) 25))

end IndependentSetDiscovery.MeasuredDiscovery
