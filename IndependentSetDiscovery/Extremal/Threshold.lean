import IndependentSetDiscovery.Extremal.Counting

/-!
# Explicit bounded-codegree prefix thresholds

All statements here use natural-number arithmetic. In particular there is no
rounding of a real root in the certificate used by the finite algorithm.
-/
namespace IndependentSetDiscovery

open Finset

/-- Paper equation (15), with `R = r - 1`. -/
def codegreeThreshold (s q R : ℕ) : ℕ := q * (8 * R) ^ s + 8 * s * R + 1

@[simp] theorem codegreeThreshold_pos (s q R : ℕ) : 0 < codegreeThreshold s q R := by
  unfold codegreeThreshold
  omega

theorem codegreeThreshold_gt_power (s q R : ℕ) :
    q * (8 * R) ^ s < codegreeThreshold s q R := by
  unfold codegreeThreshold
  omega

theorem codegreeThreshold_gt_linear (s q R : ℕ) :
    8 * s * R < codegreeThreshold s q R := by
  unfold codegreeThreshold
  omega

theorem codegreeThreshold_mono (s q : ℕ) : Monotone (codegreeThreshold s q) := by
  intro R R' h
  unfold codegreeThreshold
  gcongr

variable {V : Type*} [DecidableEq V] [Fintype V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The power-form KST estimate implies a strict scaled edge bound without
introducing real roots. -/
theorem scaled_kst_excess_lt {s q t A : ℕ} (hs : 1 ≤ s)
    (h : CodegreeBound G s q) (U W : Finset V)
    (hU : U.card = t) (hW : W.card = t) (ht : 0 < t)
    (hA : q * A ^ s < t) :
    A * ((adjacencyPairs G U W).card - (s - 1) * t) < t ^ 2 := by
  have hk := balanced_parts_kst_pow G hs h U W hU hW
  have hp : (A * ((adjacencyPairs G U W).card - (s - 1) * t)) ^ s < (t ^ 2) ^ s := by
    calc
      _ = A ^ s * ((adjacencyPairs G U W).card - (s - 1) * t) ^ s := mul_pow _ _ _
      _ ≤ A ^ s * (q * t ^ (2 * s - 1)) := Nat.mul_le_mul_left _ hk
      _ = (q * A ^ s) * t ^ (2 * s - 1) := by ring
      _ < t * t ^ (2 * s - 1) := Nat.mul_lt_mul_of_pos_right hA (Nat.pow_pos ht)
      _ = (t ^ 2) ^ s := by
        rw [← pow_succ', ← pow_mul]
        congr 1
        omega
  exact (Nat.pow_lt_pow_iff_left (by omega)).mp hp

/-- General strict codegree certificate: each summand occupies less than
one half of the available density allowance. -/
theorem codegree_conflict_certificate {s q t R : ℕ} (hs : 1 ≤ s)
    (h : CodegreeBound G s q) (U W : Finset V)
    (hU : U.card = t) (hW : W.card = t)
    (hpower : q * (8 * R) ^ s < t) (hlinear : 8 * s * R < t) :
    4 * R * (conflictPairs G U W).card < t ^ 2 := by
  have ht : 0 < t := by omega
  have he := scaled_kst_excess_lt G hs h U W hU hW ht hpower
  have hc := card_conflictPairs_le G U W
  rw [hU] at hc
  have hdeg : (adjacencyPairs G U W).card ≤
      ((adjacencyPairs G U W).card - (s - 1) * t) + (s - 1) * t := by omega
  have hst : (s - 1) * t + t = s * t := by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hs]
  have hc' : (conflictPairs G U W).card ≤
      ((adjacencyPairs G U W).card - (s - 1) * t) + s * t := by omega
  have hl : (8 * s * R) * t < t ^ 2 := by
    simpa [pow_two] using Nat.mul_lt_mul_of_pos_right hlinear ht
  have hm := Nat.mul_le_mul_left (8 * R) hc'
  nlinarith

/-- The explicit threshold from the bounded-codegree theorem supplies the
exact integer certificate consumed by the transversal argument. -/
theorem codegreeThreshold_certificate {s q R : ℕ} (hs : 1 ≤ s)
    (h : CodegreeBound G s q) (U W : Finset V)
    (hU : U.card = codegreeThreshold s q R)
    (hW : W.card = codegreeThreshold s q R) :
    4 * R * (conflictPairs G U W).card < (codegreeThreshold s q R) ^ 2 :=
  codegree_conflict_certificate G hs h U W hU hW
    (codegreeThreshold_gt_power s q R) (codegreeThreshold_gt_linear s q R)

/-- The unbalanced-biclique threshold is the codegree threshold with `q=t-1`. -/
theorem unbalancedBicliqueThreshold_certificate {s t R : ℕ}
    (hs : 1 ≤ s) (ht : 0 < t) (h : BicliqueFree G s t) (U W : Finset V)
    (hU : U.card = codegreeThreshold s (t - 1) R)
    (hW : W.card = codegreeThreshold s (t - 1) R) :
    4 * R * (conflictPairs G U W).card < (codegreeThreshold s (t - 1) R) ^ 2 :=
  codegreeThreshold_certificate G hs ((bicliqueFree_iff_codegreeBound G s t ht).mp h)
    U W hU hW

/-- Strict tangent estimate for a positive increment, proved by induction.
This is the integer form of the strict difference-of-powers argument. -/
theorem pow_add_lt_tangent (a c n : ℕ) (hc : 0 < c) :
    (a + c) ^ (n + 2) < a ^ (n + 2) + (n + 2) * c * (a + c) ^ (n + 1) := by
  induction n with
  | zero =>
    simp only [zero_add, pow_two, pow_one]
    nlinarith [Nat.mul_pos hc hc]
  | succ n ih =>
    have ht : 0 < a + c := by omega
    have hp : a ^ (n + 2) ≤ (a + c) ^ (n + 2) :=
      Nat.pow_le_pow_left (by omega) (n + 2)
    have hsucc : n.succ + 2 = (n + 2) + 1 := by omega
    have hpred : n.succ + 1 = n + 2 := by omega
    calc
      _ = (a + c) ^ (n + 2) * (a + c) := by rw [hsucc, pow_succ]
      _ < (a ^ (n + 2) + (n + 2) * c * (a + c) ^ (n + 1)) * (a + c) :=
        Nat.mul_lt_mul_of_pos_right ih ht
      _ = a ^ (n + 2) * a + c * a ^ (n + 2) +
          (n + 2) * c * (a + c) ^ (n + 2) := by
        rw [show (a + c) ^ (n + 2) = (a + c) ^ (n + 1) * (a + c) by
          rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]]
        ring
      _ ≤ a ^ (n + 2) * a + c * (a + c) ^ (n + 2) +
          (n + 2) * c * (a + c) ^ (n + 2) := by gcongr
      _ = _ := by rw [hsucc, hpred, pow_succ]; ring

/-- The sharper balanced certificate, with the exact threshold of Lemma 4.3.
The proof works directly with integer powers rather than approximate roots. -/
theorem balanced_conflict_certificate {d Q t : ℕ} (hd : 2 ≤ d) (hQ : 0 < Q)
    (h : CodegreeBound G d (d - 1)) (U W : Finset V)
    (hU : U.card = t) (hW : W.card = t)
    (hT : t = (d - 1) * Q ^ d + d ^ 2 * Q) :
    Q * (conflictPairs G U W).card < t ^ 2 := by
  have hd1 : 1 ≤ d := by omega
  have hd0 : 0 < d := by omega
  have hc : 0 < d * Q := Nat.mul_pos hd0 hQ
  have hcc : d * Q ≤ d ^ 2 * Q := by
    have : d ≤ d ^ 2 := Nat.le_self_pow (by decide) d
    exact Nat.mul_le_mul_right Q this
  have hct : d * Q ≤ t := by omega
  have ht : 0 < t := by omega
  let a := t - d * Q
  let E := (adjacencyPairs G U W).card - (d - 1) * t
  have hac : a + d * Q = t := Nat.sub_add_cancel hct
  have htangent : t ^ d < a ^ d + d * (d * Q) * t ^ (d - 1) := by
    have hz := pow_add_lt_tangent a (d * Q) (d - 2) hc
    have h₁ : d - 2 + 2 = d := by omega
    have h₂ : d - 2 + 1 = d - 1 := by omega
    simpa [h₁, h₂, hac] using hz
  have hconf : (conflictPairs G U W).card ≤ E + d * t := by
    have hcf := card_conflictPairs_le G U W
    rw [hU] at hcf
    have he : (adjacencyPairs G U W).card ≤ E + (d - 1) * t := by
      dsimp [E]
      omega
    have : (d - 1) * t + t = d * t := by
      rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hd1]
    omega
  by_contra hn
  have hn' : t ^ 2 ≤ Q * (conflictPairs G U W).card := by omega
  have hm := Nat.mul_le_mul_left Q hconf
  have hlow : t * a ≤ Q * E := by nlinarith only [hac, hm, hn', pow_two t]
  have hpow := Nat.pow_le_pow_left hlow d
  have hk := balanced_parts_kst_pow G hd1 h U W hU hW
  change E ^ d ≤ (d - 1) * t ^ (2 * d - 1) at hk
  have hupper : t ^ d * a ^ d ≤ t ^ d * ((d - 1) * Q ^ d * t ^ (d - 1)) := by
    calc
      _ = (t * a) ^ d := (mul_pow _ _ _).symm
      _ ≤ (Q * E) ^ d := hpow
      _ = Q ^ d * E ^ d := mul_pow _ _ _
      _ ≤ Q ^ d * ((d - 1) * t ^ (2 * d - 1)) := Nat.mul_le_mul_left _ hk
      _ = _ := by
        rw [show 2 * d - 1 = d + (d - 1) by omega, pow_add]
        ring
  have ha : a ^ d ≤ (d - 1) * Q ^ d * t ^ (d - 1) :=
    Nat.le_of_mul_le_mul_left hupper (Nat.pow_pos ht)
  have htEq : ((d - 1) * Q ^ d + d * (d * Q)) * t ^ (d - 1) = t ^ d := by
    have : (d - 1) * Q ^ d + d * (d * Q) = t := by
      calc
        _ = (d - 1) * Q ^ d + d ^ 2 * Q := by ring
        _ = t := hT.symm
    rw [this, ← pow_succ']
    congr 1
    omega
  have hbound : a ^ d + d * (d * Q) * t ^ (d - 1) ≤ t ^ d := by
    calc
      _ ≤ (d - 1) * Q ^ d * t ^ (d - 1) + d * (d * Q) * t ^ (d - 1) :=
        Nat.add_le_add_right ha _
      _ = ((d - 1) * Q ^ d + d * (d * Q)) * t ^ (d - 1) := by ring
      _ = t ^ d := htEq
  exact (Nat.not_lt_of_ge hbound) htangent

/-- The exact threshold `M(d,r)` from the balanced biclique theorem. -/
def balancedThreshold (d r : ℕ) : ℕ :=
  (d - 1) * (4 * (r - 1)) ^ d + 4 * d ^ 2 * (r - 1)

/-- Exact balanced threshold certificate, with no asymptotic weakening. -/
theorem balancedThreshold_certificate {d r : ℕ} (hd : 2 ≤ d) (hr : 2 ≤ r)
    (h : BicliqueFree G d d) (U W : Finset V)
    (hU : U.card = balancedThreshold d r) (hW : W.card = balancedThreshold d r) :
    4 * (r - 1) * (conflictPairs G U W).card < (balancedThreshold d r) ^ 2 := by
  apply balanced_conflict_certificate G hd (by omega)
    ((bicliqueFree_iff_codegreeBound G d d (by omega)).mp h) U W hU hW
  unfold balancedThreshold
  ring

end IndependentSetDiscovery
