import IndependentSetDiscovery.Extremal.Threshold

/-!
# The real-exponent form of the extremal estimates

These are the paper-facing versions of the integer inequalities. Algorithmic
certificates use `Threshold.lean` and therefore never evaluate a real root.
-/
namespace IndependentSetDiscovery

/-- The leading asymmetric KST term, for equal-size parts. -/
noncomputable def kstMainTerm (s q t : ℕ) : ℝ :=
  (q : ℝ) ^ (1 / (s : ℝ)) * (t : ℝ) ^ (2 - 1 / (s : ℝ))

@[simp] theorem kstMainTerm_nonneg (s q t : ℕ) : 0 ≤ kstMainTerm s q t := by
  unfold kstMainTerm
  positivity

/-- Raising the real leading term to the integer exponent removes both roots. -/
theorem kstMainTerm_pow {s : ℕ} (hs : 1 ≤ s) (q t : ℕ) :
    kstMainTerm s q t ^ s = (q : ℝ) * (t : ℝ) ^ (2 * s - 1) := by
  have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast (by omega : s ≠ 0)
  have h2 : 1 ≤ 2 * s := by omega
  have he : (2 - 1 / (s : ℝ)) * (s : ℝ) = ((2 * s - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub h2]
    push_cast
    field_simp
  unfold kstMainTerm
  rw [mul_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg q),
    one_div_mul_cancel hs0, Real.rpow_one,
    ← Real.rpow_mul_natCast (Nat.cast_nonneg t), he, Real.rpow_natCast]

open Finset
variable {V : Type*} [DecidableEq V] [Fintype V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The asymmetric Kővári–Sós–Turán bound in the exact form used in the paper. -/
theorem asymmetric_kst {s q t : ℕ} (hs : 1 ≤ s) (h : CodegreeBound G s q)
    (U W : Finset V) (hU : U.card = t) (hW : W.card = t) :
    ((adjacencyPairs G U W).card : ℝ) ≤
      (q : ℝ) ^ (1 / (s : ℝ)) * (t : ℝ) ^ (2 - 1 / (s : ℝ)) +
        ((s - 1 : ℕ) : ℝ) * t := by
  let E := (adjacencyPairs G U W).card - (s - 1) * t
  have hk : (E : ℝ) ^ s ≤ kstMainTerm s q t ^ s := by
    rw [kstMainTerm_pow hs]
    exact_mod_cast balanced_parts_kst_pow G hs h U W hU hW
  have hE : (E : ℝ) ≤ kstMainTerm s q t :=
    le_of_pow_le_pow_left₀ (by omega) (kstMainTerm_nonneg s q t) hk
  have hdegree : (adjacencyPairs G U W).card ≤ E + (s - 1) * t := by
    dsimp [E]
    omega
  have hdegree' : ((adjacencyPairs G U W).card : ℝ) ≤
      (E : ℝ) + ((s - 1 : ℕ) : ℝ) * t := by exact_mod_cast hdegree
  exact hdegree'.trans (add_le_add_right hE _)

/-- Adding equality conflicts replaces `s-1` by `s`. -/
theorem asymmetric_conflict_bound {s q t : ℕ} (hs : 1 ≤ s) (h : CodegreeBound G s q)
    (U W : Finset V) (hU : U.card = t) (hW : W.card = t) :
    ((conflictPairs G U W).card : ℝ) ≤ kstMainTerm s q t + (s : ℝ) * t := by
  have hk := asymmetric_kst G hs h U W hU hW
  have hc := card_conflictPairs_le G U W
  rw [hU] at hc
  have hc' : ((conflictPairs G U W).card : ℝ) ≤
      ((adjacencyPairs G U W).card : ℝ) + t := by exact_mod_cast hc
  have he : ((s - 1 : ℕ) : ℝ) = (s : ℝ) - 1 := by rw [Nat.cast_sub hs]; norm_num
  change _ ≤ kstMainTerm s q t + _ at hk
  rw [he] at hk
  linarith

/-- The balanced form quoted in the sparse-transversal argument. -/
theorem balanced_kst {d t : ℕ} (hd : 2 ≤ d) (h : BicliqueFree G d d)
    (U W : Finset V) (hU : U.card = t) (hW : W.card = t) :
    ((adjacencyPairs G U W).card : ℝ) ≤
      ((d - 1 : ℕ) : ℝ) ^ (1 / (d : ℝ)) * (t : ℝ) ^ (2 - 1 / (d : ℝ)) +
        ((d - 1 : ℕ) : ℝ) * t :=
  asymmetric_kst G (by omega)
    ((bicliqueFree_iff_codegreeBound G d d (by omega)).mp h) U W hU hW


/-- The normalized conflict density used throughout the paper. -/
noncomputable def codegreeDensity (s q t : ℕ) : ℝ :=
  (q : ℝ) ^ (1 / (s : ℝ)) * (t : ℝ) ^ (-(1 / (s : ℝ))) + (s : ℝ) / t

/-- Multiplying the normalized density by the number of ordered pairs recovers
the KST leading term plus the equality-corrected linear term. -/
theorem codegreeDensity_mul_square (s q : ℕ) {t : ℕ} (ht : 0 < t) :
    codegreeDensity s q t * (t : ℝ) ^ 2 = kstMainTerm s q t + (s : ℝ) * t := by
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  have hp : (t : ℝ) ^ (-(1 / (s : ℝ))) * (t : ℝ) ^ 2 =
      (t : ℝ) ^ (2 - 1 / (s : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add ht']
    congr 1
    norm_num
    ring
  unfold codegreeDensity kstMainTerm
  rw [add_mul, mul_assoc, hp]
  congr 1
  field_simp

/-- Graph-independent sharp balanced KST certificate. This is the integer
strict-tangent proof of the paper's analytic Lemma 4.3. -/
theorem balanced_kst_term_certificate {d Q t : ℕ} (hd : 2 ≤ d) (hQ : 0 < Q)
    (hT : t = (d - 1) * Q ^ d + d ^ 2 * Q) :
    (Q : ℝ) * (kstMainTerm d (d - 1) t + (d : ℝ) * t) < (t : ℝ) ^ 2 := by
  have hd1 : 1 ≤ d := by omega
  have hc : 0 < d * Q := Nat.mul_pos (by omega) hQ
  have hct : d * Q ≤ t := by
    have hm := Nat.mul_le_mul_right Q (Nat.le_self_pow (by decide : 2 ≠ 0) d)
    omega
  have ht : 0 < t := by omega
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  let a := t - d * Q
  have hac : a + d * Q = t := Nat.sub_add_cancel hct
  have hac' : (a : ℝ) + (d : ℝ) * Q = t := by exact_mod_cast hac
  have htangent : (t : ℝ) ^ d < (a : ℝ) ^ d +
      (d : ℝ) * ((d : ℝ) * Q) * (t : ℝ) ^ (d - 1) := by
    have hz := pow_add_lt_tangent a (d * Q) (d - 2) hc
    have h₁ : d - 2 + 2 = d := by omega
    have h₂ : d - 2 + 1 = d - 1 := by omega
    rw [h₁, h₂, hac] at hz
    exact_mod_cast hz
  by_contra hn
  have hlow : (t : ℝ) * a ≤ (Q : ℝ) * kstMainTerm d (d - 1) t := by
    push_neg at hn
    nlinarith only [hac', hn, sq_nonneg ((t : ℝ) - a)]
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (t : ℝ) * a) hlow d
  have hu : (t : ℝ) ^ d * (a : ℝ) ^ d ≤
      (t : ℝ) ^ d * (((d - 1 : ℕ) : ℝ) * (Q : ℝ) ^ d * (t : ℝ) ^ (d - 1)) := by
    calc
      _ = ((t : ℝ) * a) ^ d := (mul_pow _ _ _).symm
      _ ≤ ((Q : ℝ) * kstMainTerm d (d - 1) t) ^ d := hpow
      _ = (Q : ℝ) ^ d * (((d - 1 : ℕ) : ℝ) * (t : ℝ) ^ (2 * d - 1)) := by
        rw [mul_pow, kstMainTerm_pow hd1]
      _ = _ := by
        rw [show 2 * d - 1 = d + (d - 1) by omega, pow_add]
        ring
  have ha := (mul_le_mul_left (pow_pos ht' d)).mp hu
  have hcoef : ((d - 1 : ℕ) : ℝ) * (Q : ℝ) ^ d + (d : ℝ) * ((d : ℝ) * Q) = t := by
    have hT' : (t : ℝ) = ((d - 1 : ℕ) : ℝ) * (Q : ℝ) ^ d + (d : ℝ) ^ 2 * Q := by
      exact_mod_cast hT
    nlinarith only [hT']
  have hbound : (a : ℝ) ^ d + (d : ℝ) * ((d : ℝ) * Q) * (t : ℝ) ^ (d - 1) ≤
      (t : ℝ) ^ d := by
    calc
      _ ≤ (((d - 1 : ℕ) : ℝ) * (Q : ℝ) ^ d +
          (d : ℝ) * ((d : ℝ) * Q)) * (t : ℝ) ^ (d - 1) := by nlinarith only [ha]
      _ = (t : ℝ) ^ d := by
        rw [hcoef, ← pow_succ']
        congr 1
        omega
  exact (not_lt_of_ge hbound) htangent

/-- Literal normalized-density formulation of the explicit balanced threshold
lemma: `4(r-1) p_d(M(d,r)) < 1`. -/
theorem balancedThreshold_density_certificate {d r : ℕ} (hd : 2 ≤ d) (hr : 2 ≤ r) :
    (4 * (r - 1) : ℕ) * codegreeDensity d (d - 1) (balancedThreshold d r) < (1 : ℝ) := by
  let t := balancedThreshold d r
  have hQ : 0 < 4 * (r - 1) := by omega
  have hT : t = (d - 1) * (4 * (r - 1)) ^ d + d ^ 2 * (4 * (r - 1)) := by
    dsimp [t, balancedThreshold]
    ring
  have ht : 0 < t := by
    have hc : 0 < d ^ 2 * (4 * (r - 1)) := by positivity
    omega
  have h := balanced_kst_term_certificate hd hQ hT
  rw [← codegreeDensity_mul_square d (d - 1) ht, ← mul_assoc] at h
  have ht' : (0 : ℝ) < (t : ℝ) ^ 2 := by positivity
  apply (mul_lt_mul_right ht').mp
  simpa [t, Nat.cast_mul] using h

end IndependentSetDiscovery
