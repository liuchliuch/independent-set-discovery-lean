import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic

/-!
# Exact threshold and scalarization arithmetic

The integer thresholds in Section 5 of Liu--Meng, and the scalarization used
in Corollary 5.6.  All definitions in this file are executable natural-number
functions; in particular the edge threshold uses integer square root.
-/

namespace IndependentSetDiscovery

/-- The least integer greater than or equal to the square root. -/
def ceilSqrt (n : ℕ) : ℕ :=
  if n.sqrt ^ 2 = n then n.sqrt else n.sqrt + 1

theorem le_ceilSqrt_sq (n : ℕ) : n ≤ ceilSqrt n ^ 2 := by
  unfold ceilSqrt
  split_ifs with h
  · omega
  · exact (Nat.lt_succ_sqrt' n).le

theorem ceilSqrt_le_sqrt_add_one (n : ℕ) : ceilSqrt n ≤ n.sqrt + 1 := by
  unfold ceilSqrt
  split_ifs <;> omega

theorem ceilSqrt_le_iff (n q : ℕ) : ceilSqrt n ≤ q ↔ n ≤ q ^ 2 := by
  constructor
  · intro h
    exact (le_ceilSqrt_sq n).trans (Nat.pow_le_pow_left h 2)
  · intro h
    unfold ceilSqrt
    split_ifs with heq
    · have hs := Nat.sqrt_le' n
      nlinarith
    · have hs := Nat.sqrt_le' n
      have hslt : n.sqrt ^ 2 < n := by omega
      have : n.sqrt < q := by nlinarith
      omega

/-- Equation (11), using `ceilSqrt (16*m*(r-1)) = ceil (4*sqrt(m*(r-1)))`. -/
def edgePrefixThreshold (m r : ℕ) : ℕ :=
  8 * (r - 1) + ceilSqrt (16 * m * (r - 1)) + 1

theorem edgePrefixThreshold_pos (m r : ℕ) : 0 < edgePrefixThreshold m r := by
  unfold edgePrefixThreshold
  omega

theorem eight_mul_lt_edgePrefixThreshold (m r : ℕ) :
    8 * (r - 1) < edgePrefixThreshold m r := by
  unfold edgePrefixThreshold
  omega

theorem sixteen_mul_lt_edgePrefixThreshold_sq (m r : ℕ) :
    16 * m * (r - 1) < edgePrefixThreshold m r ^ 2 := by
  have h := le_ceilSqrt_sq (16 * m * (r - 1))
  have hlt : ceilSqrt (16 * m * (r - 1)) < edgePrefixThreshold m r := by
    unfold edgePrefixThreshold
    omega
  nlinarith

theorem edgePrefixThreshold_nat_certificate (m r : ℕ) :
    4 * (r - 1) * (2 * m + edgePrefixThreshold m r) < edgePrefixThreshold m r ^ 2 := by
  have hlin := eight_mul_lt_edgePrefixThreshold m r
  have hsq := sixteen_mul_lt_edgePrefixThreshold_sq m r
  have hpos := edgePrefixThreshold_pos m r
  have hquad := Nat.mul_lt_mul_of_pos_right hlin hpos
  nlinarith

/-- The strict sparse-prefix inequality needed by Theorem 5.2. -/
theorem edgePrefixThreshold_certificate (m r : ℕ) :
    4 * (r - 1 : ℕ) *
      (2 * (m : ℚ) / (edgePrefixThreshold m r : ℚ) ^ 2 +
        1 / (edgePrefixThreshold m r : ℚ)) < 1 := by
  have hpos : 0 < (edgePrefixThreshold m r : ℚ) := by
    exact_mod_cast edgePrefixThreshold_pos m r
  have hlin : (8 : ℚ) * (r - 1 : ℕ) < edgePrefixThreshold m r := by
    exact_mod_cast eight_mul_lt_edgePrefixThreshold m r
  have hsq : (16 : ℚ) * m * (r - 1 : ℕ) < (edgePrefixThreshold m r : ℚ) ^ 2 := by
    exact_mod_cast sixteen_mul_lt_edgePrefixThreshold_sq m r
  have hquad : (8 : ℚ) * (r - 1 : ℕ) * edgePrefixThreshold m r <
      (edgePrefixThreshold m r : ℚ) ^ 2 := by
    nlinarith
  apply (mul_lt_mul_iff_left₀ (sq_pos_of_pos hpos)).mp
  field_simp
  nlinarith

/-- Equation (12), the direct bounded-degeneracy threshold. -/
def degeneracyPrefixThreshold (a r : ℕ) : ℕ :=
  4 * (r - 1) * (4 * a + 1) + 1

theorem degeneracyPrefixThreshold_pos (a r : ℕ) :
    0 < degeneracyPrefixThreshold a r := by
  unfold degeneracyPrefixThreshold
  omega

theorem degeneracyPrefixThreshold_nat_certificate (a r : ℕ) :
    4 * (r - 1) * (4 * a * degeneracyPrefixThreshold a r + degeneracyPrefixThreshold a r) <
      degeneracyPrefixThreshold a r ^ 2 := by
  have hpos := degeneracyPrefixThreshold_pos a r
  have heq : degeneracyPrefixThreshold a r = 4 * (r - 1) * (4 * a + 1) + 1 := rfl
  nlinarith

/-- The strict sparse-prefix inequality needed by Theorem 5.3. -/
theorem degeneracyPrefixThreshold_certificate (a r : ℕ) :
    4 * (r - 1 : ℕ) * ((4 * (a : ℚ) + 1) / degeneracyPrefixThreshold a r) < 1 := by
  have hpos : (0 : ℚ) < degeneracyPrefixThreshold a r := by
    exact_mod_cast degeneracyPrefixThreshold_pos a r
  rw [← mul_div_assoc]
  apply (div_lt_one hpos).mpr
  unfold degeneracyPrefixThreshold
  push_cast
  linarith

/-- Bounded secondary coordinates allow exact lexicographic scalarization. -/
theorem scalar_lt_iff_lex {C a a' b b' : ℕ} (hb : b < C) (hb' : b' < C) :
    C * a + b < C * a' + b' ↔ a < a' ∨ a = a' ∧ b < b' := by
  constructor
  · intro h
    by_cases haa : a < a'
    · exact Or.inl haa
    have hle : a' ≤ a := Nat.le_of_not_gt haa
    rcases hle.eq_or_lt with heq | hlt
    · right
      subst a'
      exact ⟨rfl, by omega⟩
    · have hm := Nat.mul_le_mul_left C (Nat.succ_le_of_lt hlt)
      nlinarith
  · rintro (haa | ⟨rfl, hbb⟩)
    · have hm := Nat.mul_le_mul_left C (Nat.succ_le_of_lt haa)
      nlinarith
    · omega

theorem scalar_eq_iff {C a a' b b' : ℕ} (hb : b < C) (hb' : b' < C) :
    C * a + b = C * a' + b' ↔ a = a' ∧ b = b' := by
  constructor
  · intro h
    have h₁ : ¬ (a < a' ∨ a = a' ∧ b < b') := by
      rw [← scalar_lt_iff_lex hb hb']
      omega
    have h₂ : ¬ (a' < a ∨ a' = a ∧ b' < b) := by
      rw [← scalar_lt_iff_lex hb' hb]
      omega
    omega
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Every tuple of `k` simple paths has a secondary coordinate below this bound. -/
def scalarizationBase (k n : ℕ) : ℕ := k * (n - 1) + 1

theorem scalarizationBase_bound {k n b : ℕ} (hb : b ≤ k * (n - 1)) :
    b < scalarizationBase k n := by
  unfold scalarizationBase
  omega

theorem scalarization_sum {ι : Type*} (s : Finset ι) (C : ℕ) (w : ι → ℕ) :
    (∑ e ∈ s, (C * w e + 1)) = C * (∑ e ∈ s, w e) + s.card := by
  simp [Finset.sum_add_distrib, Finset.mul_sum]

end IndependentSetDiscovery
