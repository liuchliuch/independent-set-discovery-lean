import IndependentSetDiscovery.PaperStructural
import IndependentSetDiscovery.Transversal.Certificates
import IndependentSetDiscovery.Algorithms.EagerCompleteBounds
import IndependentSetDiscovery.Algorithms.WeightedSolver

/-! # Nonmonotone supplied thresholds in Lemma 5.1

Only the supplied ranks 2 through k are used. Terminal ranks use L(2), and
unreachable ranks above k use L(k). No monotonicity of L is assumed.
-/

namespace IndependentSetDiscovery

def suppliedThreshold (k : ℕ) (L : ℕ → ℕ) (r : ℕ) : ℕ :=
  L (max 2 (min r k))

def suppliedThresholdMax (k : ℕ) (L : ℕ → ℕ) : ℕ :=
  (Finset.Icc 2 k).sup L

theorem suppliedThreshold_eq {k r : ℕ} (L : ℕ → ℕ)
    (hr : 2 ≤ r) (hrk : r ≤ k) : suppliedThreshold k L r = L r := by
  simp [suppliedThreshold, min_eq_left hrk, max_eq_right hr]

theorem suppliedThreshold_pos {k : ℕ} (hk : 2 ≤ k) (L : ℕ → ℕ)
    (positive : ∀ r, 2 ≤ r → r ≤ k → 0 < L r) (r : ℕ) :
    0 < suppliedThreshold k L r := by
  apply positive
  · exact le_max_left _ _
  · exact max_le hk (min_le_right _ _)

theorem suppliedThreshold_le_max {k : ℕ} (hk : 2 ≤ k) (L : ℕ → ℕ) (r : ℕ) :
    suppliedThreshold k L r ≤ suppliedThresholdMax k L := by
  unfold suppliedThreshold suppliedThresholdMax
  apply Finset.le_sup
  exact Finset.mem_Icc.mpr ⟨le_max_left _ _, max_le hk (min_le_right _ _)⟩

variable {ι V : Type*} [Fintype ι] [Fintype V]
  [LinearOrder ι] [LinearOrder V] [Inhabited V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem supplied_sparse_certificate
    (hk : 2 ≤ Fintype.card ι) (L : ℕ → ℕ) (γ : ℕ → ℝ)
    (positive : ∀ r, 2 ≤ r → r ≤ Fintype.card ι → 0 < L r)
    (hlocal : ∀ t, 0 < t → ∀ U W : Finset V, U.card = t → W.card = t →
      ((adjacencyPairs G U W).card : ℝ) ≤ γ t * (t : ℝ)^2)
    (hdensity : ∀ r, 2 ≤ r → r ≤ Fintype.card ι →
      4 * ((r - 1 : ℕ) : ℝ) * (γ (L r) + 1 / (L r : ℝ)) < 1) :
    Algorithms.TransversalCertificate (ι := ι) (Compatible G)
      (suppliedThreshold (Fintype.card ι) L) := by
  intro J A hJ hsize
  have hJk : J.card ≤ Fintype.card ι := Finset.card_le_univ _
  by_cases hr : 2 ≤ J.card
  · apply extend_representatives (Compatible G) J A
    have ht := positive J.card hr hJk
    have ht' : (0 : ℝ) < L J.card := by exact_mod_cast ht
    have hd := hdensity J.card hr hJk
    have heq : (γ (L J.card) + 1 / (L J.card : ℝ)) * (L J.card : ℝ)^2 =
        γ (L J.card) * (L J.card : ℝ)^2 + L J.card := by
      field_simp
      <;> ring
    apply sparse_prefix_transversal G (fun t => γ t * (t : ℝ)^2)
      (L J.card) ht (by simpa using hr)
    · intro U W hU hW
      exact hlocal _ ht U W hU hW
    · have hp := mul_lt_mul_of_pos_right hd (sq_pos_of_pos ht')
      simpa only [Fintype.card_coe, mul_assoc, heq, one_mul] using hp
    · intro i
      simpa only [Fintype.card_coe, suppliedThreshold_eq L hr hJk] using hsize i.val i.property
  · have hcard : J.card = 1 := by have := Finset.card_pos.mpr hJ; omega
    exact singleton_representatives (Compatible G) J A hcard
      (suppliedThreshold_pos hk L positive _) hsize

/-- The exact nonmonotone maximum controls the actual measured optimizer. -/
theorem supplied_sparse_optimizer_work {k n : ℕ} [Inhabited (Fin n)]
    (R : Fin n → Fin n → Prop) [DecidableRel R] (cost : Fin k → Fin n → ℚ)
    (hk : 2 ≤ k) (L : ℕ → ℕ)
    (rows : Vector (Finset (Fin n)) k) :
    (Algorithms.optimizeEagerComplete R cost (suppliedThreshold k L) Finset.univ rows).2 ≤
      (6*Algorithms.numericSize Finset.univ (fun i => rows[i]) cost+6+(k+1)*(n+1)) *
        (128*(k+1)^2*(n+1)^2) *
          Algorithms.treeBound (k*suppliedThresholdMax k L) k := by
  exact Algorithms.optimizeEagerComplete_cost_le R cost _ _
    (fun r _ => suppliedThreshold_le_max hk L r) Finset.univ rows

end IndependentSetDiscovery
