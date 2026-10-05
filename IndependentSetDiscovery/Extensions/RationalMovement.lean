import IndependentSetDiscovery.Extensions.DirectedReduction
import IndependentSetDiscovery.Algorithms.Scaling

/-! # Rational arc weights and exact common-denominator transfer -/

namespace IndependentSetDiscovery

variable {V : Type*} [DecidableEq V]

inductive RationalSlideSequence (D : V → V → Prop) (w : V → V → ℚ) :
    Finset V → Finset V → ℚ → ℕ → Prop
  | nil (Q) : RationalSlideSequence D w Q Q 0 0
  | cons {Q R T c n u v} : DirectedTokenSlide D Q R u v →
      RationalSlideSequence D w R T c n →
      RationalSlideSequence D w Q T (w u v + c) (n + 1)

theorem RationalSlideSequence.integerize
    {D : V → V → Prop} {w : V → V → ℚ} {z : V → V → ℕ} {C : ℕ}
    (hscale : ∀ u v, D u v → (z u v : ℚ) = C * w u v)
    {Q T : Finset V} {c : ℚ} {n : ℕ} (h : RationalSlideSequence D w Q T c n) :
    ∃ a : ℕ, DirectedSlideSequence D z Q T a n ∧ (a : ℚ) = C * c := by
  induction h with
  | nil Q => exact ⟨0, .nil Q, by simp⟩
  | @cons Q R T c n u v hs ht ih =>
      obtain ⟨a, ha, heq⟩ := ih
      refine ⟨z u v + a, .cons hs ha, ?_⟩
      push_cast
      rw [heq, hscale u v hs.2.2.1]
      ring

theorem DirectedSlideSequence.rationalize
    {D : V → V → Prop} {w : V → V → ℚ} {z : V → V → ℕ} {C : ℕ}
    (hscale : ∀ u v, D u v → (z u v : ℚ) = C * w u v)
    {Q T : Finset V} {a n : ℕ} (h : DirectedSlideSequence D z Q T a n) :
    ∃ c : ℚ, RationalSlideSequence D w Q T c n ∧ (a : ℚ) = C * c := by
  induction h with
  | nil Q => exact ⟨0, .nil Q, by simp⟩
  | @cons Q R T a n u v hs ht ih =>
      obtain ⟨c, hc, heq⟩ := ih
      refine ⟨w u v + c, .cons hs hc, ?_⟩
      push_cast
      rw [heq, hscale u v hs.2.2.1]
      ring

def RationalLexOptimal (Gf : SimpleGraph V) (D : V → V → Prop) (w : V → V → ℚ)
    (S T : Finset V) (c : ℚ) (n : ℕ) : Prop :=
  Independent Gf T ∧ RationalSlideSequence D w S T c n ∧
    ∀ T' c' n', Independent Gf T' → RationalSlideSequence D w S T' c' n' →
      c ≤ c' ∧ (c = c' → n ≤ n')

theorem rational_optimal_of_integerized [Fintype V]
    {Gf : SimpleGraph V} {D : V → V → Prop} {w : V → V → ℚ}
    {z : V → V → ℕ} {C : ℕ} (hC : 0 < C)
    (hscale : ∀ u v, D u v → (z u v : ℚ) = C * w u v)
    {S T : Finset V} {a n : ℕ} (h : WeightedDirected.LexOptimal Gf D z S T a n) :
    ∃ c : ℚ, RationalLexOptimal Gf D w S T c n ∧ (a : ℚ) = C * c := by
  obtain ⟨c, hc, ha⟩ := h.2.1.rationalize hscale
  refine ⟨c, ⟨h.1, hc, ?_⟩, ha⟩
  intro T' c' n' hT' hs'
  obtain ⟨a', ha', heq⟩ := hs'.integerize hscale
  obtain ⟨hle, hsecondary⟩ := h.2.2 T' a' n' hT' ha'
  have hpos : (0 : ℚ) < C := by exact_mod_cast hC
  have hle' : (a : ℚ) ≤ a' := by exact_mod_cast hle
  refine ⟨?_, ?_⟩
  · rw [ha, heq] at hle'
    exact (mul_le_mul_iff_right₀ hpos).mp hle'
  · intro heqcost
    apply hsecondary
    have : (a : ℚ) = a' := by rw [ha, heq, heqcost]
    exact_mod_cast this

namespace WeightedDirected

variable [Fintype V] (D : V → V → Prop) [DecidableRel D] (w : V → V → ℚ)

def arcCandidates (u : V) : Finset V := Finset.univ.filter (D u)

/-- Product of precisely the denominators of the finite directed arcs. -/
def arcDenominator : ℕ := Algorithms.commonDenominator Finset.univ (arcCandidates D) w

theorem arcDenominator_pos : 0 < arcDenominator D w :=
  Algorithms.commonDenominator_pos _ _ _

def integerArcWeight (u v : V) : ℕ := Algorithms.scaleCost (arcDenominator D w) (w u v)

theorem integerArcWeight_cast (hnonneg : ∀ u v, D u v → 0 ≤ w u v)
    (u v : V) (huv : D u v) :
    (integerArcWeight D w u v : ℚ) = arcDenominator D w * w u v := by
  apply Algorithms.scaleCost_cast _ _ (hnonneg u v huv)
  exact Algorithms.denominator_dvd_common Finset.univ (arcCandidates D) w
    u (Finset.mem_univ _) v (by simp [arcCandidates, huv])

/-- The denominator product is bounded by the sum of the input denominator
bit lengths, including the empty-arc graph. -/
theorem arcDenominator_le_pow :
    arcDenominator D w ≤ 2 ^ Algorithms.denominatorBits Finset.univ (arcCandidates D) w :=
  Algorithms.commonDenominator_le_pow _ _ _

/-- Rational-weight version of the exact two-graph static-to-movement transfer. -/
theorem rational_optimal_selection_realizes_lex (Gf : SimpleGraph V)
    (hnonneg : ∀ u v, D u v → 0 ≤ w u v)
    {S : Finset V} {x : S → V}
    (hx : (movementInstance Gf D
      (fun u v => scalarizationBase S.card (Fintype.card V) * integerArcWeight D w u v + 1)
      S).Optimal x) :
    ∃ T c n, RationalLexOptimal Gf D w S T c n ∧
      n ≤ S.card * (Fintype.card V - 1) := by
  obtain ⟨T, a, n, hopt, hlen⟩ := optimal_selection_realizes_lex hx
  obtain ⟨c, hc, _⟩ := rational_optimal_of_integerized (arcDenominator_pos D w)
    (integerArcWeight_cast D w hnonneg) hopt
  exact ⟨T, c, n, hc, hlen⟩

end WeightedDirected
end IndependentSetDiscovery
