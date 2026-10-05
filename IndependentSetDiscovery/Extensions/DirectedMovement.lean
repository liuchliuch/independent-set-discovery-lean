import IndependentSetDiscovery.Basic
import IndependentSetDiscovery.Extensions.Arithmetic

/-!
# Directed weighted token movement

The movement model and exact scalarization used in Corollary 5.6.  The movement
relation is directed and independent of the undirected feasibility graph.
Weights here are natural numbers after clearing rational denominators.
-/

namespace IndependentSetDiscovery

variable {V : Type*} [DecidableEq V]

/-- A legal directed move, with no independence requirement on the state. -/
def DirectedTokenSlide (D : V → V → Prop) (Q Q' : Finset V) (u v : V) : Prop :=
  u ∈ Q ∧ v ∉ Q ∧ D u v ∧ Q' = insert v (Q.erase u)

/-- A collision-free directed sequence, indexed by both total cost and slides. -/
inductive DirectedSlideSequence (D : V → V → Prop) (w : V → V → ℕ) :
    Finset V → Finset V → ℕ → ℕ → Prop
  | nil (Q) : DirectedSlideSequence D w Q Q 0 0
  | cons {Q R T c n u v} : DirectedTokenSlide D Q R u v →
      DirectedSlideSequence D w R T c n →
      DirectedSlideSequence D w Q T (w u v + c) (n + 1)

theorem DirectedTokenSlide.card_eq {D : V → V → Prop} {Q Q' : Finset V} {u v : V}
    (h : DirectedTokenSlide D Q Q' u v) : Q'.card = Q.card := by
  rcases h with ⟨hu, hv, _, rfl⟩
  have hv' : v ∉ Q.erase u := fun h => hv (Finset.mem_of_mem_erase h)
  rw [Finset.card_insert_of_notMem hv', Finset.card_erase_of_mem hu]
  have : 0 < Q.card := Finset.card_pos.mpr ⟨u, hu⟩
  omega

theorem DirectedSlideSequence.card_eq {D : V → V → Prop} {w : V → V → ℕ}
    {Q T : Finset V} {c n : ℕ} (h : DirectedSlideSequence D w Q T c n) :
    T.card = Q.card := by
  induction h with
  | nil => rfl
  | cons hs _ ih => exact ih.trans hs.card_eq

theorem DirectedSlideSequence.trans {D : V → V → Prop} {w : V → V → ℕ}
    {Q R T : Finset V} {c d m n : ℕ}
    (h₁ : DirectedSlideSequence D w Q R c m)
    (h₂ : DirectedSlideSequence D w R T d n) :
    DirectedSlideSequence D w Q T (c + d) (m + n) := by
  induction h₁ with
  | nil => simpa using h₂
  | cons hs _ ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        DirectedSlideSequence.cons hs (ih h₂)

/-- Weighting each arc by `C*w+1` transforms a sequence's exact cost to
`C*cost+slides`, including when some original arcs have zero cost. -/
theorem DirectedSlideSequence.scalarize {D : V → V → Prop} {w : V → V → ℕ}
    {Q T : Finset V} {c n : ℕ} (h : DirectedSlideSequence D w Q T c n) (C : ℕ) :
    DirectedSlideSequence D (fun u v => C * w u v + 1) Q T (C * c + n) n := by
  induction h with
  | nil Q =>
      simpa using (DirectedSlideSequence.nil (D := D)
        (w := fun u v => C * w u v + 1) Q)
  | cons hs _ ih =>
      simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        DirectedSlideSequence.cons hs ih

/-- Scalarization changes the score, not the permitted moves or configurations. -/
theorem DirectedSlideSequence.unscalarize {D : V → V → Prop} {w : V → V → ℕ}
    {Q T : Finset V} {z n : ℕ} {C : ℕ}
    (h : DirectedSlideSequence D (fun u v => C * w u v + 1) Q T z n) :
    ∃ c, DirectedSlideSequence D w Q T c n ∧ z = C * c + n := by
  induction h with
  | nil => exact ⟨0, DirectedSlideSequence.nil _, by simp⟩
  | @cons Q R T z n u v hs _ ih =>
      obtain ⟨c, hc, rfl⟩ := ih
      exact ⟨w u v + c, DirectedSlideSequence.cons hs hc, by ring⟩

theorem scalarizedSequence_iff {D : V → V → Prop} {w : V → V → ℕ}
    {Q T : Finset V} {z n C : ℕ} :
    DirectedSlideSequence D (fun u v => C * w u v + 1) Q T z n ↔
      ∃ c, DirectedSlideSequence D w Q T c n ∧ z = C * c + n := by
  constructor
  · exact DirectedSlideSequence.unscalarize
  · rintro ⟨c, hc, rfl⟩
    exact hc.scalarize C

/-- On the bounded-slide witnesses used in the paper, scalar and lexicographic
comparison are exactly equivalent. -/
theorem boundedSequence_score_lt_iff {k n c c' b b' : ℕ}
    (hb : b ≤ k * (n - 1)) (hb' : b' ≤ k * (n - 1)) :
    scalarizationBase k n * c + b < scalarizationBase k n * c' + b' ↔
      c < c' ∨ c = c' ∧ b < b' :=
  scalar_lt_iff_lex (scalarizationBase_bound hb) (scalarizationBase_bound hb')

end IndependentSetDiscovery
