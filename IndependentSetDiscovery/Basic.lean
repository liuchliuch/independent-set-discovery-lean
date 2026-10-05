import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Card

/-!
# Configurations and collision-free token slides

Definitions 2.1 and 2.2 of Liu--Meng, *Independent Set Discovery on
Biclique-Free Graphs Is Fixed-Parameter Tractable*, arXiv:2609.27837.
Intermediate configurations are arbitrary finite vertex sets. In particular,
`TokenSlide` deliberately does not require independence of either endpoint.
-/

namespace IndependentSetDiscovery

variable {V : Type*} [DecidableEq V]

/-- An unlabeled configuration is the finite set of occupied vertices. -/
abbrev Configuration (V : Type*) := Finset V

/-- No two distinct occupied vertices are adjacent. -/
def Independent (G : SimpleGraph V) (Q : Finset V) : Prop :=
  ∀ ⦃u⦄, u ∈ Q → ∀ ⦃v⦄, v ∈ Q → u ≠ v → ¬ G.Adj u v

/-- One occupied vertex moves across an edge into a previously empty vertex. -/
def TokenSlide (G : SimpleGraph V) (Q Q' : Finset V) : Prop :=
  ∃ u ∈ Q, ∃ v, v ∉ Q ∧ G.Adj u v ∧ Q' = insert v (Q.erase u)

/-- A collision-free sequence of exactly `n` slides. -/
inductive SlideSequence (G : SimpleGraph V) : Finset V → Finset V → ℕ → Prop
  | nil (Q) : SlideSequence G Q Q 0
  | cons {Q R T n} : TokenSlide G Q R → SlideSequence G R T n →
      SlideSequence G Q T (n + 1)

/-- Definition 2.2: an independent terminal configuration reached within budget. -/
def DiscoveryWithin (G : SimpleGraph V) (S : Finset V) (b : ℕ) : Prop :=
  ∃ T n, Independent G T ∧ SlideSequence G S T n ∧ n ≤ b

theorem TokenSlide.card_eq {G : SimpleGraph V} {Q Q' : Finset V}
    (h : TokenSlide G Q Q') : Q'.card = Q.card := by
  rcases h with ⟨u, hu, v, hv, huv, rfl⟩
  have hv' : v ∉ Q.erase u := fun h => hv (Finset.mem_of_mem_erase h)
  rw [Finset.card_insert_of_notMem hv', Finset.card_erase_of_mem hu]
  have : 0 < Q.card := Finset.card_pos.mpr ⟨u, hu⟩
  omega

theorem TokenSlide.symm {G : SimpleGraph V} {Q Q' : Finset V}
    (h : TokenSlide G Q Q') : TokenSlide G Q' Q := by
  rcases h with ⟨u, hu, v, hv, huv, rfl⟩
  have hne : u ≠ v := G.ne_of_adj huv
  refine ⟨v, Finset.mem_insert_self _ _, u, ?_, G.symm huv, ?_⟩
  · simp [hne]
  · ext x
    simp only [Finset.mem_insert, Finset.mem_erase]
    by_cases hxu : x = u <;> by_cases hxv : x = v <;> simp_all

theorem TokenSlide.ne {G : SimpleGraph V} {Q Q' : Finset V}
    (h : TokenSlide G Q Q') : Q ≠ Q' := by
  rcases h with ⟨u, hu, v, hv, huv, rfl⟩
  intro heq
  apply hv
  rw [heq]
  exact Finset.mem_insert_self _ _

theorem SlideSequence.card_eq {G : SimpleGraph V} {Q T : Finset V} {n : ℕ}
    (h : SlideSequence G Q T n) : T.card = Q.card := by
  induction h with
  | nil => rfl
  | cons hs _ ih => exact ih.trans hs.card_eq

theorem SlideSequence.trans {G : SimpleGraph V} {Q R T : Finset V} {m n : ℕ}
    (h₁ : SlideSequence G Q R m) (h₂ : SlideSequence G R T n) :
    SlideSequence G Q T (m + n) := by
  induction h₁ with
  | nil => simpa using h₂
  | cons hs _ ih => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      SlideSequence.cons hs (ih h₂)

theorem SlideSequence.reverse {G : SimpleGraph V} {Q T : Finset V} {n : ℕ}
    (h : SlideSequence G Q T n) : SlideSequence G T Q n := by
  induction h with
  | nil => exact SlideSequence.nil _
  | cons hs _ ih =>
      exact ih.trans (SlideSequence.cons hs.symm (SlideSequence.nil _))

theorem SlideSequence.eq_of_zero {G : SimpleGraph V} {Q T : Finset V}
    (h : SlideSequence G Q T 0) : Q = T := by
  cases h
  rfl

theorem Independent.mono {G : SimpleGraph V} {Q T : Finset V}
    (h : Independent G Q) (hT : T ⊆ Q) : Independent G T := by
  intro u hu v hv hne
  exact h (hT hu) (hT hv) hne

theorem DiscoveryWithin.mono {G : SimpleGraph V} {S : Finset V} {b c : ℕ}
    (h : DiscoveryWithin G S b) (hbc : b ≤ c) : DiscoveryWithin G S c := by
  rcases h with ⟨T, n, hi, hs, hn⟩
  exact ⟨T, n, hi, hs, hn.trans hbc⟩

theorem DiscoveryWithin.card_eq {G : SimpleGraph V} {S : Finset V} {b : ℕ}
    (h : DiscoveryWithin G S b) :
    ∃ T n, T.card = S.card ∧ Independent G T ∧ SlideSequence G S T n ∧ n ≤ b := by
  rcases h with ⟨T, n, hi, hs, hn⟩
  exact ⟨T, n, hs.card_eq, hi, hs, hn⟩

theorem independent_empty (G : SimpleGraph V) : Independent G ∅ := by
  simp [Independent]

theorem independent_singleton (G : SimpleGraph V) (v : V) : Independent G {v} := by
  simp [Independent]

theorem discoveryWithin_zero_iff (G : SimpleGraph V) (S : Finset V) :
    DiscoveryWithin G S 0 ↔ Independent G S := by
  constructor
  · rintro ⟨T, n, hi, hs, hn⟩
    have hn' : n = 0 := Nat.eq_zero_of_le_zero hn
    subst n
    cases hs
    exact hi
  · intro hi
    exact ⟨S, 0, hi, SlideSequence.nil S, le_rfl⟩

theorem Independent.discoveryWithin {G : SimpleGraph V} {S : Finset V}
    (h : Independent G S) (b : ℕ) : DiscoveryWithin G S b :=
  ⟨S, 0, h, SlideSequence.nil S, Nat.zero_le b⟩

theorem discoveryWithin_empty (G : SimpleGraph V) (b : ℕ) :
    DiscoveryWithin G ∅ b := (independent_empty G).discoveryWithin b

theorem discoveryWithin_singleton (G : SimpleGraph V) (v : V) (b : ℕ) :
    DiscoveryWithin G {v} b := (independent_singleton G v).discoveryWithin b

end IndependentSetDiscovery
