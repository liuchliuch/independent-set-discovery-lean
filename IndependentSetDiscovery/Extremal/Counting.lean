import IndependentSetDiscovery.Extremal.Basic
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Analysis.MeanInequalities

/-!
# The asymmetric Kővári–Sós–Turán counting inequality

We double-count incidences between right vertices and `s`-element subsets of
their left neighborhoods. Descending factorials and the finite power-mean
inequality give the sharp KST estimate in a root-free, natural-number form.
-/

namespace IndependentSetDiscovery

open Finset

variable {V : Type*} [DecidableEq V] [Fintype V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The `s`-subsets of a neighborhood are precisely the `s`-subsets whose
vertices are all adjacent to the given right vertex. -/
theorem neighborhood_powersetCard (U : Finset V) (v : V) (s : ℕ) :
    (U.powersetCard s).filter (fun X => ∀ x ∈ X, G.Adj x v) =
      (leftNeighbors G U v).powersetCard s := by
  ext X
  simp only [mem_filter, mem_powersetCard]
  constructor
  · rintro ⟨⟨hsub, hcard⟩, hAdj⟩
    refine ⟨?_, hcard⟩
    intro x hx
    exact (mem_leftNeighbors G).mpr ⟨hsub hx, hAdj x hx⟩
  · rintro ⟨hsub, hcard⟩
    refine ⟨⟨?_, hcard⟩, ?_⟩
    · intro x hx
      exact ((mem_leftNeighbors G).mp (hsub hx)).1
    · intro x hx
      exact ((mem_leftNeighbors G).mp (hsub hx)).2

/-- Exact incidence double counting, before imposing any forbidden subgraph. -/
theorem sum_choose_leftNeighbors (U W : Finset V) (s : ℕ) :
    (∑ v ∈ W, ((leftNeighbors G U v).card).choose s) =
      ∑ X ∈ U.powersetCard s,
        (W.filter fun v => ∀ x ∈ X, G.Adj x v).card := by
  have h := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (fun (X : Finset V) (v : V) => ∀ x ∈ X, G.Adj x v)
    (s := U.powersetCard s) (t := W)
  simp only [bipartiteAbove, bipartiteBelow, neighborhood_powersetCard,
    card_powersetCard] at h
  exact h.symm

/-- The standard forbidden-biclique incidence estimate. -/
theorem sum_choose_leftNeighbors_le {s q : ℕ} (h : CodegreeBound G s q)
    (U W : Finset V) :
    (∑ v ∈ W, ((leftNeighbors G U v).card).choose s) ≤ q * U.card.choose s := by
  rw [sum_choose_leftNeighbors]
  calc
    _ ≤ ∑ _X ∈ U.powersetCard s, q := by
      apply sum_le_sum
      intro X hX
      exact card_commonNeighbors_filter_le G h X W (mem_powersetCard.mp hX).2
    _ = q * U.card.choose s := by simp [card_powersetCard, Nat.mul_comm]

/-- The amount of a degree above the exceptional `s-1` contribution. -/
def excessDegree (U : Finset V) (s : ℕ) (v : V) : ℕ :=
  (leftNeighbors G U v).card + 1 - s

/-- Polynomial-moment form of the incidence estimate. -/
theorem sum_excessDegree_pow_le {s q : ℕ} (h : CodegreeBound G s q)
    (U W : Finset V) :
    (∑ v ∈ W, excessDegree G U s v ^ s) ≤ q * U.card ^ s := by
  calc
    _ ≤ ∑ v ∈ W, ((leftNeighbors G U v).card).descFactorial s := by
      apply sum_le_sum
      intro v _
      exact Nat.pow_sub_le_descFactorial _ _
    _ = s.factorial * ∑ v ∈ W, ((leftNeighbors G U v).card).choose s := by
      simp only [Nat.descFactorial_eq_factorial_mul_choose, mul_sum]
    _ ≤ s.factorial * (q * U.card.choose s) :=
      Nat.mul_le_mul_left _ (sum_choose_leftNeighbors_le G h U W)
    _ = q * U.card.descFactorial s := by
      rw [Nat.descFactorial_eq_factorial_mul_choose]
      ring
    _ ≤ q * U.card ^ s := Nat.mul_le_mul_left q (Nat.descFactorial_le_pow _ _)

/-- Natural-number power mean, obtained by casting the finite real inequality. -/
theorem nat_sum_pow_le_card_mul_sum_pow {α : Type*} (S : Finset α) (f : α → ℕ)
    {s : ℕ} (hs : 1 ≤ s) :
    (∑ x ∈ S, f x) ^ s ≤ S.card ^ (s - 1) * ∑ x ∈ S, (f x) ^ s := by
  have hs' : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have h := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg S
    (f := fun x => (f x : ℝ)) hs' (fun _ _ => Nat.cast_nonneg _)
  have hexp : (s : ℝ) - 1 = ((s - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hs]
    norm_num
  rw [hexp] at h
  simp only [Real.rpow_natCast] at h
  exact_mod_cast h

/-- Separating the exceptional `s-1` part of every right degree. -/
theorem card_adjacencyPairs_le_sum_excessDegree {s : ℕ} (hs : 1 ≤ s)
    (U W : Finset V) :
    (adjacencyPairs G U W).card ≤
      (∑ v ∈ W, excessDegree G U s v) + (s - 1) * W.card := by
  rw [card_adjacencyPairs]
  calc
    _ ≤ ∑ v ∈ W, (excessDegree G U s v + (s - 1)) := by
      apply sum_le_sum
      intro v _
      unfold excessDegree
      omega
    _ = _ := by simp [sum_add_distrib, Nat.mul_comm]

/-- Asymmetric Kővári–Sós–Turán in an exact root-free form. It permits
arbitrary overlap between the original left and right candidate sets. -/
theorem asymmetric_kst_pow {s q : ℕ} (hs : 1 ≤ s) (h : CodegreeBound G s q)
    (U W : Finset V) :
    ((adjacencyPairs G U W).card - (s - 1) * W.card) ^ s ≤
      q * U.card ^ s * W.card ^ (s - 1) := by
  have hdeg := card_adjacencyPairs_le_sum_excessDegree G hs U W
  have hsub : (adjacencyPairs G U W).card - (s - 1) * W.card ≤
      ∑ v ∈ W, excessDegree G U s v := by omega
  calc
    _ ≤ (∑ v ∈ W, excessDegree G U s v) ^ s := Nat.pow_le_pow_left hsub s
    _ ≤ W.card ^ (s - 1) * ∑ v ∈ W, excessDegree G U s v ^ s :=
      nat_sum_pow_le_card_mul_sum_pow W _ hs
    _ ≤ W.card ^ (s - 1) * (q * U.card ^ s) :=
      Nat.mul_le_mul_left _ (sum_excessDegree_pow_le G h U W)
    _ = _ := by ring

/-- The square-parts form used for equal-size candidate prefixes. -/
theorem balanced_parts_kst_pow {s q t : ℕ} (hs : 1 ≤ s) (h : CodegreeBound G s q)
    (U W : Finset V) (hU : U.card = t) (hW : W.card = t) :
    ((adjacencyPairs G U W).card - (s - 1) * t) ^ s ≤ q * t ^ (2 * s - 1) := by
  have hk := asymmetric_kst_pow G hs h U W
  rw [hU, hW, mul_assoc, ← pow_add] at hk
  have he : s + (s - 1) = 2 * s - 1 := by omega
  simpa [he] using hk

end IndependentSetDiscovery
