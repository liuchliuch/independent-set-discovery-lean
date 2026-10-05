import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Fold
import Mathlib.Data.List.Sort
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Cost-ordered prefixes

The finite, executable cost-ordering and the cost-only half of Lemma 4.5.
The first sort fixes a deterministic order for ties; the stable cost sort then
orders by nondecreasing cost. No graph assumption is needed in this file.
-/
namespace IndependentSetDiscovery

open Finset

variable {V : Type*} [LinearOrder V]

/-- A deterministic list of the candidates in nondecreasing cost order. -/
def costOrdered (c : V → ℚ) (A : Finset V) : List V :=
  (A.sort (· ≤ ·)).mergeSort (fun u v => decide (c u ≤ c v))

/-- The first `t` cheapest candidates, with fixed tie breaking. -/
def cheapPrefix (c : V → ℚ) (A : Finset V) (t : ℕ) : Finset V :=
  ((costOrdered c A).take t).toFinset

@[simp] theorem mem_costOrdered (c : V → ℚ) (A : Finset V) (v : V) :
    v ∈ costOrdered c A ↔ v ∈ A := by
  simp [costOrdered]

@[simp] theorem length_costOrdered (c : V → ℚ) (A : Finset V) :
    (costOrdered c A).length = A.card := by
  simp [costOrdered]

theorem nodup_costOrdered (c : V → ℚ) (A : Finset V) :
    (costOrdered c A).Nodup := by
  exact (A.sort_nodup (· ≤ ·)).mergeSort

theorem sorted_costOrdered (c : V → ℚ) (A : Finset V) :
    (costOrdered c A).Sorted (fun u v => c u ≤ c v) := by
  unfold costOrdered
  simpa using List.sorted_mergeSort
    (le := fun u v => decide (c u ≤ c v))
    (by intro a b d hab hbd; simpa using
      le_trans (of_decide_eq_true hab) (of_decide_eq_true hbd))
    (by intro a b; simpa using le_total (c a) (c b))
    (A.sort (· ≤ ·))

theorem cheapPrefix_subset (c : V → ℚ) (A : Finset V) (t : ℕ) :
    cheapPrefix c A t ⊆ A := by
  intro v hv
  exact (mem_costOrdered c A v).mp
    (List.mem_of_mem_take (List.mem_toFinset.mp hv))

@[simp] theorem card_cheapPrefix (c : V → ℚ) (A : Finset V) (t : ℕ) :
    (cheapPrefix c A t).card = min t A.card := by
  rw [cheapPrefix, List.toFinset_card_of_nodup ((nodup_costOrdered c A).take),
    List.length_take, length_costOrdered]

theorem cheapPrefix_cost_le_outside (c : V → ℚ) (A : Finset V) (t : ℕ)
    {u v : V} (hu : u ∈ cheapPrefix c A t) (hv : v ∈ A)
    (hv' : v ∉ cheapPrefix c A t) : c u ≤ c v := by
  apply (sorted_costOrdered c A).rel_of_mem_take_of_mem_drop
    (List.mem_toFinset.mp hu)
  have hm : v ∈ costOrdered c A := (mem_costOrdered c A v).mpr hv
  rw [← List.take_append_drop t (costOrdered c A), List.mem_append] at hm
  exact hm.resolve_left (by simpa [cheapPrefix] using hv')

/-- Maximum cost, with zero as the empty-prefix default. -/
def prefixMax (c : V → ℚ) (P : Finset V) : ℚ := P.fold max 0 c

theorem prefixMax_nonneg (c : V → ℚ) (P : Finset V) : 0 ≤ prefixMax c P := by
  classical
  induction P using Finset.induction_on with
  | empty => simp [prefixMax]
  | @insert v P hv ih =>
      rw [prefixMax, Finset.fold_insert hv]
      exact le_max_of_le_right ih

theorem cost_le_prefixMax (c : V → ℚ) (P : Finset V) {v : V} (hv : v ∈ P) :
    c v ≤ prefixMax c P := by
  classical
  induction P using Finset.induction_on with
  | empty => simp at hv
  | @insert w P hw ih =>
      rw [prefixMax, Finset.fold_insert hw]
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact le_max_left _ _
      · exact le_max_of_le_right (ih hv)

theorem prefixMax_le (c : V → ℚ) (P : Finset V) {b : ℚ} (hb : 0 ≤ b)
    (h : ∀ v ∈ P, c v ≤ b) : prefixMax c P ≤ b := by
  classical
  induction P using Finset.induction_on with
  | empty => simpa [prefixMax] using hb
  | @insert w P hw ih =>
      rw [prefixMax, Finset.fold_insert hw]
      exact max_le (h _ (by simp)) (ih (fun v hv => h v (by simp [hv])))

theorem cheapPrefix_max_le_outside (c : V → ℚ) (A : Finset V) (t : ℕ)
    (hc : ∀ v ∈ A, 0 ≤ c v) {v : V} (hv : v ∈ A)
    (hv' : v ∉ cheapPrefix c A t) : prefixMax c (cheapPrefix c A t) ≤ c v := by
  exact prefixMax_le _ _ (hc v hv) fun u hu =>
    cheapPrefix_cost_le_outside c A t hu hv hv'

/-- Every selection from affordable prefixes is affordable (Lemma 4.5(a), cost part). -/
theorem affordable_prefix_selection {ι : Type*} [Fintype ι]
    (c : ι → V → ℚ) (P : ι → Finset V) (B : ℚ)
    (hB : (∑ i, prefixMax (c i) (P i)) ≤ B)
    (x : ι → V) (hx : ∀ i, x i ∈ P i) : (∑ i, c i (x i)) ≤ B := by
  exact (Finset.sum_le_sum (fun i _ => cost_le_prefixMax (c i) (P i) (hx i))).trans hB

/-- An affordable selection must meet at least one collectively over-budget prefix. -/
theorem expensive_prefix_selection_meets {ι : Type*} [Fintype ι]
    (c : ι → V → ℚ) (A : ι → Finset V) (t : ℕ) (B : ℚ)
    (hc : ∀ i v, v ∈ A i → 0 ≤ c i v)
    (hB : B < ∑ i, prefixMax (c i) (cheapPrefix (c i) (A i) t))
    (x : ι → V) (hx : ∀ i, x i ∈ A i) (hcost : (∑ i, c i (x i)) ≤ B) :
    ∃ i, x i ∈ cheapPrefix (c i) (A i) t := by
  by_contra h
  push_neg at h
  have hle : (∑ i, prefixMax (c i) (cheapPrefix (c i) (A i) t)) ≤
      ∑ i, c i (x i) := by
    exact Finset.sum_le_sum (fun i _ =>
      cheapPrefix_max_le_outside (c i) (A i) t (hc i) (hx i) (h i))
  exact (not_lt_of_ge (hle.trans hcost)) hB

/-- Active-label version of the affordable-prefix cost certificate. -/
theorem affordable_prefix_selection_on {ι : Type*} (L : Finset ι)
    (c : ι → V → ℚ) (P : ι → Finset V) (B : ℚ)
    (hB : (∑ i ∈ L, prefixMax (c i) (P i)) ≤ B)
    (x : ι → V) (hx : ∀ i ∈ L, x i ∈ P i) : (∑ i ∈ L, c i (x i)) ≤ B := by
  exact (Finset.sum_le_sum (fun i hi => cost_le_prefixMax (c i) (P i) (hx i hi))).trans hB

/-- Active-label version of the exhaustive over-budget branching certificate. -/
theorem expensive_prefix_selection_meets_on {ι : Type*} (L : Finset ι)
    (c : ι → V → ℚ) (A : ι → Finset V) (t : ℕ) (B : ℚ)
    (hc : ∀ i v, v ∈ A i → 0 ≤ c i v)
    (hB : B < ∑ i ∈ L, prefixMax (c i) (cheapPrefix (c i) (A i) t))
    (x : ι → V) (hx : ∀ i ∈ L, x i ∈ A i)
    (hcost : (∑ i ∈ L, c i (x i)) ≤ B) :
    ∃ i ∈ L, x i ∈ cheapPrefix (c i) (A i) t := by
  by_contra h
  push_neg at h
  have hle : (∑ i ∈ L, prefixMax (c i) (cheapPrefix (c i) (A i) t)) ≤
      ∑ i ∈ L, c i (x i) := by
    exact Finset.sum_le_sum (fun i hi =>
      cheapPrefix_max_le_outside (c i) (A i) t (hc i) (hx i hi) (h i hi))
  exact (not_lt_of_ge (hle.trans hcost)) hB

end IndependentSetDiscovery
