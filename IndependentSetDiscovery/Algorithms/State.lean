import IndependentSetDiscovery.Algorithms.SearchTree
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Rat.BigOperators

namespace IndependentSetDiscovery.Algorithms

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V]

/-- Residual data. Label-dependent candidates may overlap without restriction. -/
structure State (ι V : Type*) where
  labels : Finset ι
  candidates : ι → Finset V
  budget : ℚ

variable (R : V → V → Prop) [DecidableRel R] (cost : ι → V → ℚ)

/-- A completion of a residual state. `R` includes inequality as well as nonadjacency. -/
def Completion (s : State ι V) (x : ι → V) : Prop :=
  (∀ i ∈ s.labels, x i ∈ s.candidates i) ∧
  (∀ i ∈ s.labels, ∀ j ∈ s.labels, i ≠ j → R (x i) (x j)) ∧
  (∑ i ∈ s.labels, cost i (x i)) ≤ s.budget

def Feasible (s : State ι V) : Prop := ∃ x, Completion R cost s x

/-- A branch performs exactly one assignment and deletes every conflict with it. -/
def child (s : State ι V) (i : ι) (v : V) : State ι V where
  labels := s.labels.erase i
  budget := s.budget - cost i v
  candidates := fun j => (s.candidates j).filter fun u =>
    R v u ∧ cost j u ≤ s.budget - cost i v

/-- All initial single-vertex candidates are filtered to the budget. -/
def root (labels : Finset ι) (candidates : ι → Finset V) (budget : ℚ) : State ι V where
  labels := labels
  candidates := fun i => (candidates i).filter fun v => cost i v ≤ budget
  budget := budget

/-- This invariant is checked without assuming different candidate sets are disjoint. -/
def Affordable (s : State ι V) : Prop :=
  ∀ i ∈ s.labels, ∀ v ∈ s.candidates i, cost i v ≤ s.budget

theorem root_affordable (labels : Finset ι) (candidates : ι → Finset V) (budget : ℚ) :
    Affordable cost (root cost labels candidates budget) := by
  intro i hi v hv
  exact (Finset.mem_filter.mp hv).2

theorem child_affordable (s : State ι V) (i : ι) (v : V) :
    Affordable cost (child R cost s i v) := by
  intro j hj u hu
  exact (Finset.mem_filter.mp hu).2.2

theorem child_rank_lt (s : State ι V) (i : ι) (v : V) (hi : i ∈ s.labels) :
    (child R cost s i v).labels.card < s.labels.card := by
  exact Finset.card_erase_lt_of_mem hi

theorem completion_child_of_fixed
    (nonneg : ∀ i v, 0 ≤ cost i v) (s : State ι V) (i : ι) (v : V)
    (hi : i ∈ s.labels) (x : ι → V)
    (hx : Completion R cost s x) (hfix : x i = v) :
    Completion R cost (child R cost s i v) x := by
  rcases hx with ⟨hmem, hpair, hsum⟩
  have hsumerase : (∑ j ∈ s.labels.erase i, cost j (x j)) ≤ s.budget - cost i v := by
    have heq := Finset.sum_erase_add s.labels (fun j => cost j (x j)) hi
    dsimp only at heq
    rw [hfix] at heq
    linarith
  refine ⟨?_, ?_, hsumerase⟩
  · intro j hj
    have hj' : j ∈ s.labels.erase i := hj
    rcases Finset.mem_erase.mp hj' with ⟨hne, hjs⟩
    apply Finset.mem_filter.mpr
    refine ⟨hmem j hjs, ?_, ?_⟩
    · simpa [hfix] using hpair i hi j hjs (Ne.symm hne)
    · calc
        cost j (x j) ≤ ∑ a ∈ s.labels.erase i, cost a (x a) :=
          Finset.single_le_sum (fun a _ => nonneg a (x a)) hj'
        _ ≤ s.budget - cost i v := hsumerase
  · intro j hj a ha hne
    exact hpair j (Finset.mem_of_mem_erase hj) a (Finset.mem_of_mem_erase ha) hne

theorem completion_extend
    (symm : Symmetric R) (s : State ι V) (i : ι) (v : V)
    (hi : i ∈ s.labels) (hv : v ∈ s.candidates i) (x : ι → V)
    (hx : Completion R cost (child R cost s i v) x) :
    Completion R cost s (Function.update x i v) := by
  rcases hx with ⟨hmem, hpair, hsum⟩
  have hupdate : ∀ j ∈ s.labels.erase i, Function.update x i v j = x j := by
    intro j hj
    exact Function.update_of_ne (Finset.mem_erase.mp hj).1 v x
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    by_cases hji : j = i
    · subst j; simpa using hv
    · have hj' : j ∈ s.labels.erase i := Finset.mem_erase.mpr ⟨hji, hj⟩
      rw [hupdate j hj']
      exact (Finset.mem_filter.mp (hmem j hj')).1
  · intro j hj a ha hja
    by_cases hji : j = i
    · subst j
      have ha' : a ∈ s.labels.erase i := Finset.mem_erase.mpr ⟨Ne.symm hja, ha⟩
      simp only [Function.update_self, hupdate a ha']
      exact (Finset.mem_filter.mp (hmem a ha')).2.1
    · have hj' : j ∈ s.labels.erase i := Finset.mem_erase.mpr ⟨hji, hj⟩
      rw [hupdate j hj']
      by_cases hai : a = i
      · subst a
        simp only [Function.update_self]
        exact symm (Finset.mem_filter.mp (hmem j hj')).2.1
      · have ha' : a ∈ s.labels.erase i := Finset.mem_erase.mpr ⟨hai, ha⟩
        rw [hupdate a ha']
        exact hpair j hj' a ha' hja
  · have heq := Finset.sum_erase_add s.labels
      (fun j => cost j (Function.update x i v j)) hi
    have hsame : (∑ j ∈ s.labels.erase i, cost j (Function.update x i v j)) =
        ∑ j ∈ s.labels.erase i, cost j (x j) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hupdate j hj]
    dsimp only at heq
    rw [hsame, Function.update_self] at heq
    change (∑ j ∈ s.labels.erase i, cost j (x j)) ≤ s.budget - cost i v at hsum
    linarith

theorem feasible_child_iff
    (symm : Symmetric R) (nonneg : ∀ i v, 0 ≤ cost i v)
    (s : State ι V) (i : ι) (v : V) (hi : i ∈ s.labels) (hv : v ∈ s.candidates i) :
    Feasible R cost (child R cost s i v) ↔
      ∃ x, Completion R cost s x ∧ x i = v := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨Function.update x i v, completion_extend R cost symm s i v hi hv x hx, by simp⟩
  · rintro ⟨x, hx, hfix⟩
    exact ⟨x, completion_child_of_fixed R cost nonneg s i v hi x hx hfix⟩

theorem feasible_iff_some_child
    (symm : Symmetric R) (nonneg : ∀ i v, 0 ≤ cost i v)
    (s : State ι V) (i : ι) (hi : i ∈ s.labels) :
    Feasible R cost s ↔ ∃ v ∈ s.candidates i, Feasible R cost (child R cost s i v) := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x i, hx.1 i hi, x, completion_child_of_fixed R cost nonneg s i (x i) hi x hx rfl⟩
  · rintro ⟨v, hv, x, hx⟩
    exact ⟨Function.update x i v, completion_extend R cost symm s i v hi hv x hx⟩

end IndependentSetDiscovery.Algorithms
