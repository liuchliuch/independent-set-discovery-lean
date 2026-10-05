import IndependentSetDiscovery.Weighted
import Mathlib.Algebra.BigOperators.Group.Finset.Pi

namespace IndependentSetDiscovery.WeightedInstance

variable {ι κ V : Type*}

/-- Renaming labels does not change candidate overlap, costs, or feasibility. -/
def reindex (I : WeightedInstance κ V) (e : ι ≃ κ) : WeightedInstance ι V where
  graph := I.graph
  candidates := fun i => I.candidates (e i)
  cost := fun i => I.cost (e i)
  nonneg := fun i => I.nonneg (e i)

theorem ext_data {I J : WeightedInstance ι V}
    (hg : I.graph = J.graph) (hc : I.candidates = J.candidates) (hw : I.cost = J.cost) : I = J := by
  cases I
  cases J
  cases hg
  cases hc
  cases hw
  rfl

theorem reindex_selection (I : WeightedInstance κ V) (e : ι ≃ κ) (x : ι → V) :
    (I.reindex e).Selection x ↔ I.Selection (fun j => x (e.symm j)) := by
  constructor
  · rintro ⟨hm, hi, ha⟩
    refine ⟨fun j => ?_, hi.comp e.symm.injective, ?_⟩
    · simpa [reindex] using hm (e.symm j)
    · intro j j' hj
      exact ha (e.symm j) (e.symm j') (fun h => hj (e.symm.injective h))
  · rintro ⟨hm, hi, ha⟩
    refine ⟨fun i => ?_, ?_, ?_⟩
    · simpa [reindex] using hm (e i)
    · intro i i' h
      apply e.injective
      apply hi
      simpa using h
    · intro i i' hii'
      simpa [reindex] using ha (e i) (e i') (fun h => hii' (e.injective h))

theorem reindex_cost [Fintype ι] [Fintype κ]
    (I : WeightedInstance κ V) (e : ι ≃ κ) (x : ι → V) :
    (I.reindex e).selectionCost x = I.selectionCost (fun j => x (e.symm j)) := by
  simpa [selectionCost, reindex] using
    Equiv.sum_comp e (fun j => I.cost j (x (e.symm j)))

theorem reindex_optimal [Fintype ι] [Fintype κ]
    (I : WeightedInstance κ V) (e : ι ≃ κ) (x : ι → V) :
    (I.reindex e).Optimal x ↔ I.Optimal (fun j => x (e.symm j)) := by
  constructor
  · rintro ⟨hx, hmin⟩
    refine ⟨(I.reindex_selection e x).mp hx, ?_⟩
    intro y hy
    have hy' : (I.reindex e).Selection (fun i => y (e i)) :=
      (I.reindex_selection e _).mpr (by simpa using hy)
    have hm := hmin (fun i => y (e i)) hy'
    rw [I.reindex_cost e x, I.reindex_cost e (fun i => y (e i))] at hm
    simpa using hm
  · rintro ⟨hx, hmin⟩
    refine ⟨(I.reindex_selection e x).mpr hx, ?_⟩
    intro y hy
    rw [I.reindex_cost e x, I.reindex_cost e y]
    exact hmin _ ((I.reindex_selection e y).mp hy)

theorem reindex_exists_selection (I : WeightedInstance κ V) (e : ι ≃ κ) :
    (∃ x, (I.reindex e).Selection x) ↔ ∃ y, I.Selection y := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨_, (I.reindex_selection e x).mp hx⟩
  · rintro ⟨y, hy⟩
    refine ⟨fun i => y (e i), (I.reindex_selection e _).mpr ?_⟩
    simpa using hy

end IndependentSetDiscovery.WeightedInstance
