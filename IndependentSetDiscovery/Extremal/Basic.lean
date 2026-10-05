import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

/-!
# Bicliques, common neighborhoods, and ordered conflict pairs

The two candidate sets in an ordered pair may overlap. Equality and adjacency
are disjoint kinds of conflict, because a simple graph has no loops.
-/

namespace IndependentSetDiscovery

open Finset

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Ordered adjacent pairs between two (possibly overlapping) vertex sets. -/
def adjacencyPairs (U W : Finset V) : Finset (V × V) :=
  (U ×ˢ W).filter fun p => G.Adj p.1 p.2

/-- Ordered equality-or-adjacency conflicts between candidate sets. -/
def conflictPairs (U W : Finset V) : Finset (V × V) :=
  (U ×ˢ W).filter fun p => p.1 = p.2 ∨ G.Adj p.1 p.2

/-- The left neighbors of a vertex, restricted to a finite candidate set. -/
def leftNeighbors (U : Finset V) (v : V) : Finset V :=
  U.filter fun u => G.Adj u v

/-- A non-induced complete bipartite subgraph with the indicated part sizes. -/
def HasBiclique (s t : ℕ) : Prop :=
  ∃ X Y : Finset V, X.card = s ∧ Y.card = t ∧ Disjoint X Y ∧
    ∀ x ∈ X, ∀ y ∈ Y, G.Adj x y

/-- Exclusion is non-induced, as in the paper. -/
def BicliqueFree (s t : ℕ) : Prop := ¬ HasBiclique G s t

variable [Fintype V]

/-- The common neighborhood of a finite vertex set. -/
def commonNeighbors (X : Finset V) : Finset V :=
  univ.filter fun v => ∀ x ∈ X, G.Adj x v

/-- The maximum size of an `s`-fold common neighborhood is at most `q`. -/
def CodegreeBound (s q : ℕ) : Prop :=
  ∀ X : Finset V, X.card = s → (commonNeighbors G X).card ≤ q

/-- The numerical `s`-codegree. The supremum of an empty family is zero. -/
def sCodegree (s : ℕ) : ℕ :=
  (univ.powersetCard s).sup fun X => (commonNeighbors G X).card

/-- The promise predicate agrees with the numerical maximum in the paper. -/
theorem sCodegree_le_iff (s q : ℕ) :
    sCodegree G s ≤ q ↔ CodegreeBound G s q := by
  simp only [sCodegree, Finset.sup_le_iff, CodegreeBound, mem_powersetCard,
    subset_univ, true_and]

theorem sCodegree_eq_zero_of_card_lt {s : ℕ} (h : Fintype.card V < s) :
    sCodegree G s = 0 := by
  unfold sCodegree
  have he : (univ : Finset V).powersetCard s = ∅ := by
    apply powersetCard_eq_empty.mpr
    simpa using h
  rw [he]
  rfl

@[simp] theorem mem_commonNeighbors {X : Finset V} {v : V} :
    v ∈ commonNeighbors G X ↔ ∀ x ∈ X, G.Adj x v := by
  simp [commonNeighbors]

@[simp] theorem mem_leftNeighbors {U : Finset V} {u v : V} :
    u ∈ leftNeighbors G U v ↔ u ∈ U ∧ G.Adj u v := by
  simp [leftNeighbors]

/-- Looplessness guarantees the disjointness of the two projected sides. -/
theorem disjoint_commonNeighbors (X : Finset V) : Disjoint X (commonNeighbors G X) := by
  refine disjoint_left.mpr ?_
  intro x hx hc
  exact G.loopless x ((mem_commonNeighbors G).mp hc x hx)

/-- The elementary equivalence behind the unbalanced-biclique corollary. -/
theorem bicliqueFree_iff_codegreeBound (s t : ℕ) (ht : 0 < t) :
    BicliqueFree G s t ↔ CodegreeBound G s (t - 1) := by
  constructor
  · intro h X hX
    by_contra hn
    have hcard : t ≤ (commonNeighbors G X).card := by omega
    obtain ⟨Y, hY, hYcard⟩ := exists_subset_card_eq hcard
    apply h
    refine ⟨X, Y, hX, hYcard, ?_, ?_⟩
    · exact (disjoint_commonNeighbors G X).mono_right hY
    · intro x hx y hy
      exact (mem_commonNeighbors G).mp (hY hy) x hx
  · intro h ⟨X, Y, hX, hY, _, hXY⟩
    have hsub : Y ⊆ commonNeighbors G X := by
      intro y hy
      exact (mem_commonNeighbors G).mpr fun x hx => hXY x hx y hy
    have := (card_le_card hsub).trans (h X hX)
    omega

/-- A bounded common neighborhood also bounds its restriction to any set. -/
theorem card_commonNeighbors_filter_le {s q : ℕ} (h : CodegreeBound G s q)
    (X W : Finset V) (hX : X.card = s) :
    (W.filter fun v => ∀ x ∈ X, G.Adj x v).card ≤ q := by
  apply (card_le_card ?_).trans (h X hX)
  intro v hv
  exact (mem_commonNeighbors G).mpr (mem_filter.mp hv).2

/-- Each edge of the copied bipartite graph is counted by its right endpoint. -/
theorem card_adjacencyPairs (U W : Finset V) :
    (adjacencyPairs G U W).card = ∑ v ∈ W, (leftNeighbors G U v).card := by
  simp only [adjacencyPairs, leftNeighbors, card_eq_sum_ones, sum_filter,
    sum_product]
  rw [sum_comm]

/-- The equality pairs are exactly the diagonal image of the intersection. -/
theorem equalityPairs_eq (U W : Finset V) :
    ((U ×ˢ W).filter fun p => p.1 = p.2) = (U ∩ W).image (fun x => (x, x)) := by
  ext p
  rcases p with ⟨u, v⟩
  simp only [mem_filter, mem_product, mem_image, mem_inter]
  constructor
  · rintro ⟨⟨hu, hv⟩, rfl⟩
    exact ⟨u, ⟨hu, hv⟩, rfl⟩
  · rintro ⟨x, ⟨hxU, hxW⟩, h⟩
    cases h
    exact ⟨⟨hxU, hxW⟩, rfl⟩

/-- Exact conflict accounting, valid even for overlapping candidate sets. -/
theorem card_conflictPairs (U W : Finset V) :
    (conflictPairs G U W).card = (adjacencyPairs G U W).card + (U ∩ W).card := by
  have hd : Disjoint ((U ×ˢ W).filter fun p => G.Adj p.1 p.2)
      ((U ×ˢ W).filter fun p => p.1 = p.2) := by
    refine disjoint_left.mpr ?_
    intro p hp hq
    have he := (mem_filter.mp hq).2
    have ha := (mem_filter.mp hp).2
    exact G.loopless p.1 (he.symm ▸ ha)
  have heq : conflictPairs G U W =
      ((U ×ˢ W).filter fun p => G.Adj p.1 p.2) ∪
      ((U ×ˢ W).filter fun p => p.1 = p.2) := by
    ext p
    simp [conflictPairs, and_or_left, or_comm]
  rw [heq, card_union_of_disjoint hd, equalityPairs_eq]
  congr 1
  exact card_image_of_injective _ (fun x y h => congrArg Prod.fst h)

/-- Equality contributes no more than the left candidate-set size. -/
theorem card_conflictPairs_le (U W : Finset V) :
    (conflictPairs G U W).card ≤ (adjacencyPairs G U W).card + U.card := by
  rw [card_conflictPairs]
  exact Nat.add_le_add_left (card_le_card inter_subset_left) _

end IndependentSetDiscovery
