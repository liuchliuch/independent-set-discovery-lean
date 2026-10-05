import IndependentSetDiscovery.Movement.Assignment
import IndependentSetDiscovery.Weighted
import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# The actual weighted-transversal reduction

The labels are the initial occupied vertices. Their candidates are exactly
their reachable vertices, and rational costs are casts of graph distances.
This module connects the weighted solver's `Within` and `Optimal` predicates
to actual token slides. The bound `|S| (|V|-1)` applies also at zero tokens.
-/

namespace IndependentSetDiscovery
namespace Movement

variable {V : Type*} [DecidableEq V] [Fintype V] {G : SimpleGraph V}

/-- The graph-metric weighted instance of Corollary 3.3. -/
noncomputable def movementInstance (G : SimpleGraph V) (S : Finset V) :
    WeightedInstance S V := by
  classical
  exact
    { graph := G
      candidates := fun s => Finset.univ.filter (G.Reachable s.val)
      cost := fun s v => (G.dist s.val v : ℚ)
      nonneg := by intro s v _; exact_mod_cast Nat.zero_le (G.dist s.val v) }

omit [DecidableEq V] in
@[simp] theorem movementInstance_mem (G : SimpleGraph V) (S : Finset V) (s : S) (v : V) :
    v ∈ (movementInstance G S).candidates s ↔ G.Reachable s.val v := by
  classical
  simp [movementInstance]

def extendSelection (S : Finset V) (x : S → V) (v : V) : V :=
  if hv : v ∈ S then x ⟨v, hv⟩ else v

omit [Fintype V] in
@[simp] theorem extendSelection_apply (S : Finset V) (x : S → V) (s : S) :
    extendSelection S x s.val = x s := by simp [extendSelection, s.property]

/-- A feasible weighted selection supplies actual routes and an independent
endpoint, with exactly the same total integer cost. -/
theorem routing_of_selection {S : Finset V} {x : S → V}
    (hx : (movementInstance G S).Selection x) :
    ∃ T, Independent G T ∧ ∃ r : Routing G S T,
      (r.total : ℚ) = (movementInstance G S).selectionCost x := by
  let f := extendSelection S x
  have hreach : ∀ s : S, G.Reachable s.val (x s) := by
    intro s
    exact (movementInstance_mem G S s (x s)).mp (hx.1 s)
  have hi : Set.InjOn f (↑S : Set V) := by
    intro u hu v hv heq
    have hu' : u ∈ S := hu
    have hv' : v ∈ S := hv
    have heq' : x ⟨u, hu⟩ = x ⟨v, hv⟩ := by simpa [f, extendSelection, hu', hv'] using heq
    exact congrArg Subtype.val (hx.2.1 heq')
  have hind : Independent G (S.image f) := by
    intro u hu v hv huv
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hv
    have hst : (⟨s, hs⟩ : S) ≠ ⟨t, ht⟩ := by
      intro heq
      exact huv (congrArg f (congrArg Subtype.val heq))
    have hadj := hx.2.2 ⟨s, hs⟩ ⟨t, ht⟩ hst
    simpa [f, extendSelection, hs, ht, movementInstance] using hadj
  let r : Routing G S (S.image f) :=
    { target := f
      injective := hi
      image_eq := rfl
      cost := fun s => G.dist s (f s)
      routes := by
        intro s hs
        have h : G.Reachable s (f s) := by
          simpa [f, extendSelection, hs] using hreach ⟨s, hs⟩
        obtain ⟨p, hp⟩ := h.exists_walk_length_eq_dist
        exact ⟨p, hp.le⟩ }
  refine ⟨S.image f, hind, r, ?_⟩
  change (↑(∑ s ∈ S, G.dist s (f s)) : ℚ) = ∑ s : S, (G.dist s.val (x s) : ℚ)
  rw [Nat.cast_sum, ← Finset.sum_coe_sort S]
  apply Finset.sum_congr rfl
  intro s _
  simp [f]

/-- Any independent reached endpoint induces a genuine weighted selection at
cost no greater than the sequence length. -/
theorem selection_of_sequence {S T : Finset V} {n : ℕ}
    (hT : Independent G T) (hseq : SlideSequence G S T n) :
    ∃ x : S → V, (movementInstance G S).Selection x ∧
      (movementInstance G S).selectionCost x ≤ (n : ℚ) := by
  obtain ⟨r, hr⟩ := routing_of_slideSequence hseq
  let x : S → V := fun s => r.target s.val
  have hselect : (movementInstance G S).Selection x := by
    refine ⟨?_, ?_, ?_⟩
    · intro s
      apply (movementInstance_mem G S s (x s)).mpr
      obtain ⟨p, _⟩ := r.routes s.val s.property
      exact ⟨p⟩
    · intro s t hst
      apply Subtype.ext
      exact r.injective s.property t.property hst
    · intro s t hst
      apply hT
      · rw [← r.image_eq]; exact Finset.mem_image.mpr ⟨s.val, s.property, rfl⟩
      · rw [← r.image_eq]; exact Finset.mem_image.mpr ⟨t.val, t.property, rfl⟩
      · intro heq
        apply hst
        exact Subtype.ext (r.injective s.property t.property heq)
  refine ⟨x, hselect, ?_⟩
  change (∑ s : S, (G.dist s.val (r.target s.val) : ℚ)) ≤ (n : ℚ)
  rw [Finset.sum_coe_sort S (fun s => (G.dist s (r.target s) : ℚ))]
  calc
    (∑ s ∈ S, (G.dist s (r.target s) : ℚ)) ≤ ∑ s ∈ S, (r.cost s : ℚ) := by
      apply Finset.sum_le_sum
      intro s hs
      obtain ⟨p, hp⟩ := r.routes s hs
      exact_mod_cast ((SimpleGraph.dist_le p).trans hp)
    _ = (n : ℚ) := by rw [← Nat.cast_sum]; exact congrArg (fun n : ℕ => (n : ℚ)) hr

/-- Full correctness of the actual reduction, including overlapping lists and
unreachable destinations. -/
theorem movementInstance_within_iff (G : SimpleGraph V) (S : Finset V) (b : ℕ) :
    (movementInstance G S).Within (b : ℚ) ↔ DiscoveryWithin G S b := by
  constructor
  · rintro ⟨x, hx, hcost⟩
    obtain ⟨T, hT, r, hr⟩ := routing_of_selection hx
    obtain ⟨n, hn, hs⟩ := r.realize
    have hbudget : r.total ≤ b := by exact_mod_cast (hr.symm ▸ hcost)
    exact ⟨T, n, hT, hs, hn.trans hbudget⟩
  · rintro ⟨T, n, hT, hs, hn⟩
    obtain ⟨x, hx, hc⟩ := selection_of_sequence hT hs
    exact ⟨x, hx, hc.trans (by exact_mod_cast hn)⟩

omit [DecidableEq V] in
theorem reachable_dist_le_card_sub_one {u v : V} (h : G.Reachable u v) :
    G.dist u v ≤ Fintype.card V - 1 := by
  obtain ⟨p, hp, hlen⟩ := h.exists_path_of_dist
  have := hp.length_lt
  omega

/-- All graph-metric selections fit the polynomial reconstruction bound. -/
theorem movement_selectionCost_le {S : Finset V} {x : S → V}
    (hx : (movementInstance G S).Selection x) :
    (movementInstance G S).selectionCost x ≤
      (S.card * (Fintype.card V - 1) : ℕ) := by
  change (∑ s : S, (G.dist s.val (x s) : ℚ)) ≤ _
  calc
    (∑ s : S, (G.dist s.val (x s) : ℚ)) ≤
        ∑ _s : S, ((Fintype.card V - 1 : ℕ) : ℚ) := by
      apply Finset.sum_le_sum
      intro s _
      exact_mod_cast reachable_dist_le_card_sub_one
        ((movementInstance_mem G S s (x s)).mp (hx.1 s))
    _ = (S.card * (Fintype.card V - 1) : ℕ) := by simp

/-- Corollary 3.3's witness and optimization transfer. An optimal weighted
selection yields a shortest collision-free sequence to an optimal independent
target. The number of reconstructed slides is at most `k(n-1)`. -/
theorem optimal_selection_realizes_discovery {S : Finset V} {x : S → V}
    (hx : (movementInstance G S).Optimal x) :
    ∃ T n, Independent G T ∧ SlideSequence G S T n ∧
      (n : ℚ) = (movementInstance G S).selectionCost x ∧
      n ≤ S.card * (Fintype.card V - 1) ∧
      ∀ T' n', Independent G T' → SlideSequence G S T' n' → n ≤ n' := by
  obtain ⟨T, hT, r, hr⟩ := routing_of_selection hx.1
  obtain ⟨n, hn, hs⟩ := r.realize
  have hmin : ∀ T' n', Independent G T' → SlideSequence G S T' n' →
      (movementInstance G S).selectionCost x ≤ (n' : ℚ) := by
    intro T' n' hT' hs'
    obtain ⟨y, hy, hcost⟩ := selection_of_sequence hT' hs'
    exact (hx.2 y hy).trans hcost
  have heq : (n : ℚ) = (movementInstance G S).selectionCost x := by
    apply le_antisymm
    · rw [← hr]
      exact_mod_cast hn
    · exact hmin T n hT hs
  refine ⟨T, n, hT, hs, heq, ?_, ?_⟩
  · have := movement_selectionCost_le hx.1
    rw [← heq] at this
    exact_mod_cast this
  · intro T' n' hT' hs'
    have := hmin T' n' hT' hs'
    rw [← heq] at this
    exact_mod_cast this

theorem no_selection_iff_unreachable (G : SimpleGraph V) (S : Finset V) :
    (¬ ∃ x, (movementInstance G S).Selection x) ↔
      ¬ ∃ T n, Independent G T ∧ SlideSequence G S T n := by
  constructor
  · intro h ⟨T, n, hT, hs⟩
    obtain ⟨x, hx, _⟩ := selection_of_sequence hT hs
    exact h ⟨x, hx⟩
  · intro h ⟨x, hx⟩
    obtain ⟨T, hT, r, _⟩ := routing_of_selection hx
    obtain ⟨n, _, hs⟩ := r.realize
    exact h ⟨T, n, hT, hs⟩

end Movement
end IndependentSetDiscovery
