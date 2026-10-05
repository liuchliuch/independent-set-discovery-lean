import IndependentSetDiscovery.Movement.PlanTable
import IndependentSetDiscovery.Movement.Reduction

/-!
# From an optimal weighted selection to executable discovery output

The shortest paths in the input of `planOfSelection` are data, supplied by the
finite-graph shortest-path implementation. Distances occur only in correctness
proofs; reconstruction computes its budgets from actual path lengths.
-/

namespace IndependentSetDiscovery.Movement

variable {V : Type*} [DecidableEq V] [Fintype V] {G : SimpleGraph V} {S : Finset V}

/-- An executable input-plan builder. There is no choice of paths hidden here. -/
def planOfSelection (x : S → V) (hx : (movementInstance G S).Selection x)
    (paths : ∀ s : S, {p : G.Walk s.val (x s) // p.length = G.dist s.val (x s)}) :
    RoutePlan G S (S.image (extendSelection S x)) where
  target := extendSelection S x
  injective := by
    intro u hu v hv heq
    have hu' : u ∈ S := hu
    have hv' : v ∈ S := hv
    have heq' : x ⟨u, hu⟩ = x ⟨v, hv⟩ := by
      simpa [extendSelection, hu', hv'] using heq
    exact congrArg Subtype.val (hx.2.1 heq')
  image_eq := rfl
  cost := fun v => if hv : v ∈ S then (paths ⟨v, hv⟩).val.length else 0
  paths := by
    intro v hv
    have heq : extendSelection S x v = x ⟨v, hv⟩ := by simp [extendSelection, hv]
    rw [heq]
    exact ⟨(paths ⟨v, hv⟩).val, by simp [hv]⟩

theorem selected_target_independent {x : S → V} (hx : (movementInstance G S).Selection x) :
    Independent G (S.image (extendSelection S x)) := by
  intro u hu v hv huv
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hv
  have hst : (⟨s, hs⟩ : S) ≠ ⟨t, ht⟩ := by
    intro heq
    exact huv (congrArg (extendSelection S x) (congrArg Subtype.val heq))
  have hadj := hx.2.2 ⟨s, hs⟩ ⟨t, ht⟩ hst
  simpa [extendSelection, hs, ht, movementInstance] using hadj

theorem planOfSelection_total_eq (x : S → V) (hx : (movementInstance G S).Selection x)
    (paths : ∀ s : S, {p : G.Walk s.val (x s) // p.length = G.dist s.val (x s)}) :
    ((planOfSelection x hx paths).total : ℚ) = (movementInstance G S).selectionCost x := by
  change (↑(∑ v ∈ S, if hv : v ∈ S then (paths ⟨v, hv⟩).val.length else 0) : ℚ) =
    ∑ s : S, (G.dist s.val (x s) : ℚ)
  rw [Nat.cast_sum, ← Finset.sum_coe_sort S]
  apply Finset.sum_congr rfl
  intro s _
  simp [s.property, (paths s).property]

theorem planOfSelection_total_le (x : S → V) (hx : (movementInstance G S).Selection x)
    (paths : ∀ s : S, {p : G.Walk s.val (x s) // p.length = G.dist s.val (x s)}) :
    (planOfSelection x hx paths).total ≤ S.card * (Fintype.card V - 1) := by
  have h := movement_selectionCost_le hx
  rw [← planOfSelection_total_eq x hx paths] at h
  exact_mod_cast h

/-- The concrete successful result returned by the discovery algorithm. -/
structure DiscoveryResult (G : SimpleGraph V) (S : Finset V) where
  target : Finset V
  moves : List (V × V)
  independent : Independent G target
  valid : ValidMoves G S moves target
  optimal : ∀ T n, Independent G T → SlideSequence G S T n → moves.length ≤ n
  length_le : moves.length ≤ S.card * (Fintype.card V - 1)
  reconstructionWork : ℕ
  work_le : reconstructionWork ≤
    (S.card * (Fintype.card V - 1) + 1) *
      reconstructionStepBudget (Fintype.card V) (S.card * (Fintype.card V - 1))

/-- A computed optimal weighted selection plus computed shortest paths yields
an actual globally shortest collision-free slide list. -/
def reconstructOptimalSelection {n : ℕ} {G : SimpleGraph (Fin n)} {S : Finset (Fin n)}
    (x : S → Fin n) (hx : (movementInstance G S).Optimal x)
    (paths : ∀ s : S, {p : G.Walk s.val (x s) // p.length = G.dist s.val (x s)}) :
    DiscoveryResult G S := by
  let r := planOfSelection x hx.1 paths
  let out := reconstructCached r
  have hT := selected_target_independent hx.1
  have hseq : SlideSequence G S (S.image (extendSelection S x)) out.moves.length :=
    out.valid.slideSequence
  have hupper : (out.moves.length : ℚ) ≤ (movementInstance G S).selectionCost x := by
    rw [← planOfSelection_total_eq x hx.1 paths]
    exact_mod_cast out.length_le
  have hmin : ∀ T' n', Independent G T' → SlideSequence G S T' n' →
      (movementInstance G S).selectionCost x ≤ (n' : ℚ) := by
    intro T' n' hT' hs'
    obtain ⟨y, hy, hcost⟩ := selection_of_sequence hT' hs'
    exact (hx.2 y hy).trans hcost
  refine
    { target := S.image (extendSelection S x)
      moves := out.moves
      independent := hT
      valid := out.valid
      optimal := ?_
      length_le := out.length_le.trans (planOfSelection_total_le x hx.1 paths)
      reconstructionWork := out.work
      work_le := ?_ }
  · intro T' n' hT' hs'
    exact_mod_cast hupper.trans (hmin T' n' hT' hs')
  · simpa [Fintype.card_fin] using reconstructCached_polynomial_bound r
      (by simpa using planOfSelection_total_le x hx.1 paths)

theorem reconstructOptimalSelection_cost {n : ℕ} {G : SimpleGraph (Fin n)}
    {S : Finset (Fin n)} (x : S → Fin n) (hx : (movementInstance G S).Optimal x)
    (paths : ∀ s : S, {p : G.Walk s.val (x s) // p.length = G.dist s.val (x s)}) :
    ((reconstructOptimalSelection x hx paths).moves.length : ℚ) =
      (movementInstance G S).selectionCost x := by
  let r := planOfSelection x hx.1 paths
  let out := reconstructCached r
  change (out.moves.length : ℚ) = _
  apply le_antisymm
  · rw [← planOfSelection_total_eq x hx.1 paths]
    exact_mod_cast out.length_le
  · obtain ⟨y, hy, hc⟩ := selection_of_sequence (selected_target_independent hx.1)
      out.valid.slideSequence
    exact (hx.2 y hy).trans hc

end IndependentSetDiscovery.Movement
