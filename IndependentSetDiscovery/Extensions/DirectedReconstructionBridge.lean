import IndependentSetDiscovery.Extensions.DirectedPlanTable
import IndependentSetDiscovery.Extensions.DirectedReduction

/-! # Computed weighted selections become actual lex-optimal move lists -/

namespace IndependentSetDiscovery.WeightedDirected

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {Gf : SimpleGraph V} {D : V → V → Prop} {w : V → V → ℕ} {S : Finset V}

def planOfSelection (x : S → V) (hx : (movementInstance Gf D w S).Selection x)
    (paths : ∀ s : S, {p : DWalk D s.val (x s) //
      p.cost w = (distance D w s.val (x s)).toNat ∧ p.length ≤ Fintype.card V - 1}) :
    RoutePlan D w S (S.image (extendSelection S x)) where
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
  weightBudget := fun v => if hv : v ∈ S then (paths ⟨v, hv⟩).val.cost w else 0
  paths := by
    intro v hv
    have heq : extendSelection S x v = x ⟨v, hv⟩ := by simp [extendSelection, hv]
    rw [heq]
    exact ⟨(paths ⟨v, hv⟩).val, by simp [hv]⟩

theorem selected_target_independent {x : S → V} (hx : (movementInstance Gf D w S).Selection x) :
    Independent Gf (S.image (extendSelection S x)) := by
  intro u hu v hv huv
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hv
  have hst : (⟨s, hs⟩ : S) ≠ ⟨t, ht⟩ := by
    intro heq
    exact huv (congrArg (extendSelection S x) (congrArg Subtype.val heq))
  have hadj := hx.2.2 ⟨s, hs⟩ ⟨t, ht⟩ hst
  simpa [extendSelection, hs, ht, movementInstance] using hadj

theorem planOfSelection_weightTotal_eq (x : S → V)
    (hx : (movementInstance Gf D w S).Selection x)
    (paths : ∀ s : S, {p : DWalk D s.val (x s) //
      p.cost w = (distance D w s.val (x s)).toNat ∧ p.length ≤ Fintype.card V - 1}) :
    ((planOfSelection x hx paths).weightTotal : ℚ) = (movementInstance Gf D w S).selectionCost x := by
  change (↑(∑ v ∈ S, if hv : v ∈ S then (paths ⟨v, hv⟩).val.cost w else 0) : ℚ) =
    ∑ s : S, ((distance D w s.val (x s)).toNat : ℚ)
  rw [Nat.cast_sum, ← Finset.sum_coe_sort S]
  apply Finset.sum_congr rfl
  intro s _
  simp [s.property, (paths s).property.1]

theorem planOfSelection_total_le (x : S → V)
    (hx : (movementInstance Gf D w S).Selection x)
    (paths : ∀ s : S, {p : DWalk D s.val (x s) //
      p.cost w = (distance D w s.val (x s)).toNat ∧ p.length ≤ Fintype.card V - 1}) :
    (planOfSelection x hx paths).total ≤ S.card * (Fintype.card V - 1) := by
  change (∑ v ∈ S, if hv : v ∈ S then (paths ⟨v, hv⟩).val.length else 0) ≤ _
  calc
    _ ≤ ∑ _v ∈ S, (Fintype.card V - 1) := by
      apply Finset.sum_le_sum
      intro v hv
      simpa [hv] using (paths ⟨v, hv⟩).property.2
    _ = _ := by simp

theorem movesCost_scalar (w : V → V → ℕ) (C : ℕ) (moves : List (V × V)) :
    movesCost (fun u v => C * w u v + 1) moves = C * movesCost w moves + moves.length := by
  induction moves with
  | nil => simp [movesCost]
  | cons e es ih =>
      simp only [movesCost, List.map_cons, List.sum_cons, List.length_cons] at *
      rw [ih]
      ring

structure DirectedDiscoveryResult (Gf : SimpleGraph V) (D : V → V → Prop)
    (w : V → V → ℕ) (S : Finset V) where
  target : Finset V
  moves : List (V × V)
  valid : ValidMoves D S moves target
  optimal : LexOptimal Gf D w S target (movesCost w moves) moves.length
  length_le : moves.length ≤ S.card * (Fintype.card V - 1)
  reconstructionWork : ℕ
  work_le : reconstructionWork ≤
    (S.card * (Fintype.card V - 1) + 1) *
      reconstructionStepBudget (Fintype.card V) (S.card * (Fintype.card V - 1))

def reconstructOptimalSelection {n : ℕ} {Gf : SimpleGraph (Fin n)}
    {D : Fin n → Fin n → Prop} {w : Fin n → Fin n → ℕ} {S : Finset (Fin n)}
    (x : S → Fin n)
    (hx : (movementInstance Gf D (fun u v => scalarizationBase S.card (Fintype.card (Fin n)) * w u v + 1) S).Optimal x)
    (paths : ∀ s : S, {p : DWalk D s.val (x s) //
      p.cost (fun u v => scalarizationBase S.card (Fintype.card (Fin n)) * w u v + 1) =
        (distance D (fun u v => scalarizationBase S.card (Fintype.card (Fin n)) * w u v + 1) s.val (x s)).toNat ∧
      p.length ≤ Fintype.card (Fin n) - 1}) : DirectedDiscoveryResult Gf D w S := by
  let C := scalarizationBase S.card (Fintype.card (Fin n))
  let r := planOfSelection x hx.1 paths
  let out := reconstructCached r
  have hT := selected_target_independent hx.1
  have hr : (r.weightTotal : ℚ) =
      (movementInstance Gf D (fun u v => C * w u v + 1) S).selectionCost x :=
    planOfSelection_weightTotal_eq x hx.1 _
  have hmin : ∀ T', Independent Gf T' →
      ∀ r' : Routing D (fun u v => C * w u v + 1) S T', r.weightTotal ≤ r'.total := by
    intro T' hT' r'
    obtain ⟨y, hy, hc⟩ := selection_of_routing hT' r'
    have hm := (hx.2 y hy).trans hc
    rw [← hr] at hm
    exact_mod_cast hm
  have hlength : out.moves.length ≤ S.card * (Fintype.card (Fin n) - 1) :=
    out.length_le.trans (by simpa using planOfSelection_total_le x hx.1 paths)
  have hscore : C * movesCost w out.moves + out.moves.length = r.weightTotal := by
    have hupper := out.weight_le
    rw [movesCost_scalar] at hupper
    obtain ⟨rr, hrr⟩ := routing_of_directedSlideSequence
      (out.valid.slideSequence (w := fun u v => C * w u v + 1))
    have hlower := hmin _ hT rr
    rw [hrr, movesCost_scalar] at hlower
    dsimp only [C] at *
    omega
  have hactual : LexOptimal Gf D w S (S.image (extendSelection S x))
      (movesCost w out.moves) out.moves.length := by
    obtain ⟨c, k, hopt, hk, heq⟩ := reconstruct_lex_optimal Gf D w r.toRouting hT hmin
    have hpair : movesCost w out.moves = c ∧ out.moves.length = k := by
      apply (scalar_eq_iff (scalarizationBase_bound hlength)
        (scalarizationBase_bound (by simpa using hk))).mp
      simpa only [C, RoutePlan.toRouting, Routing.total, RoutePlan.weightTotal, Fintype.card_fin] using
        hscore.trans heq
    simpa only [hpair.1, hpair.2] using hopt
  refine
    { target := S.image (extendSelection S x)
      moves := out.moves
      valid := out.valid
      optimal := hactual
      length_le := by simpa using hlength
      reconstructionWork := out.work
      work_le := ?_ }
  simpa only [Fintype.card_fin] using reconstructCached_polynomial_bound r
    (by simpa using planOfSelection_total_le x hx.1 paths)

end IndependentSetDiscovery.WeightedDirected
