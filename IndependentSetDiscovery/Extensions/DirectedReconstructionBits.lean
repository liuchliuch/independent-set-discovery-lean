import IndependentSetDiscovery.Extensions.DirectedPlanTable
import IndependentSetDiscovery.Extensions.DirectedReconstructionBridge
import IndependentSetDiscovery.Algorithms.BitComplexity
import IndependentSetDiscovery.Algorithms.ResidualBits

/-! # Numeric invariants on the actual cached reconstruction trace

The trace repeats the same progress/materialization steps as `runCached`.
Both length and weight totals decrease. Individual budgets, path-sum
accumulators, and the exchanged-prefix addition are bounded by those totals.
-/
namespace IndependentSetDiscovery.WeightedDirected

open Finset Algorithms
variable {n : ℕ} {D : Fin n → Fin n → Prop} {w : Fin n → Fin n → ℕ}

/-- The exact sequence of materialized plan states visited by reconstruction. -/
def reconstructionStates {Q T : Finset (Fin n)} (p : PlanTable D w Q T) :
    List (Σ R : Finset (Fin n), RoutePlan D w R T) :=
  if h : Q = T then [⟨Q, p.toPlan⟩]
  else
    let step := p.toPlan.progress h
    let next := materializePlan step.next
    ⟨Q, p.toPlan⟩ :: reconstructionStates next
termination_by p.toPlan.total
decreasing_by
  rw [materializePlan_total]
  exact Nat.lt_of_succ_le (p.toPlan.progress h).decrease

theorem reconstructionStates_bounds {Q T : Finset (Fin n)} (p : PlanTable D w Q T)
    (z : Σ R : Finset (Fin n), RoutePlan D w R T) (hz : z ∈ reconstructionStates p) :
    z.2.total ≤ p.toPlan.total ∧ z.2.weightTotal ≤ p.toPlan.weightTotal := by
  rw [reconstructionStates] at hz
  split_ifs at hz with h
  · have he : z = ⟨Q,p.toPlan⟩ := List.mem_singleton.mp hz
    subst z
    exact ⟨le_rfl, le_rfl⟩
  · rcases List.mem_cons.mp hz with he | hz
    · subst z
      exact ⟨le_rfl, le_rfl⟩
    · have hb := reconstructionStates_bounds (materializePlan (p.toPlan.progress h).next) z hz
      rw [materializePlan_total, materializePlan_weightTotal] at hb
      have hl := (p.toPlan.progress h).decrease
      have hw := (p.toPlan.progress h).weightDecrease
      constructor <;> omega
termination_by p.toPlan.total
decreasing_by
  rw [materializePlan_total]
  exact Nat.lt_of_succ_le (p.toPlan.progress h).decrease

theorem RoutePlan.weightBudget_le_total {Q T : Finset (Fin n)} (r : RoutePlan D w Q T)
    {s : Fin n} (hs : s ∈ Q) : r.weightBudget s ≤ r.weightTotal :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) hs

theorem RoutePlan.lengthBudget_le_total {Q T : Finset (Fin n)} (r : RoutePlan D w Q T)
    {s : Fin n} (hs : s ∈ Q) : r.cost s ≤ r.total :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) hs

theorem RoutePlan.two_weightBudgets_le {Q T : Finset (Fin n)} (r : RoutePlan D w Q T)
    {s u : Fin n} (hs : s ∈ Q) (hu : u ∈ Q) (hne : s ≠ u) :
    r.weightBudget s + r.weightBudget u ≤ r.weightTotal := by
  have hsub : ({s,u} : Finset (Fin n)) ⊆ Q := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hs
    · exact hu
  have h := Finset.sum_le_sum_of_subset (f := r.weightBudget) hsub
  simpa [RoutePlan.weightTotal, hne] using h

/-- Every nonnegative prefix/suffix sum of a supplied path fits its current
budget. This includes all partial evaluations of the recursive path-cost fold. -/
theorem RoutePlan.path_parts_bound {Q T : Finset (Fin n)} (r : RoutePlan D w Q T)
    {s u : Fin n} (hs : s ∈ Q) (a : DWalk D s u) (b : DWalk D u (r.target s))
    (he : (r.paths s hs).val = a.append b) :
    a.cost w ≤ r.weightTotal ∧ b.cost w ≤ r.weightTotal := by
  have h := (r.paths s hs).property.2
  rw [he, DWalk.cost_append] at h
  have hb := r.weightBudget_le_total hs
  constructor <;> omega

/-- The temporary addition when one token yields its suffix to another is
bounded before normalization: sources are distinct and both are occupied. -/
theorem RoutePlan.exchange_addition_bound {Q T : Finset (Fin n)} (r : RoutePlan D w Q T)
    {s u : Fin n} (hs : s ∈ Q) (hu : u ∈ Q) (hne : s ≠ u) {prefixCost : ℕ}
    (hp : prefixCost ≤ r.weightBudget s) :
    prefixCost + r.weightBudget u ≤ r.weightTotal := by
  exact (Nat.add_le_add_right hp _).trans (r.two_weightBudgets_le hs hu hne)

theorem DWalk.cost_le_length_mul {s t : Fin n} (p : DWalk D s t) {W : ℕ}
    (hW : ∀ u v, D u v → w u v ≤ W) : p.cost w ≤ p.length*W := by
  induction p with
  | nil => simp
  | @cons u v t he p ih =>
    have hw := hW u v he
    simp only [DWalk.cost_cons, DWalk.length_cons, Nat.add_mul]
    omega

/-- Initial selected paths have at most `n-1` arcs each; shared scalar weights
therefore yield the advertised polynomial-length binary budget envelope. -/
theorem planOfSelection_weightTotal_le {Gf : SimpleGraph (Fin n)} {S : Finset (Fin n)}
    (x : S → Fin n) (hx : (movementInstance Gf D w S).Selection x)
    (paths : ∀ s : S, {p : DWalk D s.val (x s) //
      p.cost w = (distance D w s.val (x s)).toNat ∧ p.length ≤ Fintype.card (Fin n)-1})
    {W : ℕ} (hW : ∀ u v, D u v → w u v ≤ W) :
    (planOfSelection x hx paths).weightTotal ≤ S.card*(n-1)*W := by
  change (∑ v ∈ S, if hv : v ∈ S then (paths ⟨v,hv⟩).val.cost w else 0) ≤ _
  calc
    _ ≤ ∑ _v ∈ S, (n-1)*W := by
      apply Finset.sum_le_sum
      intro v hv
      simp only [dif_pos hv]
      exact ((paths ⟨v,hv⟩).val.cost_le_length_mul hW).trans
        (Nat.mul_le_mul_right W (by simpa using (paths ⟨v,hv⟩).property.2))
    _ = _ := by simp; ring

/-- Every reached state inherits bounds on actual unnormalized operands. -/
theorem reconstructionStates_operand_bounds {Q T : Finset (Fin n)} (r : RoutePlan D w Q T)
    {b L : ℕ} (hb : r.weightTotal ≤ 2^b) (hL : r.total ≤ L)
    (z : Σ R : Finset (Fin n), RoutePlan D w R T)
    (hz : z ∈ reconstructionStates (materializePlan r)) :
    z.2.total ≤ L ∧ z.2.weightTotal ≤ 2^b ∧
      (∀ s ∈ z.1, binaryLength (z.2.weightBudget s) ≤ b+1 ∧ z.2.cost s ≤ L) ∧
      (∀ s ∈ z.1, ∀ u ∈ z.1, s ≠ u → ∀ a ≤ z.2.weightBudget s,
        binaryLength (a+z.2.weightBudget u) ≤ b+1) := by
  have ht := reconstructionStates_bounds (materializePlan r) z hz
  rw [materializePlan_total, materializePlan_weightTotal] at ht
  have hlen := ht.1.trans hL
  have hweight := ht.2.trans hb
  refine ⟨hlen,hweight,?_,?_⟩
  · intro s hs
    exact ⟨binaryLength_le_of_le_pow ((z.2.weightBudget_le_total hs).trans hweight),
      (z.2.lengthBudget_le_total hs).trans hlen⟩
  · intro s hs u hu hne a ha
    exact binaryLength_le_of_le_pow ((z.2.exchange_addition_bound hs hu hne ha).trans hweight)

end IndependentSetDiscovery.WeightedDirected
