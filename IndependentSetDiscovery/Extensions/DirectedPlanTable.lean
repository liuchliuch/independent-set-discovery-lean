import IndependentSetDiscovery.Extensions.DirectedExecutable
import IndependentSetDiscovery.Movement.PlanTable

/-! # Eagerly cached dual-budget directed reconstruction state -/

namespace IndependentSetDiscovery.WeightedDirected

open Movement (FinTable)

structure VertexState {n : ℕ} (D : Fin n → Fin n → Prop) (w : Fin n → Fin n → ℕ) (v : Fin n) where
  target : Fin n
  budget : ℕ
  weightBudget : ℕ
  path : DWalk D v target
  length_le : path.length ≤ budget
  weight_le : path.cost w ≤ weightBudget

structure PlanTable {n : ℕ} (D : Fin n → Fin n → Prop) (w : Fin n → Fin n → ℕ) (Q T : Finset (Fin n)) where
  table : FinTable (VertexState D w)
  matching : Matching Q T
  agrees : ∀ v ∈ Q, (table.get v).target = matching.target v

def PlanTable.toPlan {n : ℕ} {D : Fin n → Fin n → Prop} {w : Fin n → Fin n → ℕ} {Q T : Finset (Fin n)}
    (p : PlanTable D w Q T) : RoutePlan D w Q T where
  target := fun v => (p.table.get v).target
  injective := by
    intro u hu v hv heq
    apply p.matching.injective hu hv
    simpa only [p.agrees u hu, p.agrees v hv] using heq
  image_eq := by
    calc Q.image (fun v => (p.table.get v).target) = Q.image p.matching.target :=
      Finset.image_congr p.agrees
      _ = T := p.matching.image_eq
  cost := fun v => (p.table.get v).budget
  weightBudget := fun v => (p.table.get v).weightBudget
  paths := fun v _ => ⟨(p.table.get v).path, (p.table.get v).length_le, (p.table.get v).weight_le⟩

def planVertex {n : ℕ} {D : Fin n → Fin n → Prop} {w : Fin n → Fin n → ℕ} {Q T : Finset (Fin n)}
    (r : RoutePlan D w Q T) (v : Fin n) : VertexState D w v :=
  if hv : v ∈ Q then
    { target := r.target v, budget := r.cost v, weightBudget := r.weightBudget v
      path := (r.paths v hv).val, length_le := (r.paths v hv).property.1,
      weight_le := (r.paths v hv).property.2 }
  else
    { target := v, budget := 0, weightBudget := 0, path := .nil, length_le := le_rfl, weight_le := le_rfl }

/-- One entry is evaluated once. The length is traversed to charge the actual
route data; the `4 * length` allowance covers that traversal and the possible
prefix copying/length computations in a one-step route update. A finite-set
membership scan uses at most `n` comparisons, with twelve fixed operations. -/
def planVertexCell {n : ℕ} {D : Fin n → Fin n → Prop} {w : Fin n → Fin n → ℕ} {Q T : Finset (Fin n)}
    (r : RoutePlan D w Q T) (v : Fin n) : (Sigma (VertexState D w)) × ℕ :=
  let state := planVertex r v
  (⟨v, state⟩, n + 16 + 4 * state.path.length)

/-- The counted implementation performs a vector callback for every vertex,
and sums those returned counters. `8*n+1` covers vector construction, mapping,
and summation. The paths and costs are shared by the table and counter. -/
def materializePlanWithWork {n : ℕ} {D : Fin n → Fin n → Prop} {w : Fin n → Fin n → ℕ} {Q T : Finset (Fin n)}
    (r : RoutePlan D w Q T) : PlanTable D w Q T × ℕ :=
  let entries := Vector.ofFn (planVertexCell r)
  let table : FinTable (VertexState D w) :=
    { entries := entries.map Prod.fst
      indexed := by intro i; simp [entries, planVertexCell] }
  let packed : PlanTable D w Q T :=
    { table := table
      matching := r.toMatching
      agrees := by
        intro v hv
        have hg : table.get v = planVertex r v :=
          FinTable.get_eq_of_entry _ _ _ (by simp [table, entries, planVertexCell])
        rw [hg]
        simp [planVertex, hv] }
  (packed, 8 * n + 1 + (entries.toList.map Prod.snd).sum)

/-- Materialization data is the first projection of the counted implementation. -/
def materializePlan {n : ℕ} {D : Fin n → Fin n → Prop} {w : Fin n → Fin n → ℕ} {Q T : Finset (Fin n)}
    (r : RoutePlan D w Q T) : PlanTable D w Q T := (materializePlanWithWork r).1

@[simp] theorem materializePlan_get {n : ℕ} {D : Fin n → Fin n → Prop} {w : Fin n → Fin n → ℕ}
    {Q T : Finset (Fin n)} (r : RoutePlan D w Q T) (v : Fin n) :
    (materializePlan r).table.get v = planVertex r v :=
  FinTable.get_eq_of_entry _ _ _ (by
    simp [materializePlan, materializePlanWithWork, planVertexCell])

@[simp] theorem materializePlan_cost {n : ℕ} {D : Fin n → Fin n → Prop} {w : Fin n → Fin n → ℕ}
    {Q T : Finset (Fin n)} (r : RoutePlan D w Q T) (v : Fin n) (hv : v ∈ Q) :
    (materializePlan r).toPlan.cost v = r.cost v := by
  change ((materializePlan r).table.get v).budget = r.cost v
  rw [materializePlan_get]
  simp [planVertex, hv]

@[simp] theorem materializePlan_total {n : ℕ} {D : Fin n → Fin n → Prop} {w : Fin n → Fin n → ℕ}
    {Q T : Finset (Fin n)} (r : RoutePlan D w Q T) :
    (materializePlan r).toPlan.total = r.total := by
  apply Finset.sum_congr rfl
  intro v hv
  exact materializePlan_cost r v hv

@[simp] theorem materializePlan_weightBudget {n : ℕ} {D : Fin n → Fin n → Prop}
    {w : Fin n → Fin n → ℕ} {Q T : Finset (Fin n)} (r : RoutePlan D w Q T)
    (v : Fin n) (hv : v ∈ Q) :
    (materializePlan r).toPlan.weightBudget v = r.weightBudget v := by
  change ((materializePlan r).table.get v).weightBudget = r.weightBudget v
  rw [materializePlan_get]
  simp [planVertex, hv]

@[simp] theorem materializePlan_weightTotal {n : ℕ} {D : Fin n → Fin n → Prop}
    {w : Fin n → Fin n → ℕ} {Q T : Finset (Fin n)} (r : RoutePlan D w Q T) :
    (materializePlan r).toPlan.weightTotal = r.weightTotal := by
  apply Finset.sum_congr rfl
  intro v hv
  exact materializePlan_weightBudget r v hv

/-- Conservative list/array work for a materialization. All next-state getters
are array accesses; each occupied route is fetched only once by `ofFn`. -/
def materializationBudget (n M : ℕ) : ℕ := 16 * (n + 1) * (n + M + 2)

def reconstructionStepBudget (n M : ℕ) : ℕ := 64 * (n + 1) * (n + M + 1)

theorem materializationBudget_le (n M : ℕ) :
    materializationBudget n M ≤ reconstructionStepBudget n M := by
  unfold materializationBudget reconstructionStepBudget
  nlinarith

theorem reconstructionStepBudget_mono (n : ℕ) {M N : ℕ} (h : M ≤ N) :
    reconstructionStepBudget n M ≤ reconstructionStepBudget n N := by
  exact Nat.mul_le_mul_left _ (by omega)

theorem planVertex_length_le_total {n : ℕ} {D : Fin n → Fin n → Prop} {w : Fin n → Fin n → ℕ}
    {Q T : Finset (Fin n)} (r : RoutePlan D w Q T) (v : Fin n) :
    (planVertex r v).path.length ≤ r.total := by
  by_cases hv : v ∈ Q
  · have h := (r.paths v hv).property.1
    have hbudget : r.cost v ≤ r.total :=
      Finset.single_le_sum (f := r.cost) (fun _ _ => Nat.zero_le _) hv
    unfold planVertex
    rw [dif_pos hv]
    exact h.trans hbudget
  · unfold planVertex
    rw [dif_neg hv]
    exact Nat.zero_le _

/-- Refinement from the actual materialization loop/counters to its polynomial
bound. In particular, all `n` path traversals are included in the sum. -/
theorem materializePlanWithWork_bound {n : ℕ} {D : Fin n → Fin n → Prop} {w : Fin n → Fin n → ℕ}
    {Q T : Finset (Fin n)} (r : RoutePlan D w Q T) :
    (materializePlanWithWork r).2 ≤ materializationBudget n r.total := by
  have hsum : (∑ v : Fin n, (planVertexCell r v).2) ≤ n * (n + 16 + 4 * r.total) := by
    calc
      _ ≤ (∑ _v : Fin n, (n + 16 + 4 * r.total)) := by
        apply Finset.sum_le_sum
        intro v _
        have h := planVertex_length_le_total r v
        simp only [planVertexCell]
        omega
      _ = _ := by simp
  simp only [materializePlanWithWork, Vector.toList_ofFn, List.map_ofFn, List.sum_ofFn] at ⊢
  change 8 * n + 1 + (∑ v : Fin n, (planVertexCell r v).2) ≤ _
  unfold materializationBudget
  nlinarith

theorem materialized_step_cost_le {n : ℕ} {D : Fin n → Fin n → Prop} {w : Fin n → Fin n → ℕ}
    {Q T : Finset (Fin n)} (p : PlanTable D w Q T) (hne : Q ≠ T) :
    (p.toPlan.progress hne).work * (2 * n + 8) +
        (materializePlanWithWork (p.toPlan.progress hne).next).2 ≤
      reconstructionStepBudget n p.toPlan.total := by
  have hwork := (p.toPlan.progress hne).work_le
  have hdecr := (p.toPlan.progress hne).decrease
  have hpack := materializePlanWithWork_bound (p.toPlan.progress hne).next
  simp only [Fintype.card_fin] at hwork
  unfold materializationBudget reconstructionStepBudget at *
  have hmul := Nat.mul_le_mul_right (2 * n + 8) hwork
  nlinarith

structure TableTrace {n : ℕ} {D : Fin n → Fin n → Prop} {w : Fin n → Fin n → ℕ} {Q T : Finset (Fin n)}
    (p : PlanTable D w Q T) where
  moves : List (Fin n × Fin n)
  valid : ValidMoves D Q moves T
  length_le : moves.length ≤ p.toPlan.total
  weight_le : movesCost w moves ≤ p.toPlan.weightTotal
  work : ℕ
  work_le : work ≤ p.toPlan.total * reconstructionStepBudget n p.toPlan.total

/-- The recursive reconstruction runs only on materialized tables. -/
def reconstructTable {n : ℕ} {D : Fin n → Fin n → Prop} {w : Fin n → Fin n → ℕ} {Q T : Finset (Fin n)}
    (p : PlanTable D w Q T) : TableTrace p := by
  by_cases hQT : Q = T
  · exact ⟨[], hQT ▸ ValidMoves.nil Q, Nat.zero_le _, Nat.zero_le _, 0, Nat.zero_le _⟩
  · let step := p.toPlan.progress hQT
    let packed := materializePlanWithWork step.next
    let next := packed.1
    let tail := reconstructTable next
    have hn : next.toPlan.total = step.next.total := materializePlan_total step.next
    refine
      { moves := (step.source, step.dest) :: tail.moves
        valid := .cons step.occupied step.empty step.edge tail.valid
        length_le := by
          have h := tail.length_le
          have h' := step.decrease
          simp only [List.length_cons]
          omega
        weight_le := by
          have h := tail.weight_le
          have h' := step.weightDecrease
          have hw : next.toPlan.weightTotal = step.next.weightTotal := materializePlan_weightTotal step.next
          change w step.source step.dest + movesCost w tail.moves ≤ p.toPlan.weightTotal
          omega
        work := step.work * (2 * n + 8) + packed.2 + tail.work
        work_le := ?_ }
    have hd : next.toPlan.total + 1 ≤ p.toPlan.total := by rw [hn]; exact step.decrease
    have hm := reconstructionStepBudget_mono n (show next.toPlan.total ≤ p.toPlan.total by omega)
    have hw : step.work * (2 * n + 8) + packed.2 ≤
        reconstructionStepBudget n p.toPlan.total := by
      exact materialized_step_cost_le p hQT
    calc
      _ ≤ reconstructionStepBudget n p.toPlan.total +
          next.toPlan.total * reconstructionStepBudget n next.toPlan.total :=
        Nat.add_le_add hw tail.work_le
      _ ≤ reconstructionStepBudget n p.toPlan.total +
          next.toPlan.total * reconstructionStepBudget n p.toPlan.total :=
        Nat.add_le_add_left (Nat.mul_le_mul_left _ hm) _
      _ = (next.toPlan.total + 1) * reconstructionStepBudget n p.toPlan.total := by
        simp [Nat.add_mul, Nat.add_comm]
      _ ≤ p.toPlan.total * reconstructionStepBudget n p.toPlan.total :=
        Nat.mul_le_mul_right _ hd
termination_by p.toPlan.total
decreasing_by
  all_goals
    change (materializePlan (p.toPlan.progress hQT).next).toPlan.total < p.toPlan.total
    rw [materializePlan_total]
    exact Nat.lt_of_succ_le (p.toPlan.progress hQT).decrease

structure CachedReconstruction {n : ℕ} {D : Fin n → Fin n → Prop} {w : Fin n → Fin n → ℕ}
    {Q T : Finset (Fin n)} (r : RoutePlan D w Q T) where
  moves : List (Fin n × Fin n)
  valid : ValidMoves D Q moves T
  length_le : moves.length ≤ r.total
  weight_le : movesCost w moves ≤ r.weightTotal
  work : ℕ
  work_le : work ≤ (r.total + 1) * reconstructionStepBudget n r.total

/-- Fully materialized reconstruction, including the initial materialization. -/
def reconstructCached {n : ℕ} {D : Fin n → Fin n → Prop} {w : Fin n → Fin n → ℕ} {Q T : Finset (Fin n)}
    (r : RoutePlan D w Q T) : CachedReconstruction r :=
  let packed := materializePlanWithWork r
  let p := packed.1
  let out := reconstructTable p
  { moves := out.moves
    valid := out.valid
    weight_le := by
      have h := out.weight_le
      change movesCost w out.moves ≤ (materializePlan r).toPlan.weightTotal at h
      simpa using h
    length_le := by
      have h := out.length_le
      change out.moves.length ≤ (materializePlan r).toPlan.total at h
      simpa using h
    work := packed.2 + out.work
    work_le := by
      have hw := out.work_le
      have hm := (materializePlanWithWork_bound r).trans (materializationBudget_le n r.total)
      have hp : p.toPlan.total = r.total := materializePlan_total r
      rw [hp] at hw
      calc
        _ ≤ reconstructionStepBudget n r.total + r.total * reconstructionStepBudget n r.total :=
          Nat.add_le_add hm hw
        _ = _ := by simp [Nat.add_mul, Nat.add_comm] }

theorem reconstructCached_polynomial_bound {n : ℕ} {D : Fin n → Fin n → Prop} {w : Fin n → Fin n → ℕ}
    {Q T : Finset (Fin n)} (r : RoutePlan D w Q T) (h : r.total ≤ Q.card * (n - 1)) :
    (reconstructCached r).work ≤
      (Q.card * (n - 1) + 1) * reconstructionStepBudget n (Q.card * (n - 1)) := by
  apply (reconstructCached r).work_le.trans
  exact Nat.mul_le_mul (by omega) (reconstructionStepBudget_mono n h)


end IndependentSetDiscovery.WeightedDirected
