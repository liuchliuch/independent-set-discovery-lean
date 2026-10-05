import IndependentSetDiscovery.Extensions.DirectedPaths
import IndependentSetDiscovery.Movement.Executable

/-! # Executable directed weighted collision-free reconstruction -/

namespace IndependentSetDiscovery.WeightedDirected

open Movement (scanChoose)

variable {V : Type*} [DecidableEq V] {D : V → V → Prop} {w : V → V → ℕ}

structure ExitData (D : V → V → Prop) (w : V → V → ℕ) (Q : Finset V) (s t : V) (length weight : ℕ) where
  source : V
  dest : V
  occupied : source ∈ Q
  empty : dest ∉ Q
  edge : D source dest
  prefixPath : DWalk D s source
  suffix : DWalk D dest t
  split_length : prefixPath.length + 1 + suffix.length = length
  split_weight : prefixPath.cost w + w source dest + suffix.cost w = weight
  work : ℕ
  work_eq : work = prefixPath.length + 1

def findExit {Q : Finset V} {s t : V} (p : DWalk D s t) (hs : s ∈ Q) (ht : t ∉ Q) :
    ExitData D w Q s t p.length (p.cost w) :=
  match p with
  | .nil => False.elim (ht hs)
  | @DWalk.cons _ _ s v t h p =>
    if hw : v ∈ Q then
      let e := findExit p hw ht
      { source := e.source
        dest := e.dest
        occupied := e.occupied
        empty := e.empty
        edge := e.edge
        prefixPath := .cons h e.prefixPath
        suffix := e.suffix
        split_length := by
          have hlen := e.split_length
          simp only [DWalk.length_cons]
          omega
        split_weight := by
          have hw := e.split_weight
          simp only [DWalk.cost_cons]
          omega
        work := e.work + 1
        work_eq := by simp [e.work_eq, Nat.add_assoc] }
    else
      { source := s, dest := v, occupied := hs, empty := hw, edge := h
        prefixPath := .nil, suffix := p
        split_length := by simp [Nat.add_comm]
        split_weight := by simp
        work := 1, work_eq := rfl }
termination_by p.length

theorem findExit_work_le {Q : Finset V} {s t : V} (p : DWalk D s t)
    (hs : s ∈ Q) (ht : t ∉ Q) : (findExit (w := w) p hs ht).work ≤ p.length := by
  have h := (findExit (w := w) p hs ht).split_length
  rw [(findExit (w := w) p hs ht).work_eq]
  omega

/-- Computational routing input: every assigned walk is available as data. -/
structure RoutePlan (D : V → V → Prop) (w : V → V → ℕ) (Q T : Finset V) extends Matching Q T where
  cost : V → ℕ
  weightBudget : V → ℕ
  paths : ∀ x ∈ Q, {p : DWalk D x (target x) //
    p.length ≤ cost x ∧ p.cost w ≤ weightBudget x}

def RoutePlan.toRouting {Q T : Finset V} (r : RoutePlan D w Q T) : Routing D w Q T :=
  { r.toMatching with
    cost := r.weightBudget
    routes := fun x hx => ⟨(r.paths x hx).val, (r.paths x hx).property.2⟩ }

def RoutePlan.total {Q T : Finset V} (r : RoutePlan D w Q T) : ℕ := ∑ x ∈ Q, r.cost x

def RoutePlan.weightTotal {Q T : Finset V} (r : RoutePlan D w Q T) : ℕ := ∑ x ∈ Q, r.weightBudget x

structure PlanStep [Fintype V] {Q T : Finset V} (r : RoutePlan D w Q T) where
  source : V
  dest : V
  occupied : source ∈ Q
  empty : dest ∉ Q
  edge : D source dest
  next : RoutePlan D w (insert dest (Q.erase source)) T
  decrease : next.total + 1 ≤ r.total
  weightDecrease : next.weightTotal + w source dest ≤ r.weightTotal
  work : ℕ
  work_le : work ≤ 4 * Fintype.card V + r.total + 1


/-- One deterministic exchange step. Both finite searches are real linear scans. -/
def RoutePlan.progress {n : ℕ} {D : Fin n → Fin n → Prop} {w : Fin n → Fin n → ℕ} {Q T : Finset (Fin n)}
    (r : RoutePlan D w Q T) (hne : Q ≠ T) : PlanStep r := by
  let tc := scanChoose (fun t => t ∈ T ∧ t ∉ Q) (List.finRange n) (by
    obtain ⟨t, ht, htQ⟩ := r.toRouting.exists_empty_target hne
    exact ⟨t, by simp, ht, htQ⟩)
  let sc := scanChoose (fun s => s ∈ Q ∧ r.target s = tc.value) (List.finRange n) (by
    have htT : tc.value ∈ T := tc.property.1
    have him : tc.value ∈ Q.image r.target := by rw [r.image_eq]; exact htT
    obtain ⟨s, hs, hst⟩ := Finset.mem_image.mp him
    exact ⟨s, by simp, hs, hst⟩)
  let s := sc.value
  have hs : s ∈ Q := sc.property.1
  have ht : r.target s ∉ Q := by rw [sc.property.2]; exact tc.property.2
  let p := (r.paths s hs).val
  have hp : p.length ≤ r.cost s := (r.paths s hs).property.1
  have hpw : p.cost w ≤ r.weightBudget s := (r.paths s hs).property.2
  rcases findExit (w := w) p hs ht with ⟨u, v, hu, hv, huv, a, b, hab, hwab, ew, hew⟩
  have hvu : v ≠ u := by rintro rfl; exact hv hu
  have hv' : v ∉ Q.erase u := fun h => hv (Finset.mem_of_mem_erase h)
  let charged := tc.work + sc.work + ew + 2 * n + 1
  have hcharged : charged ≤ 4 * Fintype.card (Fin n) + r.total + 1 := by
    have htC : tc.work ≤ n := by simpa using tc.work_le
    have hsC : sc.work ≤ n := by simpa using sc.work_le
    have hcost : r.cost s ≤ r.total :=
      Finset.single_le_sum (f := r.cost) (fun _ _ => Nat.zero_le _) hs
    simp only [Fintype.card_fin]
    dsimp [charged]
    omega
  by_cases hus : u = s
  · subst u
    let m := r.toMatching.reindex (Equiv.swap s v) (swap_image_slide hs hv)
    let c := Function.update r.cost v b.length
    let wc := Function.update r.weightBudget v (b.cost w)
    have hroutes : ∀ x ∈ insert v (Q.erase s), {q : DWalk D x (m.target x) //
        q.length ≤ c x ∧ q.cost w ≤ wc x} := by
      intro x hx
      by_cases hxv : x = v
      · subst x
        have hm : m.target v = r.target s := by simp [m, Matching.reindex]
        rw [hm]
        exact ⟨b, by simp [c, wc]⟩
      · have hx' : x ∈ Q.erase s := (Finset.mem_insert.mp hx).resolve_left hxv
        have hxs : x ≠ s := (Finset.mem_erase.mp hx').1
        have hm : m.target x = r.target x := by
          simp [m, Matching.reindex, Equiv.swap_apply_of_ne_of_ne hxs hxv]
        rw [hm]
        simpa [c, wc, hxv] using r.paths x (Finset.mem_of_mem_erase hx')
    let r' : RoutePlan D w (insert v (Q.erase s)) T := ⟨m, c, wc, hroutes⟩
    have hdecr : r'.total + 1 ≤ r.total := by
      have hsum := Finset.sum_erase_add Q r.cost hs
      have htotal : r'.total = b.length + ∑ x ∈ Q.erase s, r.cost x := by
        simp only [RoutePlan.total, r', c, Finset.sum_insert hv', Function.update_self]
        rw [Finset.sum_update_of_notMem hv']
      rw [htotal]
      change _ ≤ ∑ x ∈ Q, r.cost x
      omega
    have hwdecr : r'.weightTotal + w s v ≤ r.weightTotal := by
      have hsum := Finset.sum_erase_add Q r.weightBudget hs
      have htotal : r'.weightTotal = b.cost w + ∑ x ∈ Q.erase s, r.weightBudget x := by
        simp only [RoutePlan.weightTotal, r', wc, Finset.sum_insert hv', Function.update_self]
        rw [Finset.sum_update_of_notMem hv']
      rw [htotal]
      change _ ≤ ∑ x ∈ Q, r.weightBudget x
      omega
    exact ⟨s, v, hs, hv, huv, r', hdecr, hwdecr, charged, hcharged⟩
  · have hsv : s ≠ v := by rintro rfl; exact hv hs
    have hsu : s ≠ u := Ne.symm hus
    have hs' : s ∈ Q.erase u := Finset.mem_erase.mpr ⟨hsu, hs⟩
    let m₀ := r.toMatching.reindex (Equiv.swap s u) (swap_image_of_mem hs hu)
    let m := m₀.reindex (Equiv.swap u v) (swap_image_slide hu hv)
    let c := Function.update (Function.update r.cost s (a.length + r.cost u)) v b.length
    let wc := Function.update (Function.update r.weightBudget s (a.cost w + r.weightBudget u)) v (b.cost w)
    have hroutes : ∀ x ∈ insert v (Q.erase u), {q : DWalk D x (m.target x) //
        q.length ≤ c x ∧ q.cost w ≤ wc x} := by
      intro x hx
      by_cases hxv : x = v
      · subst x
        have hm : m.target v = r.target s := by simp [m, m₀, Matching.reindex]
        rw [hm]
        exact ⟨b, by simp [c, wc]⟩
      · have hx' : x ∈ Q.erase u := (Finset.mem_insert.mp hx).resolve_left hxv
        have hxu : x ≠ u := (Finset.mem_erase.mp hx').1
        by_cases hxs : x = s
        · subst x
          let q := (r.paths u hu).val
          have hq := (r.paths u hu).property.1
          have hqw := (r.paths u hu).property.2
          have hq' : (a.append q).length ≤ a.length + r.cost u := by
            simpa using Nat.add_le_add_left hq a.length
          have hm : m.target s = r.target u := by
            simp [m, m₀, Matching.reindex, Equiv.swap_apply_of_ne_of_ne hsu hsv]
          rw [hm]
          refine ⟨a.append q, ?_, ?_⟩
          · simpa [c, hsv] using hq'
          · simpa [wc, hsv] using Nat.add_le_add_left hqw (a.cost w)
        · have hm : m.target x = r.target x := by
            simp [m, m₀, Matching.reindex,
              Equiv.swap_apply_of_ne_of_ne hxu hxv,
              Equiv.swap_apply_of_ne_of_ne hxs hxu]
          rw [hm]
          simpa [c, wc, hxv, hxs] using r.paths x (Finset.mem_of_mem_erase hx')
    let r' : RoutePlan D w (insert v (Q.erase u)) T := ⟨m, c, wc, hroutes⟩
    have hdecr : r'.total + 1 ≤ r.total := by
      have hsum₁ := Finset.sum_erase_add Q r.cost hu
      have hsum₂ := Finset.sum_erase_add (Q.erase u) r.cost hs'
      have htotal : r'.total = b.length + (a.length + r.cost u) +
          ∑ x ∈ (Q.erase u).erase s, r.cost x := by
        simp only [RoutePlan.total, r', c, Finset.sum_insert hv', Function.update_self]
        rw [Finset.sum_update_of_notMem hv', Finset.sum_update_of_mem hs']
        simp [Finset.sdiff_singleton_eq_erase, Nat.add_assoc]
      rw [htotal]
      change _ ≤ ∑ x ∈ Q, r.cost x
      omega
    have hwdecr : r'.weightTotal + w u v ≤ r.weightTotal := by
      have hsum₁ := Finset.sum_erase_add Q r.weightBudget hu
      have hsum₂ := Finset.sum_erase_add (Q.erase u) r.weightBudget hs'
      have htotal : r'.weightTotal = b.cost w + (a.cost w + r.weightBudget u) +
          ∑ x ∈ (Q.erase u).erase s, r.weightBudget x := by
        simp only [RoutePlan.weightTotal, r', wc, Finset.sum_insert hv', Function.update_self]
        rw [Finset.sum_update_of_notMem hv', Finset.sum_update_of_mem hs']
        simp [Finset.sdiff_singleton_eq_erase, Nat.add_assoc]
      rw [htotal]
      change _ ≤ ∑ x ∈ Q, r.weightBudget x
      omega
    exact ⟨u, v, hu, hv, huv, r', hdecr, hwdecr, charged, hcharged⟩

/-- Validation of a concrete list of token slides. -/
inductive ValidMoves (D : V → V → Prop) : Finset V → List (V × V) → Finset V → Prop
  | nil (Q) : ValidMoves D Q [] Q
  | cons {Q T : Finset V} {u v : V} {moves : List (V × V)} :
      u ∈ Q → v ∉ Q → D u v →
      ValidMoves D (insert v (Q.erase u)) moves T →
      ValidMoves D Q ((u, v) :: moves) T

def movesCost (w : V → V → ℕ) (moves : List (V × V)) : ℕ :=
  (moves.map fun e => w e.1 e.2).sum

theorem ValidMoves.slideSequence {Q T : Finset V} {moves : List (V × V)}
    (h : ValidMoves D Q moves T) :
    DirectedSlideSequence D w Q T (movesCost w moves) moves.length := by
  induction h with
  | nil Q => exact .nil Q
  | cons hu hv huv _ ih => exact .cons ⟨hu, hv, huv, rfl⟩ ih

/-- Actual output data together with correctness, length, and resource bounds. -/
structure Reconstruction [Fintype V] {Q T : Finset V} (r : RoutePlan D w Q T) where
  moves : List (V × V)
  valid : ValidMoves D Q moves T
  length_le : moves.length ≤ r.total
  weight_le : movesCost w moves ≤ r.weightTotal
  work : ℕ
  work_le : work ≤ r.total * (4 * Fintype.card V + r.total + 1)

/-- Executable, terminating collision-free reconstruction from explicit paths. -/
def reconstruct {n : ℕ} {D : Fin n → Fin n → Prop} {w : Fin n → Fin n → ℕ} {Q T : Finset (Fin n)}
    (r : RoutePlan D w Q T) : Reconstruction r := by
  by_cases hQT : Q = T
  · exact ⟨[], hQT ▸ ValidMoves.nil Q, Nat.zero_le _, Nat.zero_le _, 0, Nat.zero_le _⟩
  · let step := r.progress hQT
    let tail := reconstruct step.next
    refine
      { moves := (step.source, step.dest) :: tail.moves
        valid := .cons step.occupied step.empty step.edge tail.valid
        length_le := by have := tail.length_le; have := step.decrease; simp only [List.length_cons]; omega
        weight_le := by
          have := tail.weight_le
          have := step.weightDecrease
          change w step.source step.dest + movesCost w tail.moves ≤ r.weightTotal
          omega
        work := step.work + tail.work
        work_le := ?_ }
    have hdecr : step.next.total + 1 ≤ r.total := step.decrease
    have hmono : 4 * Fintype.card (Fin n) + step.next.total + 1 ≤
        4 * Fintype.card (Fin n) + r.total + 1 := by omega
    calc
      step.work + tail.work ≤ (4 * Fintype.card (Fin n) + r.total + 1) +
          step.next.total * (4 * Fintype.card (Fin n) + step.next.total + 1) :=
        Nat.add_le_add step.work_le tail.work_le
      _ ≤ (4 * Fintype.card (Fin n) + r.total + 1) +
          step.next.total * (4 * Fintype.card (Fin n) + r.total + 1) :=
        Nat.add_le_add_left (Nat.mul_le_mul_left _ hmono) _
      _ = (step.next.total + 1) * (4 * Fintype.card (Fin n) + r.total + 1) := by simp [Nat.add_mul, Nat.add_comm]
      _ ≤ r.total * (4 * Fintype.card (Fin n) + r.total + 1) := Nat.mul_le_mul_right _ hdecr
termination_by r.total
decreasing_by
  all_goals
    change (r.progress hQT).next.total < r.total
    exact Nat.lt_of_succ_le (r.progress hQT).decrease

theorem reconstruct_correct {n : ℕ} {D : Fin n → Fin n → Prop} {w : Fin n → Fin n → ℕ} {Q T : Finset (Fin n)}
    (r : RoutePlan D w Q T) :
    DirectedSlideSequence D w Q T (movesCost w (reconstruct r).moves) (reconstruct r).moves.length ∧
      (reconstruct r).moves.length ≤ r.total ∧
      (reconstruct r).work ≤ r.total * (4 * n + r.total + 1) := by
  exact ⟨(reconstruct r).valid.slideSequence, (reconstruct r).length_le,
    by simpa using (reconstruct r).work_le⟩

/-- With shortest input routes, reconstruction's operation budget is polynomial
in the graph size and number of tokens. -/
theorem reconstruct_polynomial_bound {n : ℕ} {D : Fin n → Fin n → Prop} {w : Fin n → Fin n → ℕ}
    {Q T : Finset (Fin n)} (r : RoutePlan D w Q T)
    (hshort : r.total ≤ Q.card * (n - 1)) :
    (reconstruct r).work ≤
      (Q.card * (n - 1)) * (4 * n + Q.card * (n - 1) + 1) := by
  apply (reconstruct_correct r).2.2.trans
  exact Nat.mul_le_mul hshort (by omega)


end IndependentSetDiscovery.WeightedDirected
