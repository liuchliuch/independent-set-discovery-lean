import IndependentSetDiscovery.Movement.Assignment

/-!
# Executable collision-free reconstruction

Unlike the existence-only `Routing` certificate, `RoutePlan` contains actual
walks as data. Reconstruction on `Fin n` uses deterministic linear scans and
the first-empty-vertex exchange. `work` counts vertex-predicate evaluations,
walk-cell visits, and assignment updates; a vertex-indexed implementation
realizes these operations in polynomial time. No shortest-path oracle is used
by reconstruction: its input is the explicit collection of assigned walks.
-/

namespace IndependentSetDiscovery.Movement

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

def scan (p : V → Prop) [DecidablePred p] : List V → Option V × ℕ
  | [] => (none, 0)
  | x :: xs => if p x then (some x, 1) else
      let r := scan p xs
      (r.1, r.2 + 1)

omit [DecidableEq V] in
theorem scan_cost_le (p : V → Prop) [DecidablePred p] (xs : List V) :
    (scan p xs).2 ≤ xs.length := by
  induction xs with
  | nil => simp [scan]
  | cons x xs ih => simp only [scan, List.length_cons]; split_ifs <;> simp_all

omit [DecidableEq V] in
theorem scan_some (p : V → Prop) [DecidablePred p] {xs : List V} {x : V}
    (h : (scan p xs).1 = some x) : x ∈ xs ∧ p x := by
  induction xs with
  | nil => simp [scan] at h
  | cons y ys ih =>
    by_cases hy : p y
    · simp [scan, hy] at h
      subst x
      exact ⟨List.mem_cons_self, hy⟩
    · have h' : (scan p ys).1 = some x := by simpa [scan, hy] using h
      exact ⟨List.mem_cons_of_mem y (ih h').1, (ih h').2⟩

omit [DecidableEq V] in
theorem scan_none (p : V → Prop) [DecidablePred p] (xs : List V) :
    (scan p xs).1 = none ↔ ∀ x ∈ xs, ¬ p x := by
  induction xs with
  | nil => simp [scan]
  | cons x xs ih => by_cases hx : p x <;> simp [scan, hx, ih]

structure ScanChoice (p : V → Prop) (xs : List V) where
  value : V
  mem : value ∈ xs
  property : p value
  work : ℕ
  work_le : work ≤ xs.length

def scanChoose (p : V → Prop) [DecidablePred p] (xs : List V)
    (h : ∃ x ∈ xs, p x) : ScanChoice p xs := by
  let r := scan p xs
  match hr : r.1 with
  | none =>
    have hn := (scan_none p xs).mp hr
    exact False.elim (h.elim fun x hx => hn x hx.1 hx.2)
  | some x =>
    have hx := scan_some p hr
    exact ⟨x, hx.1, hx.2, r.2, scan_cost_le p xs⟩

structure ExitData (G : SimpleGraph V) (Q : Finset V) (s t : V) (length : ℕ) where
  source : V
  dest : V
  occupied : source ∈ Q
  empty : dest ∉ Q
  edge : G.Adj source dest
  prefixPath : G.Walk s source
  suffix : G.Walk dest t
  split_length : prefixPath.length + 1 + suffix.length = length
  work : ℕ
  work_eq : work = prefixPath.length + 1

def findExit {Q : Finset V} {s t : V} (p : G.Walk s t) (hs : s ∈ Q) (ht : t ∉ Q) :
    ExitData G Q s t p.length :=
  match p with
  | .nil => False.elim (ht hs)
  | .cons' s w t h p =>
    if hw : w ∈ Q then
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
          simp only [SimpleGraph.Walk.length_cons]
          omega
        work := e.work + 1
        work_eq := by simp [e.work_eq, Nat.add_assoc] }
    else
      { source := s, dest := w, occupied := hs, empty := hw, edge := h
        prefixPath := .nil, suffix := p
        split_length := by simp [Nat.add_comm]
        work := 1, work_eq := rfl }
termination_by p.length

theorem findExit_work_le {Q : Finset V} {s t : V} (p : G.Walk s t)
    (hs : s ∈ Q) (ht : t ∉ Q) : (findExit p hs ht).work ≤ p.length := by
  have h := (findExit p hs ht).split_length
  rw [(findExit p hs ht).work_eq]
  omega

/-- Computational routing input: every assigned walk is available as data. -/
structure RoutePlan (G : SimpleGraph V) (Q T : Finset V) extends Matching Q T where
  cost : V → ℕ
  paths : ∀ x ∈ Q, {p : G.Walk x (target x) // p.length ≤ cost x}

def RoutePlan.toRouting {Q T : Finset V} (r : RoutePlan G Q T) : Routing G Q T :=
  { r.toMatching with
    cost := r.cost
    routes := fun x hx => ⟨(r.paths x hx).val, (r.paths x hx).property⟩ }

def RoutePlan.total {Q T : Finset V} (r : RoutePlan G Q T) : ℕ := ∑ x ∈ Q, r.cost x

structure PlanStep [Fintype V] {Q T : Finset V} (r : RoutePlan G Q T) where
  source : V
  dest : V
  occupied : source ∈ Q
  empty : dest ∉ Q
  edge : G.Adj source dest
  next : RoutePlan G (insert dest (Q.erase source)) T
  decrease : next.total + 1 ≤ r.total
  work : ℕ
  work_le : work ≤ 4 * Fintype.card V + r.total + 1


/-- One deterministic exchange step. Both finite searches are real linear scans. -/
def RoutePlan.progress {n : ℕ} {G : SimpleGraph (Fin n)} {Q T : Finset (Fin n)}
    (r : RoutePlan G Q T) (hne : Q ≠ T) : PlanStep r := by
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
  have hp : p.length ≤ r.cost s := (r.paths s hs).property
  rcases findExit p hs ht with ⟨u, v, hu, hv, huv, a, b, hab, ew, hew⟩
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
    have hroutes : ∀ x ∈ insert v (Q.erase s), {q : G.Walk x (m.target x) //
        q.length ≤ c x} := by
      intro x hx
      by_cases hxv : x = v
      · subst x
        have hm : m.target v = r.target s := by simp [m, Matching.reindex]
        rw [hm]
        exact ⟨b, by simp [c]⟩
      · have hx' : x ∈ Q.erase s := (Finset.mem_insert.mp hx).resolve_left hxv
        have hxs : x ≠ s := (Finset.mem_erase.mp hx').1
        have hm : m.target x = r.target x := by
          simp [m, Matching.reindex, Equiv.swap_apply_of_ne_of_ne hxs hxv]
        rw [hm]
        simpa [c, hxv] using r.paths x (Finset.mem_of_mem_erase hx')
    let r' : RoutePlan G (insert v (Q.erase s)) T := ⟨m, c, hroutes⟩
    refine ⟨_, v, hs, hv, huv, r', ?_, charged, hcharged⟩
    have hsum := Finset.sum_erase_add Q r.cost hs
    have htotal : r'.total = b.length + ∑ x ∈ Q.erase s, r.cost x := by
      simp only [RoutePlan.total, r', c, Finset.sum_insert hv', Function.update_self]
      rw [Finset.sum_update_of_notMem hv']
    rw [htotal]
    change _ ≤ ∑ x ∈ Q, r.cost x
    omega
  · have hsv : s ≠ v := by rintro rfl; exact hv hs
    have hsu : s ≠ u := Ne.symm hus
    have hs' : s ∈ Q.erase u := Finset.mem_erase.mpr ⟨hsu, hs⟩
    let m₀ := r.toMatching.reindex (Equiv.swap s u) (swap_image_of_mem hs hu)
    let m := m₀.reindex (Equiv.swap u v) (swap_image_slide hu hv)
    let c := Function.update (Function.update r.cost s (a.length + r.cost u)) v b.length
    have hroutes : ∀ x ∈ insert v (Q.erase u), {q : G.Walk x (m.target x) //
        q.length ≤ c x} := by
      intro x hx
      by_cases hxv : x = v
      · subst x
        have hm : m.target v = r.target s := by simp [m, m₀, Matching.reindex]
        rw [hm]
        exact ⟨b, by simp [c]⟩
      · have hx' : x ∈ Q.erase u := (Finset.mem_insert.mp hx).resolve_left hxv
        have hxu : x ≠ u := (Finset.mem_erase.mp hx').1
        by_cases hxs : x = s
        · subst x
          let q := (r.paths u hu).val
          have hq := (r.paths u hu).property
          have hq' : (a.append q).length ≤ a.length + r.cost u := by
            simpa using Nat.add_le_add_left hq a.length
          have hm : m.target s = r.target u := by
            simp [m, m₀, Matching.reindex, Equiv.swap_apply_of_ne_of_ne hsu hsv]
          rw [hm]
          exact ⟨a.append q, by simpa [c, hsv] using hq'⟩
        · have hm : m.target x = r.target x := by
            simp [m, m₀, Matching.reindex,
              Equiv.swap_apply_of_ne_of_ne hxu hxv,
              Equiv.swap_apply_of_ne_of_ne hxs hxu]
          rw [hm]
          simpa [c, hxv, hxs] using r.paths x (Finset.mem_of_mem_erase hx')
    let r' : RoutePlan G (insert v (Q.erase u)) T := ⟨m, c, hroutes⟩
    refine ⟨u, v, hu, hv, huv, r', ?_, charged, hcharged⟩
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

/-- Validation of a concrete list of token slides. -/
inductive ValidMoves (G : SimpleGraph V) : Finset V → List (V × V) → Finset V → Prop
  | nil (Q) : ValidMoves G Q [] Q
  | cons {Q T : Finset V} {u v : V} {moves : List (V × V)} :
      u ∈ Q → v ∉ Q → G.Adj u v →
      ValidMoves G (insert v (Q.erase u)) moves T →
      ValidMoves G Q ((u, v) :: moves) T

theorem ValidMoves.slideSequence {Q T : Finset V} {moves : List (V × V)}
    (h : ValidMoves G Q moves T) : SlideSequence G Q T moves.length := by
  induction h with
  | nil Q => exact .nil Q
  | cons hu hv huv _ ih => exact .cons ⟨_, hu, _, hv, huv, rfl⟩ ih

/-- Actual output data together with correctness, length, and resource bounds. -/
structure Reconstruction [Fintype V] {Q T : Finset V} (r : RoutePlan G Q T) where
  moves : List (V × V)
  valid : ValidMoves G Q moves T
  length_le : moves.length ≤ r.total
  work : ℕ
  work_le : work ≤ r.total * (4 * Fintype.card V + r.total + 1)

/-- Executable, terminating collision-free reconstruction from explicit paths. -/
def reconstruct {n : ℕ} {G : SimpleGraph (Fin n)} {Q T : Finset (Fin n)}
    (r : RoutePlan G Q T) : Reconstruction r := by
  by_cases hQT : Q = T
  · exact ⟨[], hQT ▸ ValidMoves.nil Q, Nat.zero_le _, 0, Nat.zero_le _⟩
  · let step := r.progress hQT
    let tail := reconstruct step.next
    refine
      { moves := (step.source, step.dest) :: tail.moves
        valid := .cons step.occupied step.empty step.edge tail.valid
        length_le := by have := tail.length_le; have := step.decrease; simp only [List.length_cons]; omega
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

theorem reconstruct_correct {n : ℕ} {G : SimpleGraph (Fin n)} {Q T : Finset (Fin n)}
    (r : RoutePlan G Q T) :
    SlideSequence G Q T (reconstruct r).moves.length ∧
      (reconstruct r).moves.length ≤ r.total ∧
      (reconstruct r).work ≤ r.total * (4 * n + r.total + 1) := by
  exact ⟨(reconstruct r).valid.slideSequence, (reconstruct r).length_le,
    by simpa using (reconstruct r).work_le⟩

/-- With shortest input routes, reconstruction's operation budget is polynomial
in the graph size and number of tokens. -/
theorem reconstruct_polynomial_bound {n : ℕ} {G : SimpleGraph (Fin n)}
    {Q T : Finset (Fin n)} (r : RoutePlan G Q T)
    (hshort : r.total ≤ Q.card * (n - 1)) :
    (reconstruct r).work ≤
      (Q.card * (n - 1)) * (4 * n + Q.card * (n - 1) + 1) := by
  apply (reconstruct_correct r).2.2.trans
  exact Nat.mul_le_mul hshort (by omega)

end IndependentSetDiscovery.Movement
