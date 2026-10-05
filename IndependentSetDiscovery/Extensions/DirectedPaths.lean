import IndependentSetDiscovery.Extensions.DirectedRouting

/-! # Cycle removal and the polynomial slide bound for directed movement -/

namespace IndependentSetDiscovery.WeightedDirected.DWalk

variable {V : Type*} [DecidableEq V] {D : V → V → Prop}
variable {u v t : V}

def length : {u v : V} → DWalk D u v → ℕ
  | _, _, .nil => 0
  | _, _, .cons _ p => p.length + 1

def support : {u v : V} → DWalk D u v → List V
  | u, _, .nil => [u]
  | u, _, .cons _ p => u :: p.support

@[simp] theorem length_nil : (DWalk.nil (D := D) (u := u)).length = 0 := rfl
@[simp] theorem length_cons (h : D u v) (p : DWalk D v t) :
    (DWalk.cons h p).length = p.length + 1 := rfl
@[simp] theorem support_nil : (DWalk.nil (D := D) (u := u)).support = [u] := rfl
@[simp] theorem support_cons (h : D u v) (p : DWalk D v t) :
    (DWalk.cons h p).support = u :: p.support := rfl

@[simp] theorem length_append (p : DWalk D u v) (q : DWalk D v t) :
    (p.append q).length = p.length + q.length := by
  induction p with
  | nil => simp [append]
  | cons h p ih => simp [append, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem length_support (p : DWalk D u v) : p.support.length = p.length + 1 := by
  induction p with
  | nil => simp
  | cons h p ih => simp [ih, Nat.add_assoc]

theorem cost_scalar (p : DWalk D u v) (w : V → V → ℕ) (C : ℕ) :
    p.cost (fun x y => C * w x y + 1) = C * p.cost w + p.length := by
  induction p with
  | nil => simp
  | cons h p ih => simp [ih]; ring

theorem suffix_of_mem_support (w : V → V → ℕ) (p : DWalk D u t) {x : V}
    (hx : x ∈ p.support) :
    ∃ q : DWalk D x t, q.cost w ≤ p.cost w ∧ q.support <:+ p.support := by
  induction p with
  | @nil u =>
      have : x = u := by simpa using hx
      subst x
      exact ⟨.nil, le_rfl, List.suffix_rfl⟩
  | @cons u v t h p ih =>
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨.cons h p, le_rfl, List.suffix_rfl⟩
      · obtain ⟨q, hc, hs⟩ := ih hx
        exact ⟨q, hc.trans (Nat.le_add_left _ _),
          hs.trans (List.suffix_cons u p.support)⟩

/-- Removing directed cycles cannot increase nonnegative movement cost. -/
theorem exists_simple_le_cost (w : V → V → ℕ) (p : DWalk D u t) :
    ∃ q : DWalk D u t, q.support.Nodup ∧ q.cost w ≤ p.cost w := by
  induction p with
  | nil => exact ⟨.nil, by simp, le_rfl⟩
  | @cons u v t h p ih =>
      obtain ⟨q, hq, hc⟩ := ih
      by_cases hu : u ∈ q.support
      · obtain ⟨r, hr, hs⟩ := suffix_of_mem_support w q hu
        exact ⟨r, hq.sublist hs.sublist,
          hr.trans (hc.trans (Nat.le_add_left _ _))⟩
      · exact ⟨.cons h q, List.nodup_cons.mpr ⟨hu, hq⟩,
          Nat.add_le_add_left hc _⟩

theorem length_le_card_sub_one [Fintype V] (p : DWalk D u t) (hp : p.support.Nodup) :
    p.length ≤ Fintype.card V - 1 := by
  have hcard : p.support.length ≤ Fintype.card V := by
    rw [← List.toFinset_card_of_nodup hp]
    exact Finset.card_le_univ _
  rw [length_support] at hcard
  omega

theorem exists_bounded_le_cost [Fintype V] (w : V → V → ℕ) (p : DWalk D u t) :
    ∃ q : DWalk D u t, q.cost w ≤ p.cost w ∧ q.length ≤ Fintype.card V - 1 := by
  obtain ⟨q, hq, hc⟩ := p.exists_simple_le_cost w
  exact ⟨q, hc, q.length_le_card_sub_one hq⟩

end IndependentSetDiscovery.WeightedDirected.DWalk

namespace IndependentSetDiscovery.WeightedDirected

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {D : V → V → Prop} {w : V → V → ℕ}

/-- Every path assignment has a scalarized surrogate whose movement cost does
not increase and whose total number of path arcs is at most `k(n-1)`. -/
theorem Routing.bounded_scalar_surrogate {Q T : Finset V}
    (r : Routing D w Q T) (C : ℕ) :
    ∃ r' : Routing D (fun u v => C * w u v + 1) Q T,
      ∃ a b, r'.total = C * a + b ∧ a ≤ r.total ∧
        b ≤ Q.card * (Fintype.card V - 1) := by
  classical
  have hpaths : ∀ x ∈ Q, ∃ p : DWalk D x (r.target x),
      p.cost w ≤ r.cost x ∧ p.length ≤ Fintype.card V - 1 := by
    intro x hx
    obtain ⟨p, hp⟩ := r.routes x hx
    obtain ⟨q, hq, hlen⟩ := p.exists_bounded_le_cost w
    exact ⟨q, hq.trans hp, hlen⟩
  choose p hp hlen using hpaths
  let aCost : V → ℕ := fun x => if hx : x ∈ Q then (p x hx).cost w else 0
  let bCost : V → ℕ := fun x => if hx : x ∈ Q then (p x hx).length else 0
  let r' : Routing D (fun u v => C * w u v + 1) Q T :=
    { r.toMatching with
      cost := fun x => C * aCost x + bCost x
      routes := by
        intro x hx
        refine ⟨p x hx, ?_⟩
        simp [aCost, bCost, hx, DWalk.cost_scalar] }
  refine ⟨r', ∑ x ∈ Q, aCost x, ∑ x ∈ Q, bCost x, ?_, ?_, ?_⟩
  · simp [Routing.total, r', Finset.sum_add_distrib, Finset.mul_sum]
  · apply Finset.sum_le_sum
    intro x hx
    simpa [aCost, hx] using hp x hx
  · calc
      (∑ x ∈ Q, bCost x) ≤ ∑ x ∈ Q, (Fintype.card V - 1) := by
        apply Finset.sum_le_sum
        intro x hx
        simpa [bCost, hx] using hlen x hx
      _ = _ := by simp

end IndependentSetDiscovery.WeightedDirected
