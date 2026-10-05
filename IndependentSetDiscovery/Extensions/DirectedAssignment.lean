import IndependentSetDiscovery.Extensions.DirectedRouting
import Mathlib.Data.ENat.Lattice
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Exact assignment characterization for directed positive weighted motion -/

namespace IndependentSetDiscovery.WeightedDirected

variable {V : Type*} [DecidableEq V]
variable {D : V → V → Prop} {w : V → V → ℕ}

/-- Directed weighted shortest-path distance, with infinity for no path. -/
noncomputable def distance (D : V → V → Prop) (w : V → V → ℕ) (u v : V) : ℕ∞ :=
  ⨅ p : DWalk D u v, (p.cost w : ℕ∞)

noncomputable def Matching.distanceCost {Q T : Finset V} (a : Matching Q T)
    (D : V → V → Prop) (w : V → V → ℕ) : ℕ∞ :=
  ∑ x ∈ Q, distance D w x (a.target x)

noncomputable def assignmentDistance (D : V → V → Prop) (w : V → V → ℕ)
    (Q T : Finset V) : ℕ∞ := ⨅ a : Matching Q T, a.distanceCost D w

noncomputable def sequenceDistance (D : V → V → Prop) (w : V → V → ℕ)
    (Q T : Finset V) : ℕ∞ :=
  ⨅ c : {c : ℕ // ∃ n, DirectedSlideSequence D w Q T c n}, (c.val : ℕ∞)

theorem DWalk.distance_le {u v : V} (p : DWalk D u v) :
    distance D w u v ≤ p.cost w :=
  iInf_le (fun p : DWalk D u v => (p.cost w : ℕ∞)) p

theorem Routing.distanceCost_le {Q T : Finset V} (r : Routing D w Q T) :
    r.toMatching.distanceCost D w ≤ (r.total : ℕ∞) := by
  unfold Matching.distanceCost Routing.total
  rw [Nat.cast_sum]
  apply Finset.sum_le_sum
  intro x hx
  obtain ⟨p, hp⟩ := r.routes x hx
  exact p.distance_le.trans (by exact_mod_cast hp)

theorem Matching.routing_of_finite {Q T : Finset V} (a : Matching Q T)
    (h : a.distanceCost D w ≠ ⊤) :
    ∃ r : Routing D w Q T, r.toMatching = a ∧ (r.total : ℕ∞) = a.distanceCost D w := by
  have hfinite : ∀ x ∈ Q, distance D w x (a.target x) ≠ ⊤ := by
    intro x hx
    apply ne_top_of_le_ne_top h
    change distance D w x (a.target x) ≤ ∑ y ∈ Q, distance D w y (a.target y)
    exact Finset.single_le_sum (f := fun y => distance D w y (a.target y))
      (fun _ _ => bot_le) hx
  let r : Routing D w Q T :=
    { a with
      cost := fun x => (distance D w x (a.target x)).toNat
      routes := by
        intro x hx
        haveI : Nonempty (DWalk D x (a.target x)) :=
          ENat.iInf_coe_ne_top.mp (hfinite x hx)
        obtain ⟨p, hp⟩ := ENat.exists_eq_iInf
          (fun p : DWalk D x (a.target x) => (p.cost w : ℕ∞))
        refine ⟨p, ?_⟩
        have heq : (p.cost w : ℕ∞) = distance D w x (a.target x) := hp
        rw [← heq]
        simp }
  refine ⟨r, rfl, ?_⟩
  unfold Routing.total Matching.distanceCost
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro x hx
  exact ENat.coe_toNat (hfinite x hx)

/-- The directed positive-weight assignment optimum is exactly the true
collision-free movement optimum, including unreachable instances. -/
theorem assignmentDistance_eq_sequenceDistance
    (hpos : ∀ u v, D u v → 0 < w u v) (Q T : Finset V) :
    assignmentDistance D w Q T = sequenceDistance D w Q T := by
  apply le_antisymm
  · apply le_iInf
    intro c
    obtain ⟨n, hn⟩ := c.property
    obtain ⟨r, hr⟩ := routing_of_directedSlideSequence hn
    exact (iInf_le (fun a : Matching Q T => a.distanceCost D w) r.toMatching).trans
      (hr ▸ r.distanceCost_le)
  · apply le_iInf
    intro a
    by_cases h : a.distanceCost D w = ⊤
    · rw [h]; exact le_top
    obtain ⟨r, _, hr⟩ := a.routing_of_finite h
    obtain ⟨c, n, hc, hs⟩ := r.realize hpos
    exact (iInf_le
      (fun c : {c : ℕ // ∃ n, DirectedSlideSequence D w Q T c n} => (c.val : ℕ∞))
      ⟨c, n, hs⟩).trans (hr ▸ (show (c : ℕ∞) ≤ r.total by exact_mod_cast hc))

theorem assignmentDistance_eq_top_iff
    (hpos : ∀ u v, D u v → 0 < w u v) (Q T : Finset V) :
    assignmentDistance D w Q T = ⊤ ↔ ¬ ∃ c n, DirectedSlideSequence D w Q T c n := by
  rw [assignmentDistance_eq_sequenceDistance hpos]
  simp only [sequenceDistance, ENat.iInf_coe_eq_top, isEmpty_subtype]
  simp

theorem exists_minimum_cost_sequence
    (hpos : ∀ u v, D u v → 0 < w u v) {Q T : Finset V}
    (h : assignmentDistance D w Q T ≠ ⊤) :
    ∃ c n, DirectedSlideSequence D w Q T c n ∧
      (c : ℕ∞) = assignmentDistance D w Q T := by
  rw [assignmentDistance_eq_sequenceDistance hpos] at h ⊢
  haveI : Nonempty {c : ℕ // ∃ n, DirectedSlideSequence D w Q T c n} :=
    ENat.iInf_coe_ne_top.mp h
  obtain ⟨c, hc⟩ := ENat.exists_eq_iInf
    (fun c : {c : ℕ // ∃ n, DirectedSlideSequence D w Q T c n} => (c.val : ℕ∞))
  obtain ⟨n, hn⟩ := c.property
  exact ⟨c.val, n, hn, hc⟩

end IndependentSetDiscovery.WeightedDirected
