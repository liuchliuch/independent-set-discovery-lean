import IndependentSetDiscovery.Basic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Collision-free realization of a path assignment

The auxiliary routing certificate records one walk per source and an integral
upper bound on its length. Its targets form a bijection. No collision-freedom
is assumed of these walks. The theorem `Routing.realize` constructs an actual
collision-free slide sequence with at most the total routing cost.
-/

namespace IndependentSetDiscovery
namespace Movement

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- A bijective assignment between two finite configurations. -/
structure Matching (Q T : Finset V) where
  target : V → V
  injective : Set.InjOn target (↑Q : Set V)
  image_eq : Q.image target = T

/-- A walk certificate for a matching, with a separate nonnegative budget for
each source. Walks may overlap and may run through occupied vertices. -/
structure Routing (G : SimpleGraph V) (Q T : Finset V) extends Matching Q T where
  cost : V → ℕ
  routes : ∀ x ∈ Q, ∃ p : G.Walk x (target x), p.length ≤ cost x

def Routing.total {Q T : Finset V} (a : Routing G Q T) : ℕ := ∑ x ∈ Q, a.cost x

theorem Matching.card_eq {Q T : Finset V} (a : Matching Q T) : T.card = Q.card := by
  rw [← a.image_eq]
  exact Finset.card_image_of_injOn a.injective

def Matching.reindex {Q R T : Finset V} (a : Matching Q T)
    (e : Equiv.Perm V) (he : R.image e = Q) : Matching R T where
  target := a.target ∘ e
  injective := by
    intro x hx y hy hxy
    apply e.injective
    apply a.injective
    · rw [← he]; exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
    · rw [← he]; exact Finset.mem_image.mpr ⟨y, hy, rfl⟩
    · exact hxy
  image_eq := by rw [← Finset.image_image, he, a.image_eq]

theorem swap_image_of_mem {Q : Finset V} {s u : V} (hs : s ∈ Q) (hu : u ∈ Q) :
    Q.image (Equiv.swap s u) = Q := by
  ext x
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    by_cases hys : y = s
    · subst y; simpa using hu
    by_cases hyu : y = u
    · subst y; simpa using hs
    simpa [Equiv.swap_apply_of_ne_of_ne hys hyu] using hy
  · intro hx
    refine ⟨Equiv.swap s u x, ?_, by simp⟩
    by_cases hxs : x = s
    · subst x; simpa using hu
    by_cases hxu : x = u
    · subst x; simpa using hs
    simpa [Equiv.swap_apply_of_ne_of_ne hxs hxu] using hx

theorem swap_image_slide {Q : Finset V} {u v : V} (hu : u ∈ Q) (hv : v ∉ Q) :
    (insert v (Q.erase u)).image (Equiv.swap u v) = Q := by
  have huv : u ≠ v := by rintro rfl; exact hv hu
  rw [Finset.image_insert]
  simp only [Equiv.swap_apply_right]
  have he : (Q.erase u).image (Equiv.swap u v) = Q.erase u := by
    calc
      (Q.erase u).image (Equiv.swap u v) = (Q.erase u).image id := by
        apply Finset.image_congr
        intro x hx
        have hxu : x ≠ u := (Finset.mem_erase.mp hx).1
        have hxv : x ≠ v := by rintro rfl; exact hv (Finset.mem_of_mem_erase hx)
        exact Equiv.swap_apply_of_ne_of_ne hxu hxv
      _ = Q.erase u := Finset.image_id
  rw [he, Finset.insert_erase hu]

/-- Every walk from an occupied source to an unoccupied target has an exit
edge, and splitting at that edge preserves its length exactly. -/
theorem walk_exit {Q : Finset V} {s t : V} (p : G.Walk s t)
    (hs : s ∈ Q) (ht : t ∉ Q) :
    ∃ u v, u ∈ Q ∧ v ∉ Q ∧ ∃ (_h : G.Adj u v)
      (a : G.Walk s u) (b : G.Walk v t), a.length + 1 + b.length = p.length := by
  induction p with
  | nil => exact (ht hs).elim
  | @cons s w t h p ih =>
    by_cases hw : w ∈ Q
    · obtain ⟨u, v, hu, hv, huv, a, b, hab⟩ := ih hw ht
      refine ⟨u, v, hu, hv, huv, .cons h a, b, ?_⟩
      simp only [SimpleGraph.Walk.length_cons] at *
      omega
    · exact ⟨s, w, hs, hw, h, .nil, p, by simp [Nat.add_comm]⟩

def Routing.identity (G : SimpleGraph V) (Q : Finset V) : Routing G Q Q where
  target := id
  injective := fun _ _ _ _ h => h
  image_eq := Finset.image_id
  cost := fun _ => 0
  routes := fun _x _ => ⟨.nil, le_rfl⟩

@[simp] theorem Routing.identity_total (G : SimpleGraph V) (Q : Finset V) :
    (Routing.identity G Q).total = 0 := by simp [Routing.total, Routing.identity]

theorem Routing.exists_empty_target {Q T : Finset V} (a : Routing G Q T)
    (hne : Q ≠ T) : ∃ t ∈ T, t ∉ Q := by
  by_contra! h
  have hsub : T ⊆ Q := h
  have heq : T = Q := Finset.eq_of_subset_of_card_le hsub (by rw [a.toMatching.card_eq])
  exact hne heq.symm

/-- Uncrossing at the first empty vertex gives a legal slide and reduces the
total route budget by at least one. Destination swaps are only bookkeeping. -/
theorem Routing.progress {Q T : Finset V} (r : Routing G Q T) (hne : Q ≠ T) :
    ∃ R, TokenSlide G Q R ∧ ∃ r' : Routing G R T, r'.total + 1 ≤ r.total := by
  obtain ⟨t, ht, htQ⟩ := r.exists_empty_target hne
  obtain ⟨s, hs, hst⟩ := Finset.mem_image.mp (r.image_eq.symm ▸ ht)
  obtain ⟨p, hp⟩ := r.routes s hs
  have htarget : r.target s ∉ Q := by rwa [hst]
  obtain ⟨u, v, hu, hv, huv, a, b, hab⟩ := walk_exit p hs htarget
  have hvu : v ≠ u := by rintro rfl; exact hv hu
  have hv' : v ∉ Q.erase u := fun h => hv (Finset.mem_of_mem_erase h)
  refine ⟨insert v (Q.erase u), ⟨u, hu, v, hv, huv, rfl⟩, ?_⟩
  by_cases hus : u = s
  · subst u
    let m := r.toMatching.reindex (Equiv.swap s v) (swap_image_slide hs hv)
    let c := Function.update r.cost v b.length
    have hroutes : ∀ x ∈ insert v (Q.erase s), ∃ q : G.Walk x (m.target x),
        q.length ≤ c x := by
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
        simpa [c, hxv] using r.routes x (Finset.mem_of_mem_erase hx')
    let r' : Routing G (insert v (Q.erase s)) T := ⟨m, c, hroutes⟩
    refine ⟨r', ?_⟩
    have hsum := Finset.sum_erase_add Q r.cost hs
    have htotal : r'.total = b.length + ∑ x ∈ Q.erase s, r.cost x := by
      simp only [Routing.total, r', c, Finset.sum_insert hv', Function.update_self]
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
    have hroutes : ∀ x ∈ insert v (Q.erase u), ∃ q : G.Walk x (m.target x),
        q.length ≤ c x := by
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
          obtain ⟨q, hq⟩ := r.routes u hu
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
          simpa [c, hxv, hxs] using r.routes x (Finset.mem_of_mem_erase hx')
    let r' : Routing G (insert v (Q.erase u)) T := ⟨m, c, hroutes⟩
    refine ⟨r', ?_⟩
    have hsum₁ := Finset.sum_erase_add Q r.cost hu
    have hsum₂ := Finset.sum_erase_add (Q.erase u) r.cost hs'
    have htotal : r'.total = b.length + (a.length + r.cost u) +
        ∑ x ∈ (Q.erase u).erase s, r.cost x := by
      simp only [Routing.total, r', c, Finset.sum_insert hv', Function.update_self]
      rw [Finset.sum_update_of_notMem hv', Finset.sum_update_of_mem hs']
      simp [Finset.sdiff_singleton_eq_erase, Nat.add_assoc]
    rw [htotal]
    change _ ≤ ∑ x ∈ Q, r.cost x
    omega

/-- Constructive part of Lemma 3.1, for arbitrary (possibly intersecting)
assigned walks, not only shortest walks. -/
theorem Routing.realize {Q T : Finset V} (r : Routing G Q T) :
    ∃ n ≤ r.total, SlideSequence G Q T n := by
  generalize hn : r.total = N
  induction N using Nat.strong_induction_on generalizing Q r with
  | h N ih =>
    by_cases hQT : Q = T
    · subst Q
      exact ⟨0, Nat.zero_le _, .nil T⟩
    obtain ⟨R, hQR, r', hr'⟩ := r.progress hQT
    have hlt : r'.total < N := by omega
    obtain ⟨n, hn', hseq⟩ := ih r'.total hlt r' rfl
    exact ⟨n + 1, by omega, .cons hQR hseq⟩

/-- Pull a route assignment back across an actual slide. This is the token
label-tracking direction of the assignment-distance lemma. -/
theorem Routing.prepend {Q R T : Finset V} (h : TokenSlide G Q R) (r : Routing G R T) :
    ∃ r' : Routing G Q T, r'.total = r.total + 1 := by
  rcases h with ⟨u, hu, v, hv, huv, rfl⟩
  have huv' : u ≠ v := by rintro rfl; exact hv hu
  have hv' : v ∉ Q.erase u := fun h => hv (Finset.mem_of_mem_erase h)
  have himage : Q.image (Equiv.swap u v) = insert v (Q.erase u) := by
    have he := congrArg (Finset.image (Equiv.swap u v)) (swap_image_slide hu hv)
    simpa [Finset.image_image, Function.comp_def] using he.symm
  let m := r.toMatching.reindex (Equiv.swap u v) himage
  let c := Function.update r.cost u (r.cost v + 1)
  have hroutes : ∀ x ∈ Q, ∃ q : G.Walk x (m.target x), q.length ≤ c x := by
    intro x hx
    by_cases hxu : x = u
    · subst x
      obtain ⟨q, hq⟩ := r.routes v (Finset.mem_insert_self _ _)
      have hq' : (SimpleGraph.Walk.cons huv q).length ≤ r.cost v + 1 := by
        simpa using Nat.add_le_add_right hq 1
      have hm : m.target u = r.target v := by simp [m, Matching.reindex]
      rw [hm]
      exact ⟨.cons huv q, by simpa [c] using hq'⟩
    · have hxv : x ≠ v := by rintro rfl; exact hv hx
      have hx' : x ∈ insert v (Q.erase u) :=
        Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hxu, hx⟩)
      have hm : m.target x = r.target x := by
        simp [m, Matching.reindex, Equiv.swap_apply_of_ne_of_ne hxu hxv]
      rw [hm]
      simpa [c, hxu] using r.routes x hx'
  let r' : Routing G Q T := ⟨m, c, hroutes⟩
  refine ⟨r', ?_⟩
  change (∑ x ∈ Q, Function.update r.cost u (r.cost v + 1) x) =
    (∑ x ∈ insert v (Q.erase u), r.cost x) + 1
  rw [Finset.sum_update_of_mem hu, Finset.sum_insert hv']
  simp [Finset.sdiff_singleton_eq_erase, Nat.add_comm, Nat.add_left_comm]

theorem routing_of_slideSequence {Q T : Finset V} {n : ℕ} (h : SlideSequence G Q T n) :
    ∃ r : Routing G Q T, r.total = n := by
  induction h with
  | nil Q => exact ⟨Routing.identity G Q, Routing.identity_total G Q⟩
  | cons hs _ ih =>
    obtain ⟨r, hr⟩ := ih
    obtain ⟨r', hr'⟩ := r.prepend hs
    exact ⟨r', by omega⟩

theorem routing_iff_slides_within {Q T : Finset V} {b : ℕ} :
    (∃ r : Routing G Q T, r.total ≤ b) ↔ ∃ n ≤ b, SlideSequence G Q T n := by
  constructor
  · rintro ⟨r, hr⟩
    obtain ⟨n, hn, hs⟩ := r.realize
    exact ⟨n, hn.trans hr, hs⟩
  · rintro ⟨n, hn, hs⟩
    obtain ⟨r, hr⟩ := routing_of_slideSequence hs
    exact ⟨r, hr.symm ▸ hn⟩

end Movement
end IndependentSetDiscovery
