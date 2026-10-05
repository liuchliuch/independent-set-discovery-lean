import IndependentSetDiscovery.Extensions.DirectedMovement
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Collision-free realization of directed weighted path assignments

The constructive exchange argument works without symmetry. Positive integral
arc weights provide a well-founded measure. Apply it to `C*w+1` for the
lexicographic objective of Corollary 5.6.
-/

namespace IndependentSetDiscovery.WeightedDirected

variable {V : Type*} [DecidableEq V]

inductive DWalk (D : V → V → Prop) : V → V → Type _
  | nil {u} : DWalk D u u
  | cons {u v t} : D u v → DWalk D v t → DWalk D u t

namespace DWalk

variable {D : V → V → Prop} {u v t : V}

def cost (w : V → V → ℕ) : {u v : V} → DWalk D u v → ℕ
  | _, _, .nil => 0
  | _, _, @DWalk.cons _ _ u v t _ p => w u v + cost w p

@[simp] theorem cost_nil (w : V → V → ℕ) : (DWalk.nil (u := u) (D := D)).cost w = 0 := rfl

@[simp] theorem cost_cons (w : V → V → ℕ) (h : D u v) (p : DWalk D v t) :
    (DWalk.cons h p).cost w = w u v + p.cost w := rfl

def append : {u v t : V} → DWalk D u v → DWalk D v t → DWalk D u t
  | _, _, _, .nil, q => q
  | _, _, _, .cons h p, q => .cons h (append p q)

@[simp] theorem cost_append (w : V → V → ℕ) (p : DWalk D u v) (q : DWalk D v t) :
    (p.append q).cost w = p.cost w + q.cost w := by
  induction p with
  | nil => simp [append]
  | cons h p ih => simp [append, ih, Nat.add_assoc]

end DWalk

variable {D : V → V → Prop} {w : V → V → ℕ}

/-- A bijective assignment between two finite configurations. -/
structure Matching (Q T : Finset V) where
  target : V → V
  injective : Set.InjOn target (↑Q : Set V)
  image_eq : Q.image target = T

/-- A walk certificate for a matching, with a separate nonnegative budget for
each source. Walks may overlap and may run through occupied vertices. -/
structure Routing (D : V → V → Prop) (w : V → V → ℕ) (Q T : Finset V) extends Matching Q T where
  cost : V → ℕ
  routes : ∀ x ∈ Q, ∃ p : DWalk D x (target x), p.cost w ≤ cost x

def Routing.total {Q T : Finset V} (a : Routing D w Q T) : ℕ := ∑ x ∈ Q, a.cost x

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
theorem walk_exit {Q : Finset V} {s t : V} (p : DWalk D s t)
    (hs : s ∈ Q) (ht : t ∉ Q) :
    ∃ u v, u ∈ Q ∧ v ∉ Q ∧ ∃ (h : D u v)
      (a : DWalk D s u) (b : DWalk D v t), a.cost w + w u v + b.cost w = p.cost w := by
  induction p with
  | nil => exact (ht hs).elim
  | @cons s w t h p ih =>
    by_cases hw : w ∈ Q
    · obtain ⟨u, v, hu, hv, huv, a, b, hab⟩ := ih hw ht
      refine ⟨u, v, hu, hv, huv, .cons h a, b, ?_⟩
      simp only [DWalk.cost_cons] at *
      omega
    · exact ⟨s, w, hs, hw, h, .nil, p, by simp [DWalk.cost, Nat.add_comm]⟩

def Routing.identity (D : V → V → Prop) (w : V → V → ℕ) (Q : Finset V) : Routing D w Q Q where
  target := id
  injective := fun _ _ _ _ h => h
  image_eq := Finset.image_id
  cost := fun _ => 0
  routes := fun x _ => ⟨.nil, le_rfl⟩

@[simp] theorem Routing.identity_total (D : V → V → Prop) (w : V → V → ℕ) (Q : Finset V) :
    (Routing.identity D w Q).total = 0 := by simp [Routing.total, Routing.identity]

theorem Routing.exists_empty_target {Q T : Finset V} (a : Routing D w Q T)
    (hne : Q ≠ T) : ∃ t ∈ T, t ∉ Q := by
  by_contra! h
  have hsub : T ⊆ Q := h
  have heq : T = Q := Finset.eq_of_subset_of_card_le hsub (by rw [a.toMatching.card_eq])
  exact hne heq.symm

/-- Uncrossing at the first empty vertex gives a legal slide and reduces the
total route budget by at least one. Destination swaps are only bookkeeping. -/
theorem Routing.progress {Q T : Finset V} (r : Routing D w Q T) (hne : Q ≠ T) :
    ∃ R u v, DirectedTokenSlide D Q R u v ∧
      ∃ r' : Routing D w R T, r'.total + w u v ≤ r.total := by
  obtain ⟨t, ht, htQ⟩ := r.exists_empty_target hne
  obtain ⟨s, hs, hst⟩ := Finset.mem_image.mp (r.image_eq.symm ▸ ht)
  obtain ⟨p, hp⟩ := r.routes s hs
  have htarget : r.target s ∉ Q := by rwa [hst]
  obtain ⟨u, v, hu, hv, huv, a, b, hab⟩ := walk_exit (w := w) p hs htarget
  have hvu : v ≠ u := by rintro rfl; exact hv hu
  have hv' : v ∉ Q.erase u := fun h => hv (Finset.mem_of_mem_erase h)
  refine ⟨insert v (Q.erase u), u, v, ⟨hu, hv, huv, rfl⟩, ?_⟩
  by_cases hus : u = s
  · subst u
    let m := r.toMatching.reindex (Equiv.swap s v) (swap_image_slide hs hv)
    let c := Function.update r.cost v (b.cost w)
    have hroutes : ∀ x ∈ insert v (Q.erase s), ∃ q : DWalk D x (m.target x),
        q.cost w ≤ c x := by
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
    let r' : Routing D w (insert v (Q.erase s)) T := ⟨m, c, hroutes⟩
    refine ⟨r', ?_⟩
    have hsum := Finset.sum_erase_add Q r.cost hs
    have htotal : r'.total = b.cost w + ∑ x ∈ Q.erase s, r.cost x := by
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
    let c := Function.update (Function.update r.cost s (a.cost w + r.cost u)) v (b.cost w)
    have hroutes : ∀ x ∈ insert v (Q.erase u), ∃ q : DWalk D x (m.target x),
        q.cost w ≤ c x := by
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
          have hq' : (a.append q).cost w ≤ a.cost w + r.cost u := by
            simpa using Nat.add_le_add_left hq (a.cost w)
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
    let r' : Routing D w (insert v (Q.erase u)) T := ⟨m, c, hroutes⟩
    refine ⟨r', ?_⟩
    have hsum₁ := Finset.sum_erase_add Q r.cost hu
    have hsum₂ := Finset.sum_erase_add (Q.erase u) r.cost hs'
    have htotal : r'.total = b.cost w + (a.cost w + r.cost u) +
        ∑ x ∈ (Q.erase u).erase s, r.cost x := by
      simp only [Routing.total, r', c, Finset.sum_insert hv', Function.update_self]
      rw [Finset.sum_update_of_notMem hv', Finset.sum_update_of_mem hs']
      simp [Finset.sdiff_singleton_eq_erase, Nat.add_assoc]
    rw [htotal]
    change _ ≤ ∑ x ∈ Q, r.cost x
    omega

/-- Directed weighted assignment realization: all actual moves enter empty vertices. -/
theorem Routing.realize (hpos : ∀ u v, D u v → 0 < w u v)
    {Q T : Finset V} (r : Routing D w Q T) :
    ∃ c n, c ≤ r.total ∧ DirectedSlideSequence D w Q T c n := by
  generalize hn : r.total = N
  induction N using Nat.strong_induction_on generalizing Q r with
  | h N ih =>
    by_cases hQT : Q = T
    · subst Q
      exact ⟨0, 0, Nat.zero_le _, .nil T⟩
    obtain ⟨R, u, v, hQR, r', hr'⟩ := r.progress hQT
    have hw := hpos u v hQR.2.2.1
    have hlt : r'.total < N := by omega
    obtain ⟨c, n, hc, hseq⟩ := ih r'.total hlt r' rfl
    exact ⟨w u v + c, n + 1, by omega, .cons hQR hseq⟩

/-- The scalarized weights used in Corollary 5.6 are strictly positive. -/
theorem scalarized_routing_realize (C : ℕ) {Q T : Finset V}
    (r : Routing D (fun u v => C * w u v + 1) Q T) :
    ∃ c n, C * c + n ≤ r.total ∧ DirectedSlideSequence D w Q T c n := by
  obtain ⟨z, n, hz, hs⟩ := r.realize (by intro u v h; omega)
  obtain ⟨c, hc, heq⟩ := hs.unscalarize
  exact ⟨c, n, heq ▸ hz, hc⟩

/-- Pull a route assignment back across an actual slide. This is the token
label-tracking direction of the assignment-distance lemma. -/
theorem Routing.prepend {Q R T : Finset V} {u v : V} (h : DirectedTokenSlide D Q R u v) (r : Routing D w R T) :
    ∃ r' : Routing D w Q T, r'.total = r.total + w u v := by
  rcases h with ⟨hu, hv, huv, rfl⟩
  have huv' : u ≠ v := by rintro rfl; exact hv hu
  have hv' : v ∉ Q.erase u := fun h => hv (Finset.mem_of_mem_erase h)
  have himage : Q.image (Equiv.swap u v) = insert v (Q.erase u) := by
    have he := congrArg (Finset.image (Equiv.swap u v)) (swap_image_slide hu hv)
    simpa [Finset.image_image, Function.comp_def] using he.symm
  let m := r.toMatching.reindex (Equiv.swap u v) himage
  let c := Function.update r.cost u (w u v + r.cost v)
  have hroutes : ∀ x ∈ Q, ∃ q : DWalk D x (m.target x), q.cost w ≤ c x := by
    intro x hx
    by_cases hxu : x = u
    · subst x
      obtain ⟨q, hq⟩ := r.routes v (Finset.mem_insert_self _ _)
      have hq' : (DWalk.cons huv q).cost w ≤ w u v + r.cost v := by
        simpa using Nat.add_le_add_left hq (w u v)
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
  let r' : Routing D w Q T := ⟨m, c, hroutes⟩
  refine ⟨r', ?_⟩
  change (∑ x ∈ Q, Function.update r.cost u (w u v + r.cost v) x) =
    (∑ x ∈ insert v (Q.erase u), r.cost x) + w u v
  rw [Finset.sum_update_of_mem hu, Finset.sum_insert hv']
  simp [Finset.sdiff_singleton_eq_erase, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem routing_of_directedSlideSequence {Q T : Finset V} {c n : ℕ}
    (h : DirectedSlideSequence D w Q T c n) :
    ∃ r : Routing D w Q T, r.total = c := by
  induction h with
  | nil Q => exact ⟨Routing.identity D w Q, Routing.identity_total D w Q⟩
  | cons hs _ ih =>
      obtain ⟨r, hr⟩ := ih
      obtain ⟨r', hr'⟩ := r.prepend hs
      exact ⟨r', by omega⟩

theorem routing_iff_directedSlides_within (hpos : ∀ u v, D u v → 0 < w u v)
    {Q T : Finset V} {b : ℕ} :
    (∃ r : Routing D w Q T, r.total ≤ b) ↔
      ∃ c n, c ≤ b ∧ DirectedSlideSequence D w Q T c n := by
  constructor
  · rintro ⟨r, hr⟩
    obtain ⟨c, n, hc, hs⟩ := r.realize hpos
    exact ⟨c, n, hc.trans hr, hs⟩
  · rintro ⟨c, n, hc, hs⟩
    obtain ⟨r, hr⟩ := routing_of_directedSlideSequence hs
    exact ⟨r, hr.symm ▸ hc⟩

end IndependentSetDiscovery.WeightedDirected
