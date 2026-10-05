import IndependentSetDiscovery.Extensions.DirectedOptimal
import IndependentSetDiscovery.Weighted

/-! # The actual two-graph weighted-transversal reduction of Corollary 5.6 -/

namespace IndependentSetDiscovery.WeightedDirected

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {Gf : SimpleGraph V} {D : V → V → Prop} {w : V → V → ℕ}

theorem distance_path_of_ne_top {u v : V} (h : distance D w u v ≠ ⊤) :
    ∃ p : DWalk D u v, p.cost w = (distance D w u v).toNat := by
  haveI : Nonempty (DWalk D u v) := ENat.iInf_coe_ne_top.mp h
  obtain ⟨p, hp⟩ := ENat.exists_eq_iInf (fun p : DWalk D u v => (p.cost w : ℕ∞))
  refine ⟨p, ?_⟩
  have heq : (p.cost w : ℕ∞) = distance D w u v := hp
  rw [← heq]
  simp

theorem DWalk.distance_toNat_le {u v : V} (p : DWalk D u v) :
    (distance D w u v).toNat ≤ p.cost w := by
  have hfin : distance D w u v ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.coe_ne_top _) p.distance_le
  have h : ((distance D w u v).toNat : ℕ∞) ≤ p.cost w := by
    rw [ENat.coe_toNat hfin]
    exact p.distance_le
  exact_mod_cast h

noncomputable def movementInstance (Gf : SimpleGraph V) (D : V → V → Prop)
    (w : V → V → ℕ) (S : Finset V) : WeightedInstance S V := by
  classical
  exact
    { graph := Gf
      candidates := fun s => Finset.univ.filter fun v => distance D w s.val v ≠ ⊤
      cost := fun s v => ((distance D w s.val v).toNat : ℚ)
      nonneg := by intro s v _; positivity }

@[simp] theorem movementInstance_mem (Gf : SimpleGraph V) (D : V → V → Prop)
    (w : V → V → ℕ) (S : Finset V) (s : S) (v : V) :
    v ∈ (movementInstance Gf D w S).candidates s ↔ distance D w s.val v ≠ ⊤ := by
  classical
  simp [movementInstance]

def extendSelection (S : Finset V) (x : S → V) (v : V) : V :=
  if hv : v ∈ S then x ⟨v, hv⟩ else v

@[simp] theorem extendSelection_apply (S : Finset V) (x : S → V) (s : S) :
    extendSelection S x s.val = x s := by simp [extendSelection, s.property]

theorem routing_of_selection {S : Finset V} {x : S → V}
    (hx : (movementInstance Gf D w S).Selection x) :
    ∃ T, Independent Gf T ∧ ∃ r : Routing D w S T,
      (r.total : ℚ) = (movementInstance Gf D w S).selectionCost x := by
  let f := extendSelection S x
  have hreach : ∀ s : S, distance D w s.val (x s) ≠ ⊤ := by
    intro s
    exact (movementInstance_mem Gf D w S s (x s)).mp (hx.1 s)
  have hi : Set.InjOn f (↑S : Set V) := by
    intro u hu v hv heq
    have hu' : u ∈ S := hu
    have hv' : v ∈ S := hv
    have heq' : x ⟨u, hu⟩ = x ⟨v, hv⟩ := by
      simpa [f, extendSelection, hu', hv'] using heq
    exact congrArg Subtype.val (hx.2.1 heq')
  have hind : Independent Gf (S.image f) := by
    intro u hu v hv huv
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hv
    have hst : (⟨s, hs⟩ : S) ≠ ⟨t, ht⟩ := by
      intro heq
      exact huv (congrArg f (congrArg Subtype.val heq))
    have hadj := hx.2.2 ⟨s, hs⟩ ⟨t, ht⟩ hst
    simpa [f, extendSelection, hs, ht, movementInstance] using hadj
  let r : Routing D w S (S.image f) :=
    { target := f
      injective := hi
      image_eq := rfl
      cost := fun s => (distance D w s (f s)).toNat
      routes := by
        intro s hs
        have h : distance D w s (f s) ≠ ⊤ := by
          simpa [f, extendSelection, hs] using hreach ⟨s, hs⟩
        obtain ⟨p, hp⟩ := distance_path_of_ne_top h
        exact ⟨p, hp.le⟩ }
  refine ⟨S.image f, hind, r, ?_⟩
  change (↑(∑ s ∈ S, (distance D w s (f s)).toNat) : ℚ) =
    ∑ s : S, ((distance D w s.val (x s)).toNat : ℚ)
  rw [Nat.cast_sum, ← Finset.sum_coe_sort S]
  apply Finset.sum_congr rfl
  intro s _
  simp [f]

theorem selection_of_routing {S T : Finset V} (hT : Independent Gf T)
    (r : Routing D w S T) :
    ∃ x : S → V, (movementInstance Gf D w S).Selection x ∧
      (movementInstance Gf D w S).selectionCost x ≤ (r.total : ℚ) := by
  let x : S → V := fun s => r.target s.val
  have hselect : (movementInstance Gf D w S).Selection x := by
    refine ⟨?_, ?_, ?_⟩
    · intro s
      apply (movementInstance_mem Gf D w S s (x s)).mpr
      obtain ⟨p, _⟩ := r.routes s.val s.property
      exact ne_top_of_le_ne_top (ENat.coe_ne_top _) p.distance_le
    · intro s t hst
      apply Subtype.ext
      exact r.injective s.property t.property hst
    · intro s t hst
      apply hT
      · rw [← r.image_eq]; exact Finset.mem_image.mpr ⟨s.val, s.property, rfl⟩
      · rw [← r.image_eq]; exact Finset.mem_image.mpr ⟨t.val, t.property, rfl⟩
      · intro heq
        apply hst
        exact Subtype.ext (r.injective s.property t.property heq)
  refine ⟨x, hselect, ?_⟩
  change (∑ s : S, ((distance D w s.val (r.target s.val)).toNat : ℚ)) ≤ (r.total : ℚ)
  rw [Finset.sum_coe_sort S (fun s => ((distance D w s (r.target s)).toNat : ℚ))]
  change (∑ s ∈ S, ((distance D w s (r.target s)).toNat : ℚ)) ≤
    ((∑ s ∈ S, r.cost s : ℕ) : ℚ)
  rw [Nat.cast_sum]
  apply Finset.sum_le_sum
  intro s hs
  obtain ⟨p, hp⟩ := r.routes s hs
  exact_mod_cast p.distance_toNat_le.trans hp

/-- Full semantic transfer of the two-graph optimum from the weighted static
solver to a real lexicographically optimal collision-free directed sequence. -/
theorem optimal_selection_realizes_lex {S : Finset V} {x : S → V}
    (hx : (movementInstance Gf D
      (fun u v => scalarizationBase S.card (Fintype.card V) * w u v + 1) S).Optimal x) :
    ∃ T c n, LexOptimal Gf D w S T c n ∧ n ≤ S.card * (Fintype.card V - 1) := by
  obtain ⟨T, hT, r, hr⟩ := routing_of_selection hx.1
  have hmin : ∀ T', Independent Gf T' →
      ∀ r' : Routing D
        (fun u v => scalarizationBase S.card (Fintype.card V) * w u v + 1) S T',
        r.total ≤ r'.total := by
    intro T' hT' r'
    obtain ⟨y, hy, hcost⟩ := selection_of_routing hT' r'
    have h := (hx.2 y hy).trans hcost
    rw [← hr] at h
    exact_mod_cast h
  obtain ⟨c, n, hopt, hlen, _⟩ := reconstruct_lex_optimal Gf D w r hT hmin
  exact ⟨T, c, n, hopt, hlen⟩

theorem no_selection_iff_unreachable (Gf : SimpleGraph V) (D : V → V → Prop)
    (w : V → V → ℕ) (S : Finset V) (hpos : ∀ u v, D u v → 0 < w u v) :
    (¬ ∃ x, (movementInstance Gf D w S).Selection x) ↔
      ¬ ∃ T c n, Independent Gf T ∧ DirectedSlideSequence D w S T c n := by
  constructor
  · intro h ⟨T, c, n, hT, hs⟩
    obtain ⟨r, _⟩ := routing_of_directedSlideSequence hs
    obtain ⟨x, hx, _⟩ := selection_of_routing hT r
    exact h ⟨x, hx⟩
  · intro h ⟨x, hx⟩
    obtain ⟨T, hT, r, _⟩ := routing_of_selection hx
    obtain ⟨c, n, _, hs⟩ := r.realize hpos
    exact h ⟨T, c, n, hT, hs⟩

end IndependentSetDiscovery.WeightedDirected
