import IndependentSetDiscovery.Movement.Routing
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Exact assignment distance and token-slide distance

This module proves Lemma 3.1 and the semantic part of Corollaries 3.2--3.3.
All minima live in `ℕ∞`: an unreachable pair has infinite distance, and an
empty family has infinite minimum. No connectedness or nonempty-token
assumption is imposed.
-/

namespace IndependentSetDiscovery
namespace Movement

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- The sum of shortest-path distances of a particular bijective assignment. -/
noncomputable def Matching.distanceCost {Q T : Finset V} (a : Matching Q T)
    (G : SimpleGraph V) : ℕ∞ := ∑ x ∈ Q, G.edist x (a.target x)

/-- The paper's assignment distance: the minimum over all bijective assignments. -/
noncomputable def assignmentDistance (G : SimpleGraph V) (Q T : Finset V) : ℕ∞ :=
  ⨅ a : Matching Q T, a.distanceCost G

/-- Minimum length among actual collision-free slide sequences. -/
noncomputable def slideDistance (G : SimpleGraph V) (Q T : Finset V) : ℕ∞ :=
  ⨅ n : {n : ℕ // SlideSequence G Q T n}, (n.val : ℕ∞)

theorem Routing.distanceCost_le {Q T : Finset V} (r : Routing G Q T) :
    r.toMatching.distanceCost G ≤ (r.total : ℕ∞) := by
  unfold Matching.distanceCost Routing.total
  rw [Nat.cast_sum]
  apply Finset.sum_le_sum
  intro x hx
  obtain ⟨p, hp⟩ := r.routes x hx
  exact p.edist_le.trans (by exact_mod_cast hp)

/-- Finite shortest-path assignment costs have explicit walk witnesses. -/
theorem Matching.routing_of_finite {Q T : Finset V} (a : Matching Q T)
    (h : a.distanceCost G ≠ ⊤) :
    ∃ r : Routing G Q T, r.toMatching = a ∧ (r.total : ℕ∞) = a.distanceCost G := by
  have hfinite : ∀ x ∈ Q, G.edist x (a.target x) ≠ ⊤ := by
    intro x hx
    apply ne_top_of_le_ne_top h
    change G.edist x (a.target x) ≤ ∑ y ∈ Q, G.edist y (a.target y)
    exact Finset.single_le_sum (f := fun y => G.edist y (a.target y)) (fun _ _ => bot_le) hx
  let r : Routing G Q T :=
    { a with
      cost := fun x => G.dist x (a.target x)
      routes := by
        intro x hx
        obtain ⟨p, hp⟩ := (SimpleGraph.reachable_of_edist_ne_top (hfinite x hx)).exists_walk_length_eq_dist
        exact ⟨p, hp.le⟩ }
  refine ⟨r, rfl, ?_⟩
  unfold Routing.total Matching.distanceCost
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro x hx
  exact ENat.coe_toNat (hfinite x hx)

theorem Matching.realize {Q T : Finset V} (a : Matching Q T) {b : ℕ}
    (h : a.distanceCost G ≤ b) : ∃ n ≤ b, SlideSequence G Q T n := by
  have hfin : a.distanceCost G ≠ ⊤ := ne_top_of_le_ne_top (ENat.coe_ne_top _) h
  obtain ⟨r, _, hr⟩ := a.routing_of_finite hfin
  obtain ⟨n, hn, hs⟩ := r.realize
  refine ⟨n, ?_, hs⟩
  have : (r.total : ℕ∞) ≤ b := hr.symm ▸ h
  exact hn.trans (by exact_mod_cast this)

/-- Lemma 3.1: the genuine graph-distance matching optimum equals the genuine
collision-free slide-sequence optimum. -/
theorem assignmentDistance_eq_slideDistance (G : SimpleGraph V) (Q T : Finset V) :
    assignmentDistance G Q T = slideDistance G Q T := by
  apply le_antisymm
  · apply le_iInf
    intro n
    obtain ⟨r, hr⟩ := routing_of_slideSequence n.property
    exact (iInf_le (fun a : Matching Q T => a.distanceCost G) r.toMatching).trans
      (hr ▸ r.distanceCost_le)
  · apply le_iInf
    intro a
    by_cases h : a.distanceCost G = ⊤
    · rw [h]; exact le_top
    obtain ⟨r, _, hr⟩ := a.routing_of_finite h
    obtain ⟨n, hn, hs⟩ := r.realize
    exact (iInf_le (fun n : {n : ℕ // SlideSequence G Q T n} => (n.val : ℕ∞))
      ⟨n, hs⟩).trans (hr ▸ (show (n : ℕ∞) ≤ r.total by exact_mod_cast hn))

theorem slideDistance_eq_top_iff (G : SimpleGraph V) (Q T : Finset V) :
    slideDistance G Q T = ⊤ ↔ ¬ ∃ n, SlideSequence G Q T n := by
  simp only [slideDistance, ENat.iInf_coe_eq_top, isEmpty_subtype]
  simp

/-- Unreachability is reported exactly when every assignment has infinite cost. -/
theorem assignmentDistance_eq_top_iff (G : SimpleGraph V) (Q T : Finset V) :
    assignmentDistance G Q T = ⊤ ↔ ¬ ∃ n, SlideSequence G Q T n := by
  rw [assignmentDistance_eq_slideDistance, slideDistance_eq_top_iff]

/-- A finite optimum is attained by an actual shortest collision-free sequence. -/
theorem exists_shortest_sequence {Q T : Finset V}
    (h : assignmentDistance G Q T ≠ ⊤) :
    ∃ n, SlideSequence G Q T n ∧ (n : ℕ∞) = assignmentDistance G Q T := by
  rw [assignmentDistance_eq_slideDistance] at h ⊢
  haveI : Nonempty {n : ℕ // SlideSequence G Q T n} := ENat.iInf_coe_ne_top.mp h
  obtain ⟨n, hn⟩ := ENat.exists_eq_iInf
    (fun n : {n : ℕ // SlideSequence G Q T n} => (n.val : ℕ∞))
  exact ⟨n.val, n.property, hn⟩

/-- Starting from an optimal matching, the route realization returns a sequence
of exactly that cost; hence reconstruction preserves optimization, not just
feasibility. -/
theorem Matching.realize_optimal {Q T : Finset V} (a : Matching Q T)
    (ha : a.distanceCost G = assignmentDistance G Q T)
    (hfin : a.distanceCost G ≠ ⊤) :
    ∃ n, SlideSequence G Q T n ∧ (n : ℕ∞) = a.distanceCost G := by
  obtain ⟨r, _, hr⟩ := a.routing_of_finite hfin
  obtain ⟨n, hn, hs⟩ := r.realize
  refine ⟨n, hs, le_antisymm ?_ ?_⟩
  · rw [← hr]
    exact_mod_cast hn
  · rw [ha, assignmentDistance_eq_slideDistance]
    exact iInf_le (fun n : {n : ℕ // SlideSequence G Q T n} => (n.val : ℕ∞)) ⟨n, hs⟩

theorem exists_optimal_assignment {Q T : Finset V}
    (h : assignmentDistance G Q T ≠ ⊤) :
    ∃ a : Matching Q T, a.distanceCost G = assignmentDistance G Q T := by
  cases isEmpty_or_nonempty (Matching Q T) with
  | inl hempty => simp [assignmentDistance] at h
  | inr hnonempty => exact ENat.exists_eq_iInf _

theorem assignmentDistance_eq_zero_iff (G : SimpleGraph V) (Q T : Finset V) :
    assignmentDistance G Q T = 0 ↔ Q = T := by
  constructor
  · intro h
    obtain ⟨n, hs, hn⟩ := exists_shortest_sequence (G := G) (Q := Q) (T := T)
      (by rw [h]; exact ENat.zero_ne_top)
    have hn0 : n = 0 := by exact_mod_cast hn.trans h
    subst n
    cases hs
    rfl
  · rintro rfl
    apply le_antisymm _ bot_le
    exact (iInf_le (fun a : Matching Q Q => a.distanceCost G)
      (Routing.identity G Q).toMatching).trans
        (by simpa using (Routing.identity G Q).distanceCost_le)

theorem assignmentDistance_eq_top_of_card_ne {Q T : Finset V}
    (h : Q.card ≠ T.card) : assignmentDistance G Q T = ⊤ := by
  apply (assignmentDistance_eq_top_iff G Q T).mpr
  rintro ⟨n, hs⟩
  exact h hs.card_eq.symm

@[simp] theorem assignmentDistance_self (G : SimpleGraph V) (Q : Finset V) :
    assignmentDistance G Q Q = 0 := by
  apply le_antisymm _ bot_le
  exact (iInf_le (fun a : Matching Q Q => a.distanceCost G)
    (Routing.identity G Q).toMatching).trans
      (by simpa using (Routing.identity G Q).distanceCost_le)

@[simp] theorem assignmentDistance_empty (G : SimpleGraph V) :
    assignmentDistance G (∅ : Finset V) ∅ = 0 := assignmentDistance_self G ∅

/-- Budgeted form of Lemma 3.1, with no finiteness hypotheses on the graph. -/
theorem matching_iff_slides_within {Q T : Finset V} {b : ℕ} :
    (∃ a : Matching Q T, a.distanceCost G ≤ b) ↔
      ∃ n ≤ b, SlideSequence G Q T n := by
  constructor
  · rintro ⟨a, ha⟩
    exact a.realize ha
  · rintro ⟨n, hn, hs⟩
    obtain ⟨r, hr⟩ := routing_of_slideSequence hs
    exact ⟨r.toMatching, r.distanceCost_le.trans (by exact_mod_cast (hr.symm ▸ hn))⟩

/-- Corollary 3.2: movement discovery is exactly a static independent assignment. -/
theorem discoveryWithin_iff_matching {S : Finset V} {b : ℕ} :
    DiscoveryWithin G S b ↔ ∃ T, Independent G T ∧
      ∃ a : Matching S T, a.distanceCost G ≤ b := by
  constructor
  · rintro ⟨T, n, hT, hs, hn⟩
    exact ⟨T, hT, matching_iff_slides_within.mpr ⟨n, hn, hs⟩⟩
  · rintro ⟨T, hT, ha⟩
    obtain ⟨n, hn, hs⟩ := matching_iff_slides_within.mp ha
    exact ⟨T, n, hT, hs, hn⟩

/-- The endpoint formulation directly as distinct destinations indexed by the
starting vertices. Graph distances retain `∞` for unreachable destinations. -/
theorem static_endpoint_formulation {S : Finset V} {b : ℕ} :
    DiscoveryWithin G S b ↔ ∃ f : V → V,
      Set.InjOn f (↑S : Set V) ∧ Independent G (S.image f) ∧
      (∑ s ∈ S, G.edist s (f s)) ≤ b := by
  rw [discoveryWithin_iff_matching]
  constructor
  · rintro ⟨T, hT, a, ha⟩
    exact ⟨a.target, a.injective, a.image_eq.symm ▸ hT, ha⟩
  · rintro ⟨f, hi, hT, hf⟩
    exact ⟨S.image f, hT, ⟨f, hi, rfl⟩, hf⟩

/-- The paper's `OPT(G,S)`: the extended-natural minimum over independent
terminal configurations and their actual collision-free slide distances. -/
noncomputable def discoveryDistance (G : SimpleGraph V) (S : Finset V) : ℕ∞ :=
  ⨅ T : {T : Finset V // Independent G T}, slideDistance G S T.val

/-- Corollary 3.2, equation (1), including the infinite optimum. The tuple is
indexed by starting vertices; its values outside `S` do not affect the cost. -/
theorem discoveryDistance_eq_staticEndpoint (G : SimpleGraph V) (S : Finset V) :
    discoveryDistance G S =
      ⨅ f : {f : V → V // Set.InjOn f (↑S : Set V) ∧ Independent G (S.image f)},
        ∑ s ∈ S, G.edist s (f.val s) := by
  apply le_antisymm
  · apply le_iInf
    intro f
    let a : Matching S (S.image f.val) := ⟨f.val, f.property.1, rfl⟩
    calc
      discoveryDistance G S ≤ slideDistance G S (S.image f.val) :=
        iInf_le (fun T : {T : Finset V // Independent G T} => slideDistance G S T.val)
          ⟨S.image f.val, f.property.2⟩
      _ = assignmentDistance G S (S.image f.val) :=
        (assignmentDistance_eq_slideDistance G S (S.image f.val)).symm
      _ ≤ a.distanceCost G := iInf_le _ a
      _ = _ := rfl
  · apply le_iInf
    intro T
    rw [← assignmentDistance_eq_slideDistance]
    apply le_iInf
    intro a
    let f : {f : V → V // Set.InjOn f (↑S : Set V) ∧ Independent G (S.image f)} :=
      ⟨a.target, a.injective, a.image_eq.symm ▸ T.property⟩
    exact iInf_le _ f

/-- Infinite discovery optimum means that no independent target is reachable. -/
theorem discoveryDistance_eq_top_iff (G : SimpleGraph V) (S : Finset V) :
    discoveryDistance G S = ⊤ ↔
      ¬ ∃ T n, Independent G T ∧ SlideSequence G S T n := by
  simp only [discoveryDistance, iInf_eq_top, slideDistance_eq_top_iff]
  constructor
  · intro h ⟨T, n, hT, hs⟩
    exact h ⟨T, hT⟩ ⟨n, hs⟩
  · intro h T ⟨n, hs⟩
    exact h ⟨T.val, n, T.property, hs⟩

end Movement
end IndependentSetDiscovery
