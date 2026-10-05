import IndependentSetDiscovery.Transversal.Independent
import IndependentSetDiscovery.Transversal.CheapPrefix
import IndependentSetDiscovery.Algorithms.PrefixSearch
import IndependentSetDiscovery.Weighted

/-!
# Closing the cheap-prefix algorithm's structural interfaces

These are concrete instances, not assumptions on an external transversal
oracle. The exact thresholds from the paper are retained for every rank ≥ 2.
-/
namespace IndependentSetDiscovery

open Finset

variable {ι V : Type*} [LinearOrder ι] [LinearOrder V] [Inhabited V]

/-- Executable sorted-prefix operations used by the deterministic recursion. -/
def costPrefixOperations : Algorithms.PrefixOperations V where
  takeCheap := cheapPrefix
  peak := prefixMax
  subset := cheapPrefix_subset
  card := card_cheapPrefix
  below_peak := fun c A v hv => cost_le_prefixMax c A hv
  outside := fun c A t v hc _ _ hv hv' =>
    cheapPrefix_max_le_outside c A t (fun u _ => hc u) hv hv'

/-- At ranks zero and one the paper handles the state directly. The harmless
constant extension below makes the uniform recursive interface positive at
all ranks and equals `M(d,r)` at every rank occurring in the main theorem. -/
def balancedSearchThreshold (d r : ℕ) : ℕ := balancedThreshold d (max 2 r)

theorem balancedThreshold_pos {d r : ℕ} (hd : 2 ≤ d) (hr : 2 ≤ r) :
    0 < balancedThreshold d r := by
  have hR : 0 < r - 1 := by omega
  unfold balancedThreshold
  positivity

theorem balancedSearchThreshold_pos {d : ℕ} (hd : 2 ≤ d) (r : ℕ) :
    0 < balancedSearchThreshold d r :=
  balancedThreshold_pos hd (le_max_left _ _)

theorem balancedSearchThreshold_eq {d r : ℕ} (hr : 2 ≤ r) :
    balancedSearchThreshold d r = balancedThreshold d r := by
  simp [balancedSearchThreshold, max_eq_right hr]

theorem balancedSearchThreshold_mono (d : ℕ) : Monotone (balancedSearchThreshold d) := by
  intro r r' h
  unfold balancedSearchThreshold balancedThreshold
  gcongr

/-- Extend representatives on the subtype of active labels to a total function;
values outside the active label set are irrelevant. -/
theorem extend_representatives (R : V → V → Prop) (L : Finset ι) (A : ι → Finset V)
    (h : ∃ y : ↥L → V, (∀ i, y i ∈ A i.1) ∧ Pairwise (fun i j => R (y i) (y j))) :
    ∃ x : ι → V, (∀ i ∈ L, x i ∈ A i) ∧
      (∀ i ∈ L, ∀ j ∈ L, i ≠ j → R (x i) (x j)) := by
  rcases h with ⟨y, hmem, hpair⟩
  let x : ι → V := fun i => if hi : i ∈ L then y ⟨i, hi⟩ else default
  refine ⟨x, ?_, ?_⟩
  · intro i hi
    simpa [x, hi] using hmem ⟨i, hi⟩
  · intro i hi j hj hij
    have hne : (⟨i, hi⟩ : ↥L) ≠ ⟨j, hj⟩ := fun h => hij (congrArg Subtype.val h)
    simpa [x, hi, hj] using hpair hne

/-- Every positive-size candidate list supplies the unique required choice at
rank one; no adjacency theorem is used for this terminal case. -/
theorem singleton_representatives (R : V → V → Prop) (L : Finset ι) (A : ι → Finset V)
    (hcard : L.card = 1) {t : ℕ} (ht : 0 < t)
    (hsize : ∀ i ∈ L, (A i).card = t) :
    ∃ x : ι → V, (∀ i ∈ L, x i ∈ A i) ∧
      (∀ i ∈ L, ∀ j ∈ L, i ≠ j → R (x i) (x j)) := by
  obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hcard
  have ha : 0 < (A i).card := by rw [hsize i (by simp)]; exact ht
  obtain ⟨v, hv⟩ := Finset.card_pos.mp ha
  refine ⟨fun _ => v, ?_, ?_⟩
  · intro j hj
    simpa using (show j = i from mem_singleton.mp hj) ▸ hv
  · intro j hj k hk hjk
    exact False.elim (hjk ((mem_singleton.mp hj).trans (mem_singleton.mp hk).symm))

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Concrete structural certificate for the exact balanced-biclique algorithm. -/
theorem balanced_transversalCertificate {d : ℕ} (hd : 2 ≤ d) (hG : BicliqueFree G d d) :
    Algorithms.TransversalCertificate (ι := ι) (Compatible G) (balancedSearchThreshold d) := by
  intro L A hL hsize
  by_cases hr : 2 ≤ L.card
  · apply extend_representatives (Compatible G) L A
    apply biclique_free_independent_representatives G hd hG (by simpa using hr)
    intro i
    simpa only [Fintype.card_coe, balancedSearchThreshold_eq hr] using hsize i.1 i.2
  · have hcard : L.card = 1 := by have := card_pos.mpr hL; omega
    exact singleton_representatives (Compatible G) L A hcard
      (balancedSearchThreshold_pos hd _) hsize

/-- The codegree threshold is positive even for ranks zero and one. -/
def codegreeSearchThreshold (s q r : ℕ) : ℕ := codegreeThreshold s q (r - 1)

theorem codegreeSearchThreshold_pos (s q r : ℕ) : 0 < codegreeSearchThreshold s q r :=
  codegreeThreshold_pos _ _ _

theorem codegreeSearchThreshold_mono (s q : ℕ) : Monotone (codegreeSearchThreshold s q) := by
  intro r r' h
  exact codegreeThreshold_mono s q (Nat.sub_le_sub_right h 1)

/-- Concrete structural certificate for every bounded-codegree instance. -/
theorem codegree_transversalCertificate {s q : ℕ} (hs : 1 ≤ s) (hG : CodegreeBound G s q) :
    Algorithms.TransversalCertificate (ι := ι) (Compatible G) (codegreeSearchThreshold s q) := by
  intro L A hL hsize
  by_cases hr : 2 ≤ L.card
  · apply extend_representatives (Compatible G) L A
    apply codegree_independent_representatives G hs hG (by simpa using hr)
    intro i
    simpa only [Fintype.card_coe, codegreeSearchThreshold] using hsize i.1 i.2
  · have hcard : L.card = 1 := by have := card_pos.mpr hL; omega
    exact singleton_representatives (Compatible G) L A hcard
      (codegreeSearchThreshold_pos _ _ _) hsize

/-- In particular, `K(s,t)`-freeness gives the advertised asymmetric criterion. -/
theorem unbalanced_transversalCertificate {s t : ℕ} (hs : 1 ≤ s) (ht : 0 < t)
    (hG : BicliqueFree G s t) :
    Algorithms.TransversalCertificate (ι := ι) (Compatible G) (codegreeSearchThreshold s (t - 1)) :=
  codegree_transversalCertificate G hs ((bicliqueFree_iff_codegreeBound G s t ht).mp hG)

end IndependentSetDiscovery
