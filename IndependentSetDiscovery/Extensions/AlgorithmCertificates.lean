import IndependentSetDiscovery.Extensions.Certificates
import IndependentSetDiscovery.Algorithms.PrefixSearch

/-! # Active-label certificates consumed by the executable prefix search -/

namespace IndependentSetDiscovery

variable {ι V : Type*} [LinearOrder ι] [LinearOrder V] [Fintype V] [Inhabited V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem edgeCount_transversalCertificate :
    Algorithms.TransversalCertificate (ι := ι)
      (fun u v : V => u ≠ v ∧ ¬ G.Adj u v)
      (edgePrefixThreshold G.edgeFinset.card) := by
  intro L A hL hsize
  have hs : ∀ i : L, (A i.val).card =
      edgePrefixThreshold G.edgeFinset.card (Fintype.card L) := by
    intro i
    simpa using hsize i.val i.property
  obtain ⟨x, hx, hp⟩ := independent_representatives_of_edge_count G
    (fun i : L => A i.val) hs
  let y : ι → V := fun i => if hi : i ∈ L then x ⟨i, hi⟩ else default
  refine ⟨y, ?_, ?_⟩
  · intro i hi
    simpa only [y, dif_pos hi] using hx ⟨i, hi⟩
  · intro i hi j hj hij
    have hn : (⟨i, hi⟩ : L) ≠ ⟨j, hj⟩ := by
      intro h
      exact hij (congrArg Subtype.val h)
    simpa only [y, dif_pos hi, dif_pos hj] using hp hn

theorem degeneracy_transversalCertificate {a : ℕ} (hG : Degenerate G a) :
    Algorithms.TransversalCertificate (ι := ι)
      (fun u v : V => u ≠ v ∧ ¬ G.Adj u v)
      (degeneracyPrefixThreshold a) := by
  intro L A hL hsize
  have hs : ∀ i : L, (A i.val).card =
      degeneracyPrefixThreshold a (Fintype.card L) := by
    intro i
    simpa using hsize i.val i.property
  obtain ⟨x, hx, hp⟩ := independent_representatives_of_degeneracy G hG
    (fun i : L => A i.val) hs
  let y : ι → V := fun i => if hi : i ∈ L then x ⟨i, hi⟩ else default
  refine ⟨y, ?_, ?_⟩
  · intro i hi
    simpa only [y, dif_pos hi] using hx ⟨i, hi⟩
  · intro i hi j hj hij
    have hn : (⟨i, hi⟩ : L) ≠ ⟨j, hj⟩ := by
      intro h
      exact hij (congrArg Subtype.val h)
    simpa only [y, dif_pos hi, dif_pos hj] using hp hn

end IndependentSetDiscovery
