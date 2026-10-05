import IndependentSetDiscovery.Algorithms.PrefixSearch

namespace IndependentSetDiscovery.Algorithms

/-- A structural transversal certificate is invariant under a bijective
renaming of labels, including its active-label subsets and their cardinality. -/
theorem reindex_certificate {ι κ V : Type*} [DecidableEq ι] [DecidableEq κ]
    (R : V → V → Prop) (threshold : ℕ → ℕ) (e : ι ≃ κ)
    (certificate : TransversalCertificate (ι := κ) R threshold) :
    TransversalCertificate (ι := ι) R threshold := by
  intro L A hL hA
  have hcard : (L.image e).card = L.card := Finset.card_image_of_injective L e.injective
  have hsize : ∀ j ∈ L.image e, (A (e.symm j)).card = threshold (L.image e).card := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    simpa [hcard] using hA i hi
  obtain ⟨y, hy, hp⟩ := certificate (L.image e) (fun j => A (e.symm j))
    (hL.image e) hsize
  refine ⟨fun i => y (e i), ?_, ?_⟩
  · intro i hi
    simpa using hy (e i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  · intro i hi j hj hij
    exact hp (e i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
      (e j) (Finset.mem_image.mpr ⟨j, hj, rfl⟩) (fun h => hij (e.injective h))

end IndependentSetDiscovery.Algorithms
