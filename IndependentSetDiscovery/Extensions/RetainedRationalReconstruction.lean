import IndependentSetDiscovery.Extensions.RationalDiscoveryAlgorithm

/-! Reconstruction with an explicitly retained integer-weight implementation.
The function argument `z` is the stored matrix lookup in the final driver;
no common-denominator computation is embedded in an arc callback. -/
namespace IndependentSetDiscovery.WeightedDirected

open WeightedShortestPaths
variable {n : ℕ} [NeZero n]

/-- Generalized concrete bridge for a precomputed exact integerization. -/
def reconstructScaledPreparedSelection (a : ShortestPaths.MatrixGraph n)
    (D : Fin n → Fin n → Prop) [DecidableRel D] (w : Fin n → Fin n → ℚ)
    (z : Fin n → Fin n → ℕ) (denom : ℕ) (hdenom : 0 < denom)
    (hscale : ∀ u v, D u v → (z u v : ℚ) = denom*w u v)
    (S : Finset (Fin n))
    (P : PreparedRows D (fun u v => scalarizationBase S.card n*z u v+1))
    (x : S → Fin n)
    (hopt : (movementInstance a.graph D
      (fun u v => scalarizationBase S.card n*z u v+1) S).Optimal x) :
    RationalDiscoveryResult a.graph D w S := by
  let C := scalarizationBase S.card (Fintype.card (Fin n))
  let scalar := fun u v => C*z u v+1
  have Ps : PreparedRows D scalar := by simpa only [scalar, C, Fintype.card_fin] using P
  have hoptS : (movementInstance a.graph D scalar S).Optimal x := by
    simpa only [scalar, C, Fintype.card_fin] using hopt
  let cached := Ps.prepareSelectedPaths S x (fun s =>
    (movementInstance_mem a.graph D scalar S s (x s)).mp (hoptS.1.1 s))
  let paths := fun s : S =>
    (⟨(cached.paths s).val, by
      refine ⟨(cached.paths s).property.1, ?_⟩
      simpa only [Fintype.card_fin] using (cached.paths s).property.2⟩ :
      {p : DWalk D s.val (x s) // p.cost scalar = (distance D scalar s.val (x s)).toNat ∧
        p.length ≤ Fintype.card (Fin n)-1})
  let out := reconstructOptimalSelection (w := z) x hoptS paths
  let rationalOut := rationalizeDiscoveryResult hdenom hscale out
  exact { rationalOut with
    pathDecodingWork := cached.work
    pathDecodingWork_le := by simpa only [Fintype.card_fin] using cached.work_le }

end IndependentSetDiscovery.WeightedDirected
