import IndependentSetDiscovery.Algorithms.Optimization
import IndependentSetDiscovery.Transversal.Certificates

/-!
# The weighted transversal algorithm (Theorem 4.4)

These entrypoints are executable. Structural hypotheses occur only in the
correctness theorems; they are not an oracle passed to the implementation.
-/
namespace IndependentSetDiscovery

open Algorithms

variable {ι V : Type*} [Fintype ι] [LinearOrder ι]
  [Fintype V] [LinearOrder V] [Inhabited V]

namespace WeightedInstance

variable (I : WeightedInstance ι V) [DecidableRel I.graph.Adj]

def solveWithThreshold (threshold : ℕ → ℕ) : Option (ι → V) :=
  Algorithms.optimize (Compatible I.graph) I.normalizedCost costPrefixOperations threshold
    Finset.univ I.candidates

def decideWithThreshold (threshold : ℕ → ℕ) (B : ℚ) : Bool :=
  Algorithms.decidePrefix (Compatible I.graph) I.normalizedCost costPrefixOperations threshold
    (Algorithms.budgetState Finset.univ I.candidates B)

theorem algorithmsSelection_iff (x : ι → V) :
    Algorithms.Selection (Compatible I.graph) Finset.univ I.candidates x ↔ I.Selection x := by
  rw [I.selection_iff_compatible]
  simp [Algorithms.Selection]

theorem algorithmsMinimum_iff (x : ι → V) :
    Algorithms.MinimumSelection (Compatible I.graph) I.normalizedCost Finset.univ I.candidates x ↔
      I.Optimal x := by
  constructor
  · rintro ⟨hx, hmin⟩
    have hx' := (I.algorithmsSelection_iff x).mp hx
    refine ⟨hx', ?_⟩
    intro y hy
    have hm := hmin y ((I.algorithmsSelection_iff y).mpr hy)
    simpa [I.sum_normalizedCost hx', I.sum_normalizedCost hy] using hm
  · rintro ⟨hx, hmin⟩
    refine ⟨(I.algorithmsSelection_iff x).mpr hx, ?_⟩
    intro y hy
    have hy' := (I.algorithmsSelection_iff y).mp hy
    simpa [I.sum_normalizedCost hx, I.sum_normalizedCost hy'] using hmin y hy'

theorem solveWithThreshold_some {threshold : ℕ → ℕ}
    (positive : ∀ r, 0 < threshold r)
    (certificate : Algorithms.TransversalCertificate (ι := ι) (Compatible I.graph) threshold)
    {x : ι → V} (hx : I.solveWithThreshold threshold = some x) : I.Optimal x := by
  apply (I.algorithmsMinimum_iff x).mp
  exact Algorithms.optimize_some_spec (Compatible I.graph) I.normalizedCost
    costPrefixOperations threshold (compatible_symm I.graph) I.normalizedCost_nonneg
    positive certificate Finset.univ I.candidates x hx

theorem solveWithThreshold_none_iff {threshold : ℕ → ℕ}
    (positive : ∀ r, 0 < threshold r)
    (certificate : Algorithms.TransversalCertificate (ι := ι) (Compatible I.graph) threshold) :
    I.solveWithThreshold threshold = none ↔ ¬∃ x, I.Selection x := by
  rw [solveWithThreshold, Algorithms.optimize_none_iff _ _ _ _
    (compatible_symm I.graph) I.normalizedCost_nonneg positive certificate]
  simp only [I.algorithmsSelection_iff]

theorem decideWithThreshold_correct {threshold : ℕ → ℕ}
    (positive : ∀ r, 0 < threshold r)
    (certificate : Algorithms.TransversalCertificate (ι := ι) (Compatible I.graph) threshold)
    (B : ℚ) : I.decideWithThreshold threshold B = true ↔ I.Within B := by
  rw [decideWithThreshold, Algorithms.decidePrefix_correct _ _ _ _
    (compatible_symm I.graph) I.normalizedCost_nonneg positive certificate]
  constructor
  · rintro ⟨x, hx, hp, hc⟩
    have hs : I.Selection x := (I.algorithmsSelection_iff x).mp ⟨hx, hp⟩
    exact ⟨x, hs, by simpa [Algorithms.budgetState, I.sum_normalizedCost hs] using hc⟩
  · rintro ⟨x, hx, hc⟩
    have hs := (I.algorithmsSelection_iff x).mpr hx
    exact ⟨x, hs.1, hs.2, by simpa [Algorithms.budgetState, I.sum_normalizedCost hx] using hc⟩

/-- Concrete biclique-free optimizer. No promise-checking or nonconstructive choice runs. -/
def solveBicliqueFree (d : ℕ) : Option (ι → V) :=
  I.solveWithThreshold (balancedSearchThreshold d)

def decideBicliqueFree (d : ℕ) (B : ℚ) : Bool :=
  I.decideWithThreshold (balancedSearchThreshold d) B

/-- Theorem 4.4, exact optimization and a returned witness. -/
theorem solveBicliqueFree_some {d : ℕ} (hd : 2 ≤ d) (hG : BicliqueFree I.graph d d)
    {x : ι → V} (hx : I.solveBicliqueFree d = some x) : I.Optimal x :=
  I.solveWithThreshold_some (balancedSearchThreshold_pos hd)
    (balanced_transversalCertificate I.graph hd hG) hx

/-- Theorem 4.4, exact certification of nonexistence. -/
theorem solveBicliqueFree_none_iff {d : ℕ} (hd : 2 ≤ d) (hG : BicliqueFree I.graph d d) :
    I.solveBicliqueFree d = none ↔ ¬∃ x, I.Selection x :=
  I.solveWithThreshold_none_iff (balancedSearchThreshold_pos hd)
    (balanced_transversalCertificate I.graph hd hG)

theorem decideBicliqueFree_correct {d : ℕ} (hd : 2 ≤ d) (hG : BicliqueFree I.graph d d)
    (B : ℚ) : I.decideBicliqueFree d B = true ↔ I.Within B :=
  I.decideWithThreshold_correct (balancedSearchThreshold_pos hd)
    (balanced_transversalCertificate I.graph hd hG) B

/-- Exact state-expansion counter of the concrete decision implementation. -/
def decisionNodes (d : ℕ) (B : ℚ) : ℕ :=
  (Algorithms.run
    (Algorithms.prefixStep (Compatible I.graph) I.normalizedCost costPrefixOperations
      (balancedSearchThreshold d)) (Fintype.card ι)
    (Algorithms.budgetState Finset.univ I.candidates B)).2

theorem decisionNodes_le {d : ℕ} (hd : 2 ≤ d) (hk : 2 ≤ Fintype.card ι)
    (hG : BicliqueFree I.graph d d) (B : ℚ) :
    I.decisionNodes d B ≤
      2 * (Fintype.card ι * balancedThreshold d (Fintype.card ι)) ^ Fintype.card ι := by
  have hcost := Algorithms.decidePrefix_cost_le
    (Compatible I.graph) I.normalizedCost costPrefixOperations (balancedSearchThreshold d)
    (compatible_symm I.graph) I.normalizedCost_nonneg (balancedSearchThreshold_pos hd)
    (balanced_transversalCertificate I.graph hd hG)
    (Fintype.card ι) (balancedThreshold d (Fintype.card ι))
    (fun r hr => by
      have hm := balancedSearchThreshold_mono d hr
      simpa [balancedSearchThreshold_eq hk] using hm)
    (Algorithms.budgetState Finset.univ I.candidates B) (by simp [Algorithms.budgetState])
  have hbranch : 2 ≤ Fintype.card ι * balancedThreshold d (Fintype.card ι) := by
    have ht := balancedThreshold_pos hd hk
    nlinarith
  have htree := Algorithms.treeBound_add_one_le
    (Fintype.card ι * balancedThreshold d (Fintype.card ι)) (Fintype.card ι) hbranch
  simp only [Algorithms.budgetState, Finset.card_univ] at hcost
  exact le_trans hcost (by omega)

end WeightedInstance
end IndependentSetDiscovery
