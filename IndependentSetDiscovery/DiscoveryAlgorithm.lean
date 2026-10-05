import IndependentSetDiscovery.Algorithms.ComputedMovement
import IndependentSetDiscovery.Algorithms.EncodedMovement
import IndependentSetDiscovery.Algorithms.WeightedSolver
import IndependentSetDiscovery.Algorithms.PathDecoder
import IndependentSetDiscovery.Movement.ReconstructionBridge
import IndependentSetDiscovery.Movement.CachedPaths

/-! # Executable discovery algorithm

The graph is a finite Boolean adjacency matrix. Every successful result contains
an actual optimal collision-free slide list. The biclique promise is used only
in erased correctness proofs, never as an algorithmic oracle.
-/

namespace IndependentSetDiscovery

open ShortestPaths ComputedMovement Movement

variable {n : ℕ} [NeZero n]

/-- Generic executable transfer, with a proved structural certificate used
only for correctness. The threshold itself is executable input data. -/
def solveDiscoveryWithThreshold (a : MatrixGraph n) (S : Finset (Fin n))
    (threshold : ℕ → ℕ) (positive : ∀ r, 0 < threshold r)
    (certificate : Algorithms.TransversalCertificate (ι := S)
      (Compatible a.graph) threshold) : Option (DiscoveryResult a.graph S) := by
  match hx : EncodedMovement.solveEncodedWithThreshold a S threshold with
  | none => exact none
  | some x =>
    have hopt := EncodedMovement.solveEncodedWithThreshold_some a S positive certificate hx
    let paths := cachedSelectedPaths a.graph S x hopt.1
    exact some (reconstructOptimalSelection x hopt paths)

theorem solveDiscoveryWithThreshold_none_iff (a : MatrixGraph n)
    (S : Finset (Fin n)) (threshold : ℕ → ℕ)
    (positive : ∀ r, 0 < threshold r)
    (certificate : Algorithms.TransversalCertificate (ι := S)
      (Compatible a.graph) threshold) :
    solveDiscoveryWithThreshold a S threshold positive certificate = none ↔
      ¬ ∃ T m, Independent a.graph T ∧ SlideSequence a.graph S T m := by
  unfold solveDiscoveryWithThreshold
  split <;> rename_i hx
  · have h := (EncodedMovement.solveEncodedWithThreshold_none_iff a S positive certificate).mp hx
    simp only [true_iff]
    exact (no_selection_iff_unreachable a.graph S).mp h
  · simp only [Option.some_ne_none, false_iff, not_not]
    have hopt := EncodedMovement.solveEncodedWithThreshold_some a S positive certificate hx
    by_contra hnone
    exact ((no_selection_iff_unreachable a.graph S).mpr hnone) ⟨_, hopt.1⟩

def solveDiscovery (a : MatrixGraph n) (S : Finset (Fin n)) (d : ℕ)
    (hd : 2 ≤ d) (hG : BicliqueFree a.graph d d) :
    Option (DiscoveryResult a.graph S) := by
  match hx : EncodedMovement.solveEncoded a S d with
  | none => exact none
  | some x =>
    have hopt := EncodedMovement.solveEncoded_some a S hd hG hx
    let paths := cachedSelectedPaths a.graph S x hopt.1
    exact some (reconstructOptimalSelection x hopt paths)

theorem solveDiscovery_none_iff (a : MatrixGraph n) (S : Finset (Fin n))
    (d : ℕ) (hd : 2 ≤ d) (hG : BicliqueFree a.graph d d) :
    solveDiscovery a S d hd hG = none ↔
      ¬ ∃ T m, Independent a.graph T ∧ SlideSequence a.graph S T m := by
  unfold solveDiscovery
  split <;> rename_i hx
  · have h := (EncodedMovement.solveEncoded_none_iff a S hd hG).mp hx
    simp only [true_iff]
    exact (no_selection_iff_unreachable a.graph S).mp h
  · simp only [Option.some_ne_none, false_iff, not_not]
    have hopt := EncodedMovement.solveEncoded_some a S hd hG hx
    by_contra hnone
    exact ((no_selection_iff_unreachable a.graph S).mpr hnone) ⟨_, hopt.1⟩

/-- The binary-budget decision version compares the computed optimum with the
supplied natural budget, without using that budget as a search-depth bound. -/
def decideDiscovery (a : MatrixGraph n) (S : Finset (Fin n)) (d : ℕ)
    (hd : 2 ≤ d) (hG : BicliqueFree a.graph d d) (budget : ℕ) : Bool :=
  match solveDiscovery a S d hd hG with
  | none => false
  | some out => decide (out.moves.length ≤ budget)

theorem decideDiscovery_correct (a : MatrixGraph n) (S : Finset (Fin n))
    (d : ℕ) (hd : 2 ≤ d) (hG : BicliqueFree a.graph d d) (budget : ℕ) :
    decideDiscovery a S d hd hG budget = true ↔ DiscoveryWithin a.graph S budget := by
  unfold decideDiscovery
  split <;> rename_i h
  · simp only [Bool.false_eq_true, false_iff]
    intro hdsc
    obtain ⟨T, m, hT, hs, _⟩ := hdsc
    exact ((solveDiscovery_none_iff a S d hd hG).mp h) ⟨T, m, hT, hs⟩
  · rename_i out
    simp only [decide_eq_true_eq]
    constructor
    · intro hb
      exact ⟨out.target, out.moves.length, out.independent, out.valid.slideSequence, hb⟩
    · rintro ⟨T, m, hT, hs, hb⟩
      exact (out.optimal T m hT hs).trans hb

end IndependentSetDiscovery
