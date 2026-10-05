import IndependentSetDiscovery.Algorithms.ComputedMovement
import IndependentSetDiscovery.Algorithms.CacheAccounting
import IndependentSetDiscovery.Movement.ReconstructionBridge

/-!
# Polynomial preprocessing and reconstruction stages

These are bounds for the concrete shortest-path and reconstruction counters.
The main search's measured finite-table implementation is accounted separately;
no arbitrary decision oracle or generic prefix-operation tariff is asserted
to have unit cost here. This file provides the polynomial stages needed when
assembling the final uniform FPT bound.
-/

namespace IndependentSetDiscovery
namespace DiscoveryComplexity

open ShortestPaths ComputedMovement Movement

theorem power_envelope (n i j : ℕ) (hij : i ≤ j) : n ^ i ≤ (n + 1) ^ j :=
  (Nat.pow_le_pow_left (Nat.le_succ n) i).trans
    (Nat.pow_le_pow_right (by omega) hij)

/-- Cost of exactly the `n` source rows materialized by `allRows`. -/
def preprocessingWork {n : ℕ} (a : MatrixGraph n) : ℕ :=
  n + ∑ s : Fin n, (shortestPaths a.graph s).2

theorem shortestPaths_quartic {n : ℕ} (a : MatrixGraph n) (s : Fin n) :
    (shortestPaths a.graph s).2 ≤ 28 * (n + 1) ^ 4 := by
  have h := shortestPaths_cost a.graph s
  have h1 := power_envelope n 1 4 (by omega)
  have h2 := power_envelope n 2 4 (by omega)
  have h3 := power_envelope n 3 4 (by omega)
  have h4 := power_envelope n 4 4 (by omega)
  simp only [pow_one] at h1
  omega

theorem preprocessingWork_le {n : ℕ} (a : MatrixGraph n) :
    preprocessingWork a ≤ 29 * (n + 1) ^ 5 := by
  have hs := Finset.sum_le_sum (s := Finset.univ)
    (fun s _ => shortestPaths_quartic a s)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  have h1 := power_envelope n 1 5 (by omega)
  simp only [pow_one] at h1
  have hm : n * (n + 1) ^ 4 ≤ (n + 1) ^ 5 := by
    calc
      _ ≤ (n + 1) * (n + 1) ^ 4 := Nat.mul_le_mul_right _ (Nat.le_succ n)
      _ = _ := (pow_succ' (n + 1) 4).symm
  unfold preprocessingWork
  nlinarith

theorem walkOption_quartic {n : ℕ} (a : MatrixGraph n) (s v : Fin n) :
    (walkOption a.graph s v).2 ≤ 41 * (n + 1) ^ 4 := by
  have h := walkOption_cost a.graph s v
  have h0 : 1 ≤ (n + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
  have h1 := power_envelope n 1 4 (by omega)
  have h2 := power_envelope n 2 4 (by omega)
  have h3 := power_envelope n 3 4 (by omega)
  have h4 := power_envelope n 4 4 (by omega)
  simp only [pow_one] at h1
  omega

theorem selectedPathsSourceWork_polynomial {n : ℕ} (a : MatrixGraph n)
    (S : Finset (Fin n)) (x : S → Fin n) :
    selectedPathsSourceWork a.graph S x ≤ 44 * (n + 1) ^ 5 := by
  have hk : S.card ≤ n := by simpa using Finset.card_le_univ S
  have hs := Finset.sum_le_sum (s := Finset.univ)
    (fun s _ => walkOption_quartic a s.val (x s))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul] at hs
  have hm : S.card * (n + 1)^4 ≤ (n + 1)^5 := by
    calc
      _ ≤ (n + 1) * (n + 1)^4 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' (n + 1) 4).symm
  have hquad : n * (S.card + 2) ≤ 3 * (n + 1)^2 := by nlinarith
  have hpower : (n + 1)^2 ≤ (n + 1)^5 := Nat.pow_le_pow_right (by omega) (by omega)
  unfold selectedPathsSourceWork
  nlinarith

/-- The reconstruction result carries the cost of its actual eager plan-table
implementation, including materialization after every update. -/
theorem reconstructionWork_polynomial {n : ℕ} {G : SimpleGraph (Fin n)}
    {S : Finset (Fin n)} (out : DiscoveryResult G S) :
    out.reconstructionWork ≤ 64 * (n + 1) ^ 5 := by
  have hk : S.card ≤ n := by simpa using Finset.card_le_univ S
  have hM : S.card * (n - 1) ≤ n^2 := by
    simpa [pow_two] using Nat.mul_le_mul hk (Nat.sub_le n 1)
  have hA : S.card * (n - 1) + 1 ≤ (n + 1)^2 := by nlinarith
  have hB : n + S.card * (n - 1) + 1 ≤ (n + 1)^2 := by nlinarith
  have h := out.work_le
  simp only [Fintype.card_fin, reconstructionStepBudget] at h
  calc
    _ ≤ (S.card * (n - 1) + 1) * (64 * (n + 1) *
        (n + S.card * (n - 1) + 1)) := h
    _ ≤ (n + 1)^2 * (64 * (n + 1) * (n + 1)^2) := by gcongr
    _ = 64 * (n + 1)^5 := by ring

/-- Sum of the concrete non-search stages for a successful selected solution. -/
def successfulAuxiliaryWork {n : ℕ} (a : MatrixGraph n) (S : Finset (Fin n))
    (x : S → Fin n) (hx : (movementInstance a.graph S).Optimal x) : ℕ :=
  preprocessingWork a + selectedPathsSourceWork a.graph S x +
    (reconstructOptimalSelection x hx (cachedSelectedPaths a.graph S x hx.1)).reconstructionWork

theorem successfulAuxiliaryWork_le {n : ℕ} (a : MatrixGraph n) (S : Finset (Fin n))
    (x : S → Fin n) (hx : (movementInstance a.graph S).Optimal x) :
    successfulAuxiliaryWork a S x hx ≤ 137 * (n + 1)^5 := by
  have hp := preprocessingWork_le a
  have hs := selectedPathsSourceWork_polynomial a S x
  have hr := reconstructionWork_polynomial
    (reconstructOptimalSelection x hx (cachedSelectedPaths a.graph S x hx.1))
  unfold successfulAuxiliaryWork
  omega

/-- Polynomial matrix expansion preserves the requested sparse-input form. -/
theorem successfulAuxiliaryWork_edge_form {n : ℕ} (a : MatrixGraph n)
    (S : Finset (Fin n)) (x : S → Fin n)
    (hx : (movementInstance a.graph S).Optimal x) (m : ℕ) :
    successfulAuxiliaryWork a S x hx ≤ 137 * (n + m + 1)^5 :=
  (successfulAuxiliaryWork_le a S x hx).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 5))

end DiscoveryComplexity
end IndependentSetDiscovery
