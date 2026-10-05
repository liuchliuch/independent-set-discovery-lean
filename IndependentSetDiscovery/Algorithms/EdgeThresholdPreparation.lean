import IndependentSetDiscovery.Algorithms.ThresholdPreparation
import IndependentSetDiscovery.Algorithms.BinarySearch

/-! # Counted exact integer square root and capped edge thresholds -/

namespace IndependentSetDiscovery.Algorithms.ThresholdPreparation

def squareRootPredicate (N q : ℕ) : Bool := decide (N ≤ q ^ 2)

/-- Binary integer-root search with an explicit counter for every tested square,
comparison, midpoint computation and recursive interval update. -/
def rootBisect (N : ℕ) : ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, lo, _ => (lo, 1)
  | fuel + 1, lo, hi =>
      let mid := (lo + hi) / 2
      let child := if squareRootPredicate N mid then rootBisect N fuel lo mid
        else rootBisect N fuel (mid + 1) hi
      (child.1, child.2 + 8)

theorem rootBisect_value (N fuel lo hi : ℕ) :
    (rootBisect N fuel lo hi).1 = bisect (squareRootPredicate N) fuel lo hi := by
  induction fuel generalizing lo hi with
  | zero => rfl
  | succ fuel ih => simp [rootBisect, bisect]; split <;> simp [ih]

theorem rootBisect_work (N fuel lo hi : ℕ) :
    (rootBisect N fuel lo hi).2 = 1 + 8 * fuel := by
  induction fuel generalizing lo hi with
  | zero => simp [rootBisect]
  | succ fuel ih => simp [rootBisect]; split <;> simp [ih] <;> omega

def measuredCeilSqrt (N : ℕ) : ℕ × ℕ :=
  let fuel := N.log2 + 1
  let result := rootBisect N fuel 0 N
  (result.1, result.2 + fuel + 4)

theorem measuredCeilSqrt_value (N : ℕ) : (measuredCeilSqrt N).1 = ceilSqrt N := by
  have hmono : ∀ a b, a ≤ b → squareRootPredicate N a = true →
      squareRootPredicate N b = true := by
    intro a b hab ha
    simp only [squareRootPredicate, decide_eq_true_eq] at ha ⊢
    exact ha.trans (Nat.pow_le_pow_left hab 2)
  have hupper : squareRootPredicate N N = true := by
    simp only [squareRootPredicate, decide_eq_true_eq]
    exact Nat.le_self_pow (by decide : 2 ≠ 0) N
  have hwidth : N - 0 < 2 ^ (N.log2 + 1) := by
    simpa [Nat.log2_eq_log_two] using Nat.lt_pow_succ_log_self (by decide : 1 < 2) N
  have hs := bisect_correct (squareRootPredicate N) hmono (N.log2 + 1) 0 N
    (Nat.zero_le _) hwidth hupper (by intro q hq; omega)
  change (rootBisect N (N.log2 + 1) 0 N).1 = _
  rw [rootBisect_value]
  apply Nat.le_antisymm
  · by_contra hle
    have hlt : ceilSqrt N < bisect (squareRootPredicate N) (N.log2 + 1) 0 N := by omega
    have hn := hs.2.1 (ceilSqrt N) hlt
    have hy : squareRootPredicate N (ceilSqrt N) = true := by
      simp only [squareRootPredicate, decide_eq_true_eq]
      exact le_ceilSqrt_sq N
    simp [hy] at hn
  · apply (ceilSqrt_le_iff N _).mpr
    simpa only [squareRootPredicate, decide_eq_true_eq] using hs.1

theorem measuredCeilSqrt_work (N : ℕ) :
    (measuredCeilSqrt N).2 = 9 * N.log2 + 14 := by
  simp [measuredCeilSqrt, rootBisect_work]
  omega

def edge (n m r : ℕ) : ℕ × ℕ :=
  let q := measuredCeilSqrt (16 * m * (r - 1))
  (min (n + 1) (8 * (r - 1) + q.1 + 1), q.2 + 12)

theorem edge_value (n m r : ℕ) :
    (edge n m r).1 = min (n + 1) (edgePrefixThreshold m r) := by
  simp [edge, measuredCeilSqrt_value, edgePrefixThreshold]

theorem edge_work (n m r : ℕ) : (edge n m r).2 ≤ 144 * m * r + 26 := by
  have hlog : (16 * m * (r - 1)).log2 ≤ 16 * m * (r - 1) := Nat.log2_le_self _
  have hmul := Nat.mul_le_mul_left (16 * m) (Nat.sub_le r 1)
  simp only [edge, measuredCeilSqrt_work]
  nlinarith

def edgeTable (k n m : ℕ) : Vector ℕ (k + 1) × ℕ := prepareTable k (edge n m)

theorem edgeTable_spec (k n m : ℕ) :
    (∀ r : Fin (k + 1), (edgeTable k n m).1[r] = min (n + 1) (edgePrefixThreshold m r)) ∧
      (edgeTable k n m).2 ≤ (k + 1) * (144 * m * k + 30) := by
  refine ⟨fun r => (prepareTable_get k _ r).trans (edge_value n m r), ?_⟩
  apply prepareTable_work k (144 * m * k + 26) (edge n m)
  intro r hr
  have hm := Nat.mul_le_mul_left (144 * m) hr
  exact (edge_work n m r).trans (by omega)

/-- An explicit graph-size polynomial, since an `n`-vertex graph has at most
`n²` edges. No square-root computation depends exponentially on the edge value. -/
theorem edgeTable_work_le_vertex_polynomial (k n m : ℕ) (hm : m ≤ n ^ 2) :
    (edgeTable k n m).2 ≤ (k + 1) * (144 * n ^ 2 * k + 30) := by
  apply (edgeTable_spec k n m).2.trans
  gcongr

end IndependentSetDiscovery.Algorithms.ThresholdPreparation
