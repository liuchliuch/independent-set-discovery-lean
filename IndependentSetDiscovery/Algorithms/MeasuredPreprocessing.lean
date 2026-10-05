import IndependentSetDiscovery.Algorithms.PrimitiveCosts
import IndependentSetDiscovery.Algorithms.Scaling

namespace IndependentSetDiscovery.Algorithms

local instance : Std.Commutative (fun a b : ℕ => a*b) := ⟨Nat.mul_comm⟩
local instance : Std.Associative (fun a b : ℕ => a*b) := ⟨Nat.mul_assoc⟩
local instance : Std.Commutative (fun a b : ℕ => a+b) := ⟨Nat.add_comm⟩
local instance : Std.Associative (fun a b : ℕ => a+b) := ⟨Nat.add_assoc⟩

theorem fold_mul_eq_prod (A : Finset α) (f : α → ℕ) :
    A.fold (fun a b : ℕ => a*b) 1 f = ∏ a ∈ A, f a := by
  simp [Finset.fold, Finset.prod, Multiset.prod_eq_foldl, Multiset.fold_eq_foldl]

theorem fold_add_eq_sum (A : Finset α) (f : α → ℕ) :
    A.fold (fun a b : ℕ => a+b) 0 f = ∑ a ∈ A, f a := by
  simp [Finset.fold, Finset.sum, Multiset.sum_eq_foldl, Multiset.fold_eq_foldl]

/-- One measured input-row pass to multiply its rational denominators. -/
def denominatorRowMeasured (c : Fin n → ℚ) (A : Finset (Fin n)) : ℕ × ℕ :=
  foldMapMeasured (fun v => ((c v).den, 1)) (· * ·) 1 A

/-- One measured input-row pass to find the largest scaled integer cost.
Six scalar instructions cover cost/field access, integer conversion, exact
division by the denominator, and integer multiplication. -/
def maximumRowMeasured (D : ℕ) (c : Fin n → ℚ) (A : Finset (Fin n)) : ℕ × ℕ :=
  foldMapMeasured (fun v => (scaleCost D (c v), 6)) max 0 A

theorem denominatorRowMeasured_value (c : Fin n → ℚ) (A : Finset (Fin n)) :
    (denominatorRowMeasured c A).1 = ∏ v ∈ A, (c v).den := by
  rw [denominatorRowMeasured, foldMapMeasured_value, fold_mul_eq_prod]

theorem maximumRowMeasured_value (D : ℕ) (c : Fin n → ℚ) (A : Finset (Fin n)) :
    (maximumRowMeasured D c A).1 = A.sup (fun v => scaleCost D (c v)) := by
  rw [maximumRowMeasured, foldMapMeasured_value]
  rfl

/-- Concrete preprocessing: product denominator, scaled row maxima, then sum.
Nested row programs run once per listed label, and their work is summed by
`foldMapMeasured`; input rows themselves are eagerly stored vectors. -/
def prepareMeasured (cost : Fin k → Fin n → ℚ) (L : Finset (Fin k))
    (rows : Vector (Finset (Fin n)) k) : (ℕ × ℕ) × ℕ :=
  let denom := foldMapMeasured (fun i =>
    let row := denominatorRowMeasured (cost i) (rows[i])
    (row.1, row.2+1)) (· * ·) 1 L
  let upper := foldMapMeasured (fun i =>
    let row := maximumRowMeasured denom.1 (cost i) (rows[i])
    (row.1, row.2+1)) (· + ·) 0 L
  ((denom.1, upper.1), denom.2+upper.2)

theorem prepareMeasured_value (cost : Fin k → Fin n → ℚ) (L : Finset (Fin k))
    (rows : Vector (Finset (Fin n)) k) :
    (prepareMeasured cost L rows).1 =
      (commonDenominator L (fun i => rows[i]) cost,
        upperBudget L (fun i => rows[i]) (scaledCosts L (fun i => rows[i]) cost)) := by
  unfold prepareMeasured
  simp only [foldMapMeasured_value, denominatorRowMeasured_value, maximumRowMeasured_value,
    fold_mul_eq_prod, fold_add_eq_sum]
  rfl

theorem denominatorRowMeasured_cost (c : Fin n → ℚ) (A : Finset (Fin n)) :
    (denominatorRowMeasured c A).2 ≤ 4*n^2+3*n := by
  have hh := foldMapMeasured_cost (fun v => ((c v).den, 1)) (· * ·) 1 A 1 (by simp)
  have hc : A.card ≤ n := by simpa using Finset.card_le_univ A
  change _ ≤ _ at hh
  have hs := Nat.pow_le_pow_left hc 2
  dsimp only [denominatorRowMeasured]
  nlinarith

theorem maximumRowMeasured_cost (D : ℕ) (c : Fin n → ℚ) (A : Finset (Fin n)) :
    (maximumRowMeasured D c A).2 ≤ 4*n^2+8*n := by
  have hh := foldMapMeasured_cost (fun v => (scaleCost D (c v), 6)) max 0 A 6 (by simp)
  have hc : A.card ≤ n := by simpa using Finset.card_le_univ A
  have hs := Nat.pow_le_pow_left hc 2
  dsimp only [maximumRowMeasured]
  nlinarith

/-- Universal polynomial preprocessing bound, derived from the measured folds. -/
theorem prepareMeasured_cost (cost : Fin k → Fin n → ℚ) (L : Finset (Fin k))
    (rows : Vector (Finset (Fin n)) k) :
    (prepareMeasured cost L rows).2 ≤ 32*(k+1)^2*(n+1)^2 := by
  let denom := foldMapMeasured (fun i =>
    let row := denominatorRowMeasured (cost i) (rows[i])
    (row.1, row.2+1)) (· * ·) 1 L
  have hd := foldMapMeasured_cost (fun i =>
    let row := denominatorRowMeasured (cost i) (rows[i])
    (row.1, row.2+1)) (· * ·) 1 L (4*n^2+8*n+1) (by
      intro i hi; have := denominatorRowMeasured_cost (cost i) (rows[i]); dsimp only; omega)
  have hu := foldMapMeasured_cost (fun i =>
    let row := maximumRowMeasured denom.1 (cost i) (rows[i])
    (row.1, row.2+1)) (· + ·) 0 L (4*n^2+8*n+1) (by
      intro i hi; have := maximumRowMeasured_cost denom.1 (cost i) (rows[i]); dsimp only; omega)
  have hl : L.card ≤ k := by simpa using Finset.card_le_univ L
  have hl2 := Nat.pow_le_pow_left hl 2
  have hmul := Nat.mul_le_mul_right (4*n^2+8*n+1) hl
  change denom.2 + _ ≤ _
  change denom.2 ≤ _ at hd
  nlinarith [Nat.zero_le (k*n), Nat.zero_le (k^2*n), Nat.zero_le (k*n^2), Nat.zero_le (k^2*n^2)]

end IndependentSetDiscovery.Algorithms
