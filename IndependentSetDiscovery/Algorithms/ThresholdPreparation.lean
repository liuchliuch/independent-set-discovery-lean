import IndependentSetDiscovery.Transversal.Certificates
import IndependentSetDiscovery.Extensions.Arithmetic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Bounded, counted preparation of structural thresholds

Only thresholds up to `n+1` can affect an `n`-vertex instance. Saturating
arithmetic prevents large parameter values from creating huge intermediate
integers. Exponentiation stops after at most `n+1` multiplications, even when
the exponent parameter is much larger. Bases zero and one are handled directly.
-/

namespace IndependentSetDiscovery.Algorithms
namespace ThresholdPreparation

def capAdd (cap x y : ℕ) : ℕ := min cap (min cap x + min cap y)
def capMul (cap x y : ℕ) : ℕ := min cap (min cap x * min cap y)

@[simp] theorem cap_add_left (cap x y : ℕ) :
    min cap (min cap x + y) = min cap (x + y) := by omega

@[simp] theorem cap_add_right (cap x y : ℕ) :
    min cap (x + min cap y) = min cap (x + y) := by omega

@[simp] theorem cap_mul_left (cap x y : ℕ) :
    min cap (min cap x * y) = min cap (x * y) := by
  cases y with
  | zero => simp
  | succ y =>
    rw [min_mul, ← min_assoc]
    have h : cap ≤ cap * (y + 1) := by nlinarith
    rw [min_eq_left h]

@[simp] theorem cap_mul_right (cap x y : ℕ) :
    min cap (x * min cap y) = min cap (x * y) := by
  simpa only [Nat.mul_comm] using cap_mul_left cap y x

@[simp] theorem capAdd_value (cap x y : ℕ) : capAdd cap x y = min cap (x+y) := by
  simp [capAdd]

@[simp] theorem capMul_value (cap x y : ℕ) : capMul cap x y = min cap (x*y) := by
  simp [capMul]

/-- Repeated saturated multiplication, with a concrete six-operation charge
for each iteration (bounded minima, multiplication and loop control). -/
def powLoop (cap base : ℕ) : ℕ → ℕ × ℕ
  | 0 => (min cap 1, 1)
  | exponent + 1 =>
    let p := powLoop cap base exponent
    (capMul cap p.1 base, p.2 + 6)

theorem powLoop_value (cap base exponent : ℕ) :
    (powLoop cap base exponent).1 = min cap (base ^ exponent) := by
  induction exponent with
  | zero => simp [powLoop]
  | succ exponent ih => simp [powLoop, ih, pow_succ]

theorem powLoop_work (cap base exponent : ℕ) :
    (powLoop cap base exponent).2 = 1 + 6 * exponent := by
  induction exponent with
  | zero => simp [powLoop]
  | succ exponent ih => simp [powLoop, ih]; omega

theorem pow_truncate (cap base exponent : ℕ) (hb : 2 ≤ base) :
    min cap (base ^ min exponent cap) = min cap (base ^ exponent) := by
  by_cases he : exponent ≤ cap
  · rw [min_eq_left he]
  · have hc : cap ≤ exponent := by omega
    have hp : cap ≤ base ^ cap :=
      (Nat.lt_two_pow_self.le).trans (Nat.pow_le_pow_left hb cap)
    have hp' : cap ≤ base ^ exponent := hp.trans (Nat.pow_le_pow_right (by omega) hc)
    rw [min_eq_right hc, min_eq_left hp, min_eq_left hp']

/-- At most `cap` multiplications; all stored intermediate results are ≤cap. -/
def cappedPow (cap base exponent : ℕ) : ℕ × ℕ :=
  if base = 0 then (min cap (if exponent = 0 then 1 else 0), 4)
  else if base = 1 then (min cap 1, 3)
  else
    let p := powLoop cap base (min exponent cap)
    (p.1, p.2 + 4)

theorem cappedPow_value (cap base exponent : ℕ) :
    (cappedPow cap base exponent).1 = min cap (base ^ exponent) := by
  unfold cappedPow
  split_ifs with hb0 he hb1
  · subst base; subst exponent; simp
  · subst base; simp [he]
  · subst base; simp
  · exact (powLoop_value _ _ _).trans (pow_truncate _ _ _ (by omega))

theorem cappedPow_work (cap base exponent : ℕ) :
    (cappedPow cap base exponent).2 ≤ 6 * cap + 5 := by
  unfold cappedPow
  split_ifs <;> simp only [powLoop_work] <;> omega

theorem cappedPow_result_le (cap base exponent : ℕ) :
    (cappedPow cap base exponent).1 ≤ cap := by rw [cappedPow_value]; exact min_le_left _ _

theorem powLoop_product_le (cap x base : ℕ) : min cap x * min cap base ≤ cap ^ 2 := by
  simpa [pow_two] using Nat.mul_le_mul (min_le_left cap x) (min_le_left cap base)

/-- Capped balanced threshold, computed without forming a large power. -/
def balanced (n d r : ℕ) : ℕ × ℕ :=
  let cap := n + 1
  let R := max 2 r - 1
  let p := cappedPow cap (4 * R) d
  let q := cappedPow cap d 2
  (capAdd cap (capMul cap (d-1) p.1) (capMul cap (capMul cap 4 q.1) R),
    p.2 + q.2 + 24)

theorem balanced_value (n d r : ℕ) :
    (balanced n d r).1 = min (n+1) (balancedSearchThreshold d r) := by
  simp [balanced, cappedPow_value, balancedSearchThreshold, balancedThreshold]

theorem balanced_work (n d r : ℕ) : (balanced n d r).2 ≤ 12 * (n+1) + 34 := by
  have hp := cappedPow_work (n+1) (4*(max 2 r-1)) d
  have hq := cappedPow_work (n+1) d 2
  dsimp only [balanced]
  omega

def codegree (n s q r : ℕ) : ℕ × ℕ :=
  let cap := n + 1
  let R := r - 1
  let p := cappedPow cap (8 * R) s
  (capAdd cap (capAdd cap (capMul cap q p.1) (capMul cap (capMul cap 8 s) R)) 1,
    p.2 + 32)

theorem codegree_value (n s q r : ℕ) :
    (codegree n s q r).1 = min (n+1) (codegreeSearchThreshold s q r) := by
  simp [codegree, cappedPow_value, codegreeSearchThreshold, codegreeThreshold]

theorem codegree_work (n s q r : ℕ) : (codegree n s q r).2 ≤ 6 * (n+1) + 37 := by
  have hp := cappedPow_work (n+1) (8*(r-1)) s
  dsimp only [codegree]
  omega

def degeneracy (n a r : ℕ) : ℕ × ℕ :=
  let cap := n + 1
  (capAdd cap (capMul cap (capMul cap 4 (r-1)) (capAdd cap (capMul cap 4 a) 1)) 1, 32)

theorem degeneracy_value (n a r : ℕ) :
    (degeneracy n a r).1 = min (n+1) (degeneracyPrefixThreshold a r) := by
  simp only [degeneracy, capAdd_value, capMul_value, cap_mul_left, cap_mul_right,
    cap_add_left, cap_add_right, degeneracyPrefixThreshold]

/-- Materialize each relevant rank once and aggregate the returned costs. -/
def prepareTable (k : ℕ) (prepare : ℕ → ℕ × ℕ) : Vector ℕ (k+1) × ℕ :=
  let entries := Vector.ofFn fun r : Fin (k+1) => prepare r.val
  (entries.map Prod.fst, 4 * (k+1) + (entries.toList.map Prod.snd).sum)

@[simp] theorem prepareTable_get (k : ℕ) (prepare : ℕ → ℕ × ℕ) (r : Fin (k+1)) :
    (prepareTable k prepare).1[r] = (prepare r.val).1 := by simp [prepareTable]

theorem prepareTable_work (k bound : ℕ) (prepare : ℕ → ℕ × ℕ)
    (h : ∀ r ≤ k, (prepare r).2 ≤ bound) :
    (prepareTable k prepare).2 ≤ (k+1) * (bound+4) := by
  have hs := Finset.sum_le_sum (s := Finset.univ)
    (fun r _ => h (r : Fin (k+1)).val (by omega))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  simp only [prepareTable, Vector.toList_ofFn, List.map_ofFn, List.sum_ofFn, Function.comp_def]
  nlinarith

def balancedTable (k n d : ℕ) : Vector ℕ (k+1) × ℕ := prepareTable k (balanced n d)
def codegreeTable (k n s q : ℕ) : Vector ℕ (k+1) × ℕ := prepareTable k (codegree n s q)
def degeneracyTable (k n a : ℕ) : Vector ℕ (k+1) × ℕ := prepareTable k (degeneracy n a)

theorem balancedTable_spec (k n d : ℕ) :
    (∀ r : Fin (k+1), (balancedTable k n d).1[r] = min (n+1) (balancedSearchThreshold d r)) ∧
      (balancedTable k n d).2 ≤ (k+1) * (12*(n+1)+38) := by
  refine ⟨fun r => ?_, ?_⟩
  · exact (prepareTable_get k _ r).trans (balanced_value n d r.val)
  · exact prepareTable_work k _ _ (fun r _ => balanced_work n d r)

theorem codegreeTable_spec (k n s q : ℕ) :
    (∀ r : Fin (k+1), (codegreeTable k n s q).1[r] = min (n+1) (codegreeSearchThreshold s q r)) ∧
      (codegreeTable k n s q).2 ≤ (k+1) * (6*(n+1)+41) := by
  refine ⟨fun r => ?_, ?_⟩
  · exact (prepareTable_get k _ r).trans (codegree_value n s q r.val)
  · exact prepareTable_work k _ _ (fun r _ => codegree_work n s q r)

theorem degeneracyTable_spec (k n a : ℕ) :
    (∀ r : Fin (k+1), (degeneracyTable k n a).1[r] = min (n+1) (degeneracyPrefixThreshold a r)) ∧
      (degeneracyTable k n a).2 ≤ 36*(k+1) := by
  refine ⟨fun r => ?_, ?_⟩
  · exact (prepareTable_get k _ r).trans (degeneracy_value n a r.val)
  · simpa [Nat.mul_comm] using prepareTable_work k 32 (degeneracy n a) (by intro r hr; rfl)

end ThresholdPreparation
end IndependentSetDiscovery.Algorithms
