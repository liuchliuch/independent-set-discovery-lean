import IndependentSetDiscovery.Algorithms.PrefixSearch
import IndependentSetDiscovery.Algorithms.Witness
import IndependentSetDiscovery.Algorithms.BinarySearch
import IndependentSetDiscovery.Algorithms.Scaling

namespace IndependentSetDiscovery.Algorithms

variable {ι V : Type*} [LinearOrder ι] [LinearOrder V] [Inhabited V]
variable (R : V → V → Prop) [DecidableRel R] (cost : ι → V → ℚ)
variable (ops : PrefixOperations V) (threshold : ℕ → ℕ)

/-- Budget-independent feasibility for an overlapping weighted transversal. -/
def Selection (L : Finset ι) (A : ι → Finset V) (x : ι → V) : Prop :=
  (∀ i ∈ L, x i ∈ A i) ∧ (∀ i ∈ L, ∀ j ∈ L, i ≠ j → R (x i) (x j))

def MinimumSelection (L : Finset ι) (A : ι → Finset V) (x : ι → V) : Prop :=
  Selection R L A x ∧ ∀ y, Selection R L A y →
    (∑ i ∈ L, cost i (x i)) ≤ ∑ i ∈ L, cost i (y i)

def budgetState (L : Finset ι) (A : ι → Finset V) (B : ℚ) : State ι V := ⟨L, A, B⟩

/-- Exact rational optimization: denominator clearing, binary search, then self-reduction. -/
def optimize (L : Finset ι) (A : ι → Finset V) : Option (ι → V) :=
  let D := commonDenominator L A cost
  let U := upperBudget L A (scaledCosts L A cost)
  let oracle := decidePrefix R cost ops threshold
  let p := fun b : ℕ => oracle (budgetState L A ((b : ℚ) / D))
  match leastBudget p U with
  | none => none
  | some b => (recover R cost oracle L.card (budgetState L A ((b : ℚ) / D))).1

theorem feasible_budgetState_mono (L : Finset ι) (A : ι → Finset V)
    (B B' : ℚ) (hle : B ≤ B') :
    Feasible R cost (budgetState L A B) → Feasible R cost (budgetState L A B') := by
  rintro ⟨x, hmem, hpair, hbudget⟩
  exact ⟨x, hmem, hpair, hbudget.trans hle⟩

theorem scaled_selection_feasible (nonneg : ∀ i v, 0 ≤ cost i v)
    (L : Finset ι) (A : ι → Finset V) (x : ι → V) (hx : Selection R L A x) :
    Feasible R cost (budgetState L A
      (((∑ i ∈ L, scaledCosts L A cost i (x i) : ℕ) : ℚ) / commonDenominator L A cost)) := by
  refine ⟨x, hx.1, hx.2, ?_⟩
  have hD : (0 : ℚ) < commonDenominator L A cost := by
    exact_mod_cast commonDenominator_pos L A cost
  have heq := scaled_sum L A cost nonneg x hx.1
  change (∑ i ∈ L, cost i (x i)) ≤ _
  rw [heq]
  exact le_of_eq (by field_simp; rfl)

theorem feasible_upper_of_selection (nonneg : ∀ i v, 0 ≤ cost i v)
    (L : Finset ι) (A : ι → Finset V) (x : ι → V) (hx : Selection R L A x) :
    Feasible R cost (budgetState L A
      ((upperBudget L A (scaledCosts L A cost) : ℚ) / commonDenominator L A cost)) := by
  apply feasible_budgetState_mono R cost L A _ _ _
    (scaled_selection_feasible R cost nonneg L A x hx)
  apply div_le_div_of_nonneg_right
  · exact_mod_cast selection_le_upperBudget L A (scaledCosts L A cost) x hx.1
  · positivity

/-- Every existing feasible selection is optimized, with the actual returned assignment. -/
theorem optimize_complete
    (symm : Symmetric R) (nonneg : ∀ i v, 0 ≤ cost i v)
    (positive : ∀ r, 0 < threshold r)
    (certificate : TransversalCertificate (ι := ι) R threshold)
    (L : Finset ι) (A : ι → Finset V)
    (hex : ∃ x, Selection R L A x) :
    ∃ x, optimize R cost ops threshold L A = some x ∧ MinimumSelection R cost L A x := by
  let D := commonDenominator L A cost
  let U := upperBudget L A (scaledCosts L A cost)
  let oracle := decidePrefix R cost ops threshold
  let p := fun b : ℕ => oracle (budgetState L A ((b : ℚ) / D))
  have hD : (0 : ℚ) < D := by exact_mod_cast commonDenominator_pos L A cost
  have horacle : ∀ s, oracle s = true ↔ Feasible R cost s :=
    decidePrefix_correct R cost ops threshold symm nonneg positive certificate
  have hmono : ∀ a b, a ≤ b → p a = true → p b = true := by
    intro a b hab hpa
    apply (horacle _).mpr
    apply feasible_budgetState_mono R cost L A _ _ _ ((horacle _).mp hpa)
    exact div_le_div_of_nonneg_right (by exact_mod_cast hab) hD.le
  have hu : p U = true := by
    rcases hex with ⟨x, hx⟩
    exact (horacle _).mpr (feasible_upper_of_selection R cost nonneg L A x hx)
  rcases leastBudget_some_spec p U hmono hu with ⟨b, hb, hpb, hleast, hbu⟩
  have hfeasible := (horacle _).mp hpb
  rcases recover_correct R cost symm nonneg oracle (fun s _ => horacle s) L.card
      (budgetState L A ((b : ℚ) / D)) (le_refl _) hfeasible with ⟨x, hrecover, hx⟩
  refine ⟨x, ?_, ⟨hx.1, hx.2.1⟩, ?_⟩
  · change (match leastBudget p U with
      | none => none
      | some b => (recover R cost oracle L.card (budgetState L A ((b : ℚ) / D))).1) = some x
    rw [hb]
    exact hrecover
  · intro y hy
    let m := ∑ i ∈ L, scaledCosts L A cost i (y i)
    have hm : p m = true := (horacle _).mpr (scaled_selection_feasible R cost nonneg L A y hy)
    have hbm : b ≤ m := by
      by_contra h
      have := hleast m (by omega)
      simp_all
    have hs := scaled_sum L A cost nonneg y hy.1
    have hdivide : (m : ℚ) / D = ∑ i ∈ L, cost i (y i) := by
      change ((∑ i ∈ L, scaledCosts L A cost i (y i) : ℕ) : ℚ) / D = _
      rw [hs]
      have hDne : (D : ℚ) ≠ 0 := ne_of_gt hD
      change ((D : ℚ) * _) / D = _
      field_simp
    calc
      (∑ i ∈ L, cost i (x i)) ≤ (b : ℚ) / D := hx.2.2
      _ ≤ (m : ℚ) / D := div_le_div_of_nonneg_right (by exact_mod_cast hbm) hD.le
      _ = ∑ i ∈ L, cost i (y i) := hdivide

/-- On infeasible inputs the explicit upper-budget test rejects before self-reduction. -/
theorem optimize_none_of_infeasible
    (symm : Symmetric R) (nonneg : ∀ i v, 0 ≤ cost i v)
    (positive : ∀ r, 0 < threshold r)
    (certificate : TransversalCertificate (ι := ι) R threshold)
    (L : Finset ι) (A : ι → Finset V) (hno : ¬∃ x, Selection R L A x) :
    optimize R cost ops threshold L A = none := by
  have hfalse : decidePrefix R cost ops threshold
      (budgetState L A ((upperBudget L A (scaledCosts L A cost) : ℚ) /
        commonDenominator L A cost)) = false := by
    by_contra h
    have ht : decidePrefix R cost ops threshold
        (budgetState L A ((upperBudget L A (scaledCosts L A cost) : ℚ) /
          commonDenominator L A cost)) = true := Bool.eq_true_of_not_eq_false h
    rcases (decidePrefix_correct R cost ops threshold symm nonneg positive certificate _).mp ht with ⟨x, hx⟩
    exact hno ⟨x, hx.1, hx.2.1⟩
  simp [optimize, leastBudget, hfalse]

theorem optimize_none_iff
    (symm : Symmetric R) (nonneg : ∀ i v, 0 ≤ cost i v)
    (positive : ∀ r, 0 < threshold r)
    (certificate : TransversalCertificate (ι := ι) R threshold)
    (L : Finset ι) (A : ι → Finset V) :
    optimize R cost ops threshold L A = none ↔ ¬∃ x, Selection R L A x := by
  constructor
  · intro hn hex
    rcases optimize_complete R cost ops threshold symm nonneg positive certificate L A hex with ⟨x, hx, _⟩
    simp [hn] at hx
  · exact optimize_none_of_infeasible R cost ops threshold symm nonneg positive certificate L A

theorem optimize_some_spec
    (symm : Symmetric R) (nonneg : ∀ i v, 0 ≤ cost i v)
    (positive : ∀ r, 0 < threshold r)
    (certificate : TransversalCertificate (ι := ι) R threshold)
    (L : Finset ι) (A : ι → Finset V) (x : ι → V)
    (hx : optimize R cost ops threshold L A = some x) : MinimumSelection R cost L A x := by
  have hex : ∃ y, Selection R L A y := by
    by_contra hn
    have := optimize_none_of_infeasible R cost ops threshold symm nonneg positive certificate L A hn
    simp [this] at hx
  rcases optimize_complete R cost ops threshold symm nonneg positive certificate L A hex with ⟨y, hy, hmin⟩
  have : y = x := Option.some.inj (hy.symm.trans hx)
  simpa [this] using hmin

end IndependentSetDiscovery.Algorithms
