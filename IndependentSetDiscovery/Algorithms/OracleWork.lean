import IndependentSetDiscovery.Algorithms.Optimization
import IndependentSetDiscovery.Algorithms.BitComplexity

/-!
# Compositional oracle-call and oracle-work counters

The counters follow the actual branch choices of binary search and witness
self-reduction. They account for each evaluated oracle call, including failed
probes. The value projection of `optimizeCounted` is the original optimizer.
-/
namespace IndependentSetDiscovery.Algorithms

/-- The actual work charged to the sequential probes made by `firstYes`. -/
def firstYesWork (p : α → Bool) (work : α → ℕ) : List α → ℕ
  | [] => 0
  | a :: as => work a + if p a then 0 else firstYesWork p work as

theorem firstYesWork_le (p : α → Bool) (work : α → ℕ) (C : ℕ) :
    ∀ as, (∀ a ∈ as, work a ≤ C) →
      firstYesWork p work as ≤ (firstYes p as).2 * C := by
  intro as
  induction as with
  | nil => simp [firstYesWork, firstYes]
  | cons a as ih =>
    intro h
    have ha := h a (by simp)
    have ht := ih (fun b hb => h b (by simp [hb]))
    cases hp : p a <;> simp [firstYesWork, firstYes, hp] <;> nlinarith

/-- The exact work of binary search, following the same queried midpoints. -/
def bisectWork (p : ℕ → Bool) (work : ℕ → ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | fuel + 1, lo, hi =>
    let mid := (lo + hi) / 2
    work mid + if p mid then bisectWork p work fuel lo mid
      else bisectWork p work fuel (mid + 1) hi

theorem bisectWork_le (p : ℕ → Bool) (work : ℕ → ℕ) (C : ℕ)
    (hwork : ∀ n, work n ≤ C) :
    ∀ fuel lo hi, bisectWork p work fuel lo hi ≤ fuel * C := by
  intro fuel
  induction fuel with
  | zero => simp [bisectWork]
  | succ fuel ih =>
    intro lo hi
    simp only [bisectWork]
    split
    · have h := ih lo ((lo + hi) / 2)
      have h' := hwork ((lo + hi) / 2)
      nlinarith
    · have h := ih ((lo + hi) / 2 + 1) hi
      have h' := hwork ((lo + hi) / 2)
      nlinarith

/-- Binary search with its exact decision-call count. -/
def leastBudgetCounted (p : ℕ → Bool) (upper : ℕ) : Option ℕ × ℕ :=
  if p upper then
    (some (bisect p (Nat.log2 upper + 1) 0 upper),
      1 + bisectCalls p (Nat.log2 upper + 1) 0 upper)
  else (none, 1)

@[simp] theorem leastBudgetCounted_value (p : ℕ → Bool) (upper : ℕ) :
    (leastBudgetCounted p upper).1 = leastBudget p upper := by
  unfold leastBudgetCounted leastBudget
  split <;> rfl

theorem leastBudgetCounted_calls (p : ℕ → Bool) (upper : ℕ) :
    (leastBudgetCounted p upper).2 ≤ optimizationCalls upper := by
  unfold leastBudgetCounted
  split <;> simp [bisectCalls_eq, optimizationCalls] <;> omega

/-- Oracle work of the initial upper-endpoint test and the actual search. -/
def leastBudgetWork (p : ℕ → Bool) (work : ℕ → ℕ) (upper : ℕ) : ℕ :=
  work upper + if p upper then bisectWork p work (Nat.log2 upper + 1) 0 upper else 0

theorem leastBudgetWork_le (p : ℕ → Bool) (work : ℕ → ℕ) (C : ℕ)
    (hwork : ∀ n, work n ≤ C) (upper : ℕ) :
    leastBudgetWork p work upper ≤ optimizationCalls upper * C := by
  unfold leastBudgetWork optimizationCalls
  have hu := hwork upper
  have hb := bisectWork_le p work C hwork (Nat.log2 upper + 1) 0 upper
  split <;> nlinarith

variable {ι V : Type*} [LinearOrder ι] [LinearOrder V] [Inhabited V]
variable (R : V → V → Prop) [DecidableRel R] (cost : ι → V → ℚ)

/-- Work of exactly the oracle calls performed during self-reduction. -/
def recoverWork (oracle : State ι V → Bool) (work : State ι V → ℕ) : ℕ → State ι V → ℕ
  | 0, _ => 0
  | fuel + 1, s =>
    if h : s.labels.Nonempty then
      let i := s.labels.min' h
      let choices := (s.candidates i).sort (· ≤ ·)
      let p := fun v => oracle (child R cost s i v)
      let charged := firstYesWork p (fun v => work (child R cost s i v)) choices
      match (firstYes p choices).1 with
      | none => charged
      | some v => charged + recoverWork oracle work fuel (child R cost s i v)
    else 0

/-- Any invariant closed under child formation can be used to transport a
uniform bound on one oracle invocation to the entire witness extraction. -/
theorem recoverWork_le_calls (oracle : State ι V → Bool) (work : State ι V → ℕ)
    (P : State ι V → Prop) (C : ℕ)
    (hchild : ∀ s, P s → ∀ i ∈ s.labels, ∀ v, P (child R cost s i v))
    (hwork : ∀ s, P s → work s ≤ C) :
    ∀ fuel s, P s → recoverWork R cost oracle work fuel s ≤ (recover R cost oracle fuel s).2 * C := by
  intro fuel
  induction fuel with
  | zero => intro s hs; simp [recoverWork]
  | succ fuel ih =>
    intro s hs
    by_cases h : s.labels.Nonempty
    · let i := s.labels.min' h
      have hi : i ∈ s.labels := s.labels.min'_mem h
      have hprobe := firstYesWork_le (fun v => oracle (child R cost s i v))
        (fun v => work (child R cost s i v)) C ((s.candidates i).sort (· ≤ ·))
        (fun v _ => hwork _ (hchild s hs i hi v))
      simp only [recoverWork, recover, dif_pos h]
      change (match (firstYes (fun v => oracle (child R cost s i v))
          ((s.candidates i).sort (· ≤ ·))).1 with
        | none => _
        | some v => _) ≤ _
      cases hp : (firstYes (fun v => oracle (child R cost s i v))
        ((s.candidates i).sort (· ≤ ·))).1 with
      | none => simpa only [hp] using hprobe
      | some v =>
          have ht := ih (child R cost s i v) (hchild s hs i hi v)
          simp only [hp]
          nlinarith
    · simp [recoverWork, recover, h]

theorem recoverWork_le_candidates (oracle : State ι V → Bool) (work : State ι V → ℕ)
    (P : State ι V → Prop) (C : ℕ)
    (hchild : ∀ s, P s → ∀ i ∈ s.labels, ∀ v, P (child R cost s i v))
    (hwork : ∀ s, P s → work s ≤ C) (fuel : ℕ) (s : State ι V) (hs : P s) :
    recoverWork R cost oracle work fuel s ≤ totalCandidates s * C :=
  (recoverWork_le_calls R cost oracle work P C hchild hwork fuel s hs).trans
    (Nat.mul_le_mul_right C (recover_calls_le R cost oracle fuel s))

variable (ops : PrefixOperations V) (threshold : ℕ → ℕ)

/-- The executable optimizer together with its actual decision-oracle count. -/
def optimizeCounted (L : Finset ι) (A : ι → Finset V) : Option (ι → V) × ℕ :=
  let D := commonDenominator L A cost
  let U := upperBudget L A (scaledCosts L A cost)
  let oracle := decidePrefix R cost ops threshold
  let p := fun b : ℕ => oracle (budgetState L A ((b : ℚ) / D))
  let search := leastBudgetCounted p U
  match search.1 with
  | none => (none, search.2)
  | some b =>
      let result := recover R cost oracle L.card (budgetState L A ((b : ℚ) / D))
      (result.1, search.2 + result.2)

@[simp] theorem optimizeCounted_value (L : Finset ι) (A : ι → Finset V) :
    (optimizeCounted R cost ops threshold L A).1 = optimize R cost ops threshold L A := by
  unfold optimizeCounted optimize
  simp only [leastBudgetCounted_value]
  split <;> simp_all only [Prod.fst]

theorem optimizeCounted_calls (L : Finset ι) (A : ι → Finset V) :
    (optimizeCounted R cost ops threshold L A).2 ≤
      optimizationCalls (upperBudget L A (scaledCosts L A cost)) +
        ∑ i ∈ L, (A i).card := by
  let D := commonDenominator L A cost
  let U := upperBudget L A (scaledCosts L A cost)
  let oracle := decidePrefix R cost ops threshold
  let p := fun b : ℕ => oracle (budgetState L A ((b : ℚ) / D))
  have hsearch := leastBudgetCounted_calls p U
  change (match (leastBudgetCounted p U).1 with
    | none => (none, (leastBudgetCounted p U).2)
    | some b => ((recover R cost oracle L.card (budgetState L A ((b : ℚ) / D))).1,
      (leastBudgetCounted p U).2 + (recover R cost oracle L.card (budgetState L A ((b : ℚ) / D))).2)).2 ≤
      optimizationCalls U + ∑ i ∈ L, (A i).card
  split
  · exact hsearch.trans (Nat.le_add_right _ _)
  · rename_i b hb
    have hr := recover_calls_le R cost oracle L.card (budgetState L A ((b : ℚ) / D))
    change _ ≤ ∑ i ∈ L, (A i).card at hr
    omega

/-- The complete optimization call count is linear in input numeric bits plus
the number of listed candidates. -/
theorem optimizeCounted_calls_numeric (L : Finset ι) (A : ι → Finset V) :
    (optimizeCounted R cost ops threshold L A).2 ≤
      3 * numericSize L A cost + 2 + ∑ i ∈ L, (A i).card :=
  (optimizeCounted_calls R cost ops threshold L A).trans
    (Nat.add_le_add_right (optimizationCalls_le_numericSize L A cost) _)

/-- Composed work of the exact oracle calls of the optimizer. -/
def optimizeOracleWork (work : State ι V → ℕ) (L : Finset ι) (A : ι → Finset V) : ℕ :=
  let D := commonDenominator L A cost
  let U := upperBudget L A (scaledCosts L A cost)
  let oracle := decidePrefix R cost ops threshold
  let p := fun b : ℕ => oracle (budgetState L A ((b : ℚ) / D))
  leastBudgetWork p (fun b => work (budgetState L A ((b : ℚ) / D))) U +
    match leastBudget p U with
    | none => 0
    | some b => recoverWork R cost oracle work L.card (budgetState L A ((b : ℚ) / D))

theorem optimizeOracleWork_le (work : State ι V → ℕ) (L : Finset ι) (A : ι → Finset V)
    (P : State ι V → Prop) (C : ℕ)
    (hbudget : ∀ B, P (budgetState L A B))
    (hchild : ∀ s, P s → ∀ i ∈ s.labels, ∀ v, P (child R cost s i v))
    (hwork : ∀ s, P s → work s ≤ C) :
    optimizeOracleWork R cost ops threshold work L A ≤
      (optimizationCalls (upperBudget L A (scaledCosts L A cost)) +
        ∑ i ∈ L, (A i).card) * C := by
  let D := commonDenominator L A cost
  let U := upperBudget L A (scaledCosts L A cost)
  let oracle := decidePrefix R cost ops threshold
  let p := fun b : ℕ => oracle (budgetState L A ((b : ℚ) / D))
  have hsearch := leastBudgetWork_le p
    (fun b => work (budgetState L A ((b : ℚ) / D))) C
    (fun b => hwork _ (hbudget _)) U
  change leastBudgetWork p (fun b => work (budgetState L A ((b : ℚ) / D))) U +
    (match leastBudget p U with
    | none => 0
    | some b => recoverWork R cost oracle work L.card (budgetState L A ((b : ℚ) / D))) ≤
      (optimizationCalls U + ∑ i ∈ L, (A i).card) * C
  split
  · simp only [Nat.add_zero]
    exact hsearch.trans (Nat.mul_le_mul_right C (Nat.le_add_right _ _))
  · rename_i b hb
    have hr := recoverWork_le_candidates R cost oracle work P C hchild hwork
      L.card (budgetState L A ((b : ℚ) / D)) (hbudget _)
    change _ ≤ (∑ i ∈ L, (A i).card) * C at hr
    nlinarith

end IndependentSetDiscovery.Algorithms
