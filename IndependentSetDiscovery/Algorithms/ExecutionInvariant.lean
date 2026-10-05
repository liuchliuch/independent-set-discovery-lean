import IndependentSetDiscovery.Algorithms.RationalArithmeticBits
import IndependentSetDiscovery.Algorithms.OracleWork
import IndependentSetDiscovery.Transversal.Certificates

/-!
# Arithmetic invariants of the actual optimization execution

The traces below follow precisely the branch choices of `run`, `firstYes`,
`recover`, and `bisect`. The residual invariant records a subset of distinct
assigned original labels, their original candidates, and the exact rational
budget. It applies to rejected negative-budget children as well as successful
ones: no feasibility or nonnegative residual-budget hypothesis is used.
-/
namespace IndependentSetDiscovery.Algorithms

open Finset

variable {ι V : Type*} [LinearOrder ι] [LinearOrder V] [Inhabited V]

/-- Every assigned label occurs once, and all remaining candidates still come
from the original input. `B` is the initial rational query budget. -/
def ResidualInvariant (cost : ι → V → ℚ) (L : Finset ι)
    (A : ι → Finset V) (B : ℚ) (s : State ι V) : Prop :=
  ∃ (K : Finset ι) (x : ι → V), K ⊆ L ∧ s.labels = L \ K ∧
    (∀ i, s.candidates i ⊆ A i) ∧ (∀ i ∈ K, x i ∈ A i) ∧
    s.budget = B - ∑ i ∈ K, cost i (x i)

variable (R : V → V → Prop) [DecidableRel R] (cost : ι → V → ℚ)

 theorem residualInvariant_initial (L : Finset ι) (A : ι → Finset V) (B : ℚ) :
    ResidualInvariant cost L A B (budgetState L A B) := by
  refine ⟨∅, fun _ => default, by simp, ?_, ?_, by simp, ?_⟩ <;>
    simp [budgetState]

 theorem ResidualInvariant.labels_subset {L : Finset ι} {A : ι → Finset V}
    {B : ℚ} {s : State ι V} (hs : ResidualInvariant cost L A B s) : s.labels ⊆ L := by
  rcases hs with ⟨K, x, hK, hlabels, hA, hx, hb⟩
  rw [hlabels]
  exact Finset.sdiff_subset

 theorem ResidualInvariant.candidates_subset {L : Finset ι} {A : ι → Finset V}
    {B : ℚ} {s : State ι V} (hs : ResidualInvariant cost L A B s) :
    ∀ i, s.candidates i ⊆ A i := by
  obtain ⟨K, x, hK, hlabels, hA, hx, hb⟩ := hs
  exact hA

 theorem ResidualInvariant.child {L : Finset ι} {A : ι → Finset V}
    {B : ℚ} {s : State ι V} (hs : ResidualInvariant cost L A B s)
    (i : ι) (hi : i ∈ s.labels) (v : V) (hv : v ∈ s.candidates i) :
    ResidualInvariant cost L A B (child R cost s i v) := by
  rcases hs with ⟨K, x, hK, hlabels, hA, hx, hb⟩
  have hiL : i ∈ L := (Finset.mem_sdiff.mp (hlabels ▸ hi)).1
  have hiK : i ∉ K := (Finset.mem_sdiff.mp (hlabels ▸ hi)).2
  refine ⟨insert i K, Function.update x i v, Finset.insert_subset hiL hK, ?_, ?_, ?_, ?_⟩
  · change s.labels.erase i = L \ insert i K
    rw [hlabels]
    ext j
    simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_insert]
    tauto
  · intro j u hu
    exact hA j (Finset.mem_filter.mp hu).1
  · intro j hj
    rcases Finset.mem_insert.mp hj with hji | hj
    · subst j; simpa using hA i hv
    · rw [Function.update_of_ne (show j ≠ i from fun he => hiK (he ▸ hj))]
      exact hx j hj
  · change s.budget - cost i v = B - ∑ j ∈ insert i K, cost j (Function.update x i v j)
    rw [Finset.sum_insert hiK, Function.update_self, hb]
    have heq : (∑ j ∈ K, cost j (Function.update x i v j)) = ∑ j ∈ K, cost j (x j) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Function.update_of_ne (show j ≠ i from fun he => hiK (he ▸ hj))]
    rw [heq]
    ring

variable (ops : PrefixOperations V) (threshold : ℕ → ℕ)

/-- Every child actually emitted by the deterministic step chooses an active
label and a current candidate, including the small-label case. -/
theorem prefixStep_child_origin (s : State ι V) (children : List (State ι V))
    (hstep : prefixStep R cost ops threshold s = .branch children)
    (t : State ι V) (ht : t ∈ children) :
    ∃ i ∈ s.labels, ∃ v ∈ s.candidates i, t = child R cost s i v := by
  unfold prefixStep at hstep
  split_ifs at hstep with hb he hs ha
  · injection hstep with hc
    subst children
    rcases List.mem_map.mp ht with ⟨v, hv, rfl⟩
    exact ⟨_, (Finset.mem_filter.mp ((smallLabels threshold s).min'_mem hs)).1,
      v, by simpa using hv, rfl⟩
  · injection hstep with hc
    subst children
    rcases (mem_allPrefixBranches R cost ops threshold s t).mp ht with ⟨i, hi, v, hv, h⟩
    exact ⟨i, hi, v, ops.subset _ _ _ hv, h⟩

theorem ResidualInvariant.prefixStep {L : Finset ι} {A : ι → Finset V}
    {B : ℚ} {s : State ι V} (hs : ResidualInvariant cost L A B s)
    (children : List (State ι V))
    (hstep : prefixStep R cost ops threshold s = .branch children) :
    ∀ t ∈ children, ResidualInvariant cost L A B t := by
  intro t ht
  rcases prefixStep_child_origin R cost ops threshold s children hstep t ht with
    ⟨i, hi, v, hv, rfl⟩
  exact hs.child R cost i hi v hv

/-- Exact preorder of state expansions performed by `run`. Even at zero fuel
`run` evaluates the current step, so the root is always recorded. -/
def runTrace (step : σ → Instruction σ) : ℕ → σ → List σ
  | 0, s => [s]
  | fuel + 1, s => s :: match step s with
    | .yes => []
    | .no => []
    | .branch children => children.flatMap (runTrace step fuel)

theorem runTrace_length (step : σ → Instruction σ) : ∀ fuel s,
    (runTrace step fuel s).length = (run step fuel s).2 := by
  intro fuel
  induction fuel with
  | zero => intro s; cases h : step s <;> simp [runTrace, run, h]
  | succ fuel ih =>
    intro s
    cases h : step s <;> simp [runTrace, run, h, List.length_flatMap, ih, Nat.add_comm, Function.comp_def]

theorem runTrace_invariant (step : σ → Instruction σ) (P : σ → Prop)
    (hchild : ∀ s, P s → ∀ children, step s = .branch children → ∀ t ∈ children, P t) :
    ∀ fuel s, P s → ∀ t ∈ runTrace step fuel s, P t := by
  intro fuel
  induction fuel with
  | zero =>
    intro s hs t ht
    have ht : t = s := by simpa [runTrace] using ht
    simpa [ht] using hs
  | succ fuel ih =>
    intro s hs t ht
    simp only [runTrace, List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact hs
    · cases h : step s with
      | yes => simp [h] at ht
      | no => simp [h] at ht
      | branch children =>
        simp only [h, List.mem_flatMap] at ht
        rcases ht with ⟨u, hu, ht⟩
        exact ih u (hchild s hs children h u hu) t ht

theorem residualInvariant_runTrace {L : Finset ι} {A : ι → Finset V}
    {B : ℚ} {s : State ι V} (hs : ResidualInvariant cost L A B s)
    (fuel : ℕ) : ∀ t ∈ runTrace (prefixStep R cost ops threshold) fuel s,
      ResidualInvariant cost L A B t :=
  runTrace_invariant _ _ (fun _ h => h.prefixStep R cost ops threshold) fuel s hs

/-- The normalized representation bound holds on every actual recursive state,
without assuming its budget is nonnegative. -/
theorem residualInvariant_budget_bits (nonneg : ∀ i v, 0 ≤ cost i v)
    {L : Finset ι} {A : ι → Finset V} {b : ℕ}
    (hb : b ≤ upperBudget L A (scaledCosts L A cost)) {s : State ι V}
    (hs : ResidualInvariant cost L A ((b : ℚ) / commonDenominator L A cost) s) :
    rationalBits s.budget ≤ 4 * numericSize L A cost + 2 := by
  rcases hs with ⟨K, x, hK, hlabels, hA, hx, hbudget⟩
  rw [hbudget]
  exact residualBudget_rationalBits L K A cost nonneg hK b hb x hx

theorem residualInvariant_candidate_bits {L : Finset ι} {A : ι → Finset V}
    {B : ℚ} {s : State ι V} (hs : ResidualInvariant cost L A B s)
    (i : ι) (hi : i ∈ s.labels) (v : V) (hv : v ∈ s.candidates i) :
    rationalBits (cost i v) ≤ numericSize L A cost :=
  rationalBits_le_numericSize L A cost i (hs.labels_subset cost hi) v
    (hs.candidates_subset cost i hv)

/-- Inputs actually tested by `firstYes`, stopping at its first success. -/
def firstYesTrace (p : α → Bool) : List α → List α
  | [] => []
  | a :: as => a :: if p a then [] else firstYesTrace p as

theorem firstYesTrace_subset (p : α → Bool) (xs : List α) :
    ∀ a ∈ firstYesTrace p xs, a ∈ xs := by
  induction xs with
  | nil => simp [firstYesTrace]
  | cons x xs ih =>
    intro a ha
    simp only [firstYesTrace, List.mem_cons] at ha
    rcases ha with rfl | ha
    · simp
    · cases hp : p x <;> simp only [hp, Bool.false_eq_true,
        ↓reduceIte] at ha
      · exact List.mem_cons_of_mem _ (ih a ha)
      · simp at ha

theorem firstYesTrace_length (p : α → Bool) (xs : List α) :
    (firstYesTrace p xs).length = (firstYes p xs).2 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases hp : p x <;> simp [firstYesTrace, firstYes, hp, ih]

/-- The exact sequence of oracle inputs used by self-reduction, including
failed tentative assignments and the recursive successful continuation. -/
def recoverQueries (oracle : State ι V → Bool) : ℕ → State ι V → List (State ι V)
  | 0, _ => []
  | fuel + 1, s =>
    if h : s.labels.Nonempty then
      let i := s.labels.min' h
      let choices := (s.candidates i).sort (· ≤ ·)
      let p := fun v => oracle (child R cost s i v)
      let queries := (firstYesTrace p choices).map (child R cost s i)
      match (firstYes p choices).1 with
      | none => queries
      | some v => queries ++ recoverQueries oracle fuel (child R cost s i v)
    else []

theorem recoverQueries_length (oracle : State ι V → Bool) : ∀ fuel s,
    (recoverQueries R cost oracle fuel s).length = (recover R cost oracle fuel s).2 := by
  intro fuel
  induction fuel with
  | zero => intro s; simp [recoverQueries, recover]; split <;> rfl
  | succ fuel ih =>
    intro s
    by_cases h : s.labels.Nonempty
    · simp only [recoverQueries, recover, dif_pos h]
      split <;> simp_all [List.length_append, firstYesTrace_length]
    · simp only [recoverQueries, recover, dif_neg h, List.length_nil]
      split <;> rfl

theorem recoverQueries_invariant (oracle : State ι V → Bool) (P : State ι V → Prop)
    (hchild : ∀ s, P s → ∀ i ∈ s.labels, ∀ v ∈ s.candidates i, P (child R cost s i v)) :
    ∀ fuel s, P s → ∀ t ∈ recoverQueries R cost oracle fuel s, P t := by
  intro fuel
  induction fuel with
  | zero => simp [recoverQueries]
  | succ fuel ih =>
    intro s hs t ht
    by_cases h : s.labels.Nonempty
    · let i := s.labels.min' h
      let choices := (s.candidates i).sort (· ≤ ·)
      let p := fun v => oracle (child R cost s i v)
      have hi : i ∈ s.labels := s.labels.min'_mem h
      have hqueries : ∀ t ∈ (firstYesTrace p choices).map (child R cost s i), P t := by
        intro t ht
        rcases List.mem_map.mp ht with ⟨v, hv, rfl⟩
        have hv' : v ∈ s.candidates i := by
          simpa [choices] using firstYesTrace_subset p choices v hv
        exact hchild s hs i hi v hv'
      simp only [recoverQueries, dif_pos h] at ht
      change t ∈ (match (firstYes p choices).1 with
        | none => (firstYesTrace p choices).map (child R cost s i)
        | some v => (firstYesTrace p choices).map (child R cost s i) ++
            recoverQueries R cost oracle fuel (child R cost s i v)) at ht
      cases hp : (firstYes p choices).1 with
      | none => simp only [hp] at ht; exact hqueries t ht
      | some v =>
        have hv : v ∈ s.candidates i := by
          simpa [choices] using (firstYes_some p choices v hp).1
        simp only [hp, List.mem_append] at ht
        exact ht.elim (hqueries t) (ih _ (hchild s hs i hi v hv) t)
    · simp [recoverQueries, h] at ht

/-- Binary-search midpoint trace, following the actual predicate outcomes. -/
def bisectQueries (p : ℕ → Bool) : ℕ → ℕ → ℕ → List ℕ
  | 0, _, _ => []
  | fuel + 1, lo, hi =>
    let mid := (lo + hi) / 2
    mid :: if p mid then bisectQueries p fuel lo mid else bisectQueries p fuel (mid + 1) hi

theorem bisectQueries_length (p : ℕ → Bool) : ∀ fuel lo hi,
    (bisectQueries p fuel lo hi).length = bisectCalls p fuel lo hi := by
  intro fuel
  induction fuel with
  | zero => simp [bisectQueries, bisectCalls]
  | succ fuel ih => intro lo hi; simp [bisectQueries, bisectCalls]; split <;> simp [ih, Nat.add_comm]

/-- Feasibility of the upper endpoint alone keeps every midpoint and returned
budget inside the initial interval, even after it has become a singleton. -/
theorem bisectQueries_bounds (p : ℕ → Bool) : ∀ fuel lo hi,
    lo ≤ hi → p hi = true →
    (lo ≤ bisect p fuel lo hi ∧ bisect p fuel lo hi ≤ hi) ∧
    ∀ b ∈ bisectQueries p fuel lo hi, lo ≤ b ∧ b ≤ hi := by
  intro fuel
  induction fuel with
  | zero => intro lo hi hle hp; simp [bisect, bisectQueries, hle]
  | succ fuel ih =>
    intro lo hi hle hhi
    let mid := (lo + hi) / 2
    have hlo : lo ≤ mid := by dsimp [mid]; omega
    have hmid : mid ≤ hi := by dsimp [mid]; omega
    by_cases hp : p mid = true
    · have hh := ih lo mid hlo hp
      simp only [bisect, bisectQueries, show (lo + hi) / 2 = mid from rfl, hp, ↓reduceIte]
      refine ⟨⟨hh.1.1, hh.1.2.trans hmid⟩, ?_⟩
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ⟨hlo, hmid⟩
      · exact ⟨(hh.2 b hb).1, (hh.2 b hb).2.trans hmid⟩
    · have hfalse : p mid = false := Bool.eq_false_iff.mpr hp
      have hlt : mid < hi := by
        by_contra hn
        have heq : mid = hi := by omega
        exact hp (heq ▸ hhi)
      have hh := ih (mid + 1) hi (by omega) hhi
      simp only [bisect, bisectQueries, show (lo + hi) / 2 = mid from rfl, hfalse,
        Bool.false_eq_true, ↓reduceIte]
      refine ⟨⟨by omega, hh.1.2⟩, ?_⟩
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ⟨hlo, hmid⟩
      · exact ⟨by have := (hh.2 b hb).1; omega, (hh.2 b hb).2⟩

def leastBudgetQueries (p : ℕ → Bool) (U : ℕ) : List ℕ :=
  U :: if p U then bisectQueries p (Nat.log2 U + 1) 0 U else []

theorem leastBudgetQueries_le (p : ℕ → Bool) (U b : ℕ)
    (hb : b ∈ leastBudgetQueries p U) : b ≤ U := by
  simp only [leastBudgetQueries, List.mem_cons] at hb
  rcases hb with rfl | hb
  · rfl
  · cases hp : p U with
    | false => simp [hp] at hb
    | true =>
      simp only [hp, ↓reduceIte] at hb
      exact ((bisectQueries_bounds p _ 0 U (Nat.zero_le _) hp).2 b hb).2

theorem leastBudget_result_le (p : ℕ → Bool) (U b : ℕ)
    (hb : leastBudget p U = some b) : b ≤ U := by
  unfold leastBudget at hb
  split at hb
  · rename_i hp
    have heq := Option.some.inj hb
    subst b
    exact (bisectQueries_bounds p _ 0 U (Nat.zero_le _) hp).1.2
  · contradiction

/-- Exact decision-oracle inputs used by the optimizer. -/
def optimizeQueries (L : Finset ι) (A : ι → Finset V) : List (State ι V) :=
  let D := commonDenominator L A cost
  let U := upperBudget L A (scaledCosts L A cost)
  let oracle := decidePrefix R cost ops threshold
  let initial := fun b : ℕ => budgetState L A ((b : ℚ) / D)
  let p := fun b => oracle (initial b)
  (leastBudgetQueries p U).map initial ++ match leastBudget p U with
    | none => []
    | some b => recoverQueries R cost oracle L.card (initial b)

/-- Every oracle input has its own actual initial query budget in `[0,U]`
and a distinct-label partial assignment over the original candidates. -/
theorem optimizeQueries_invariant (L : Finset ι) (A : ι → Finset V) :
    ∀ s ∈ optimizeQueries R cost ops threshold L A,
    ∃ b ≤ upperBudget L A (scaledCosts L A cost),
      ResidualInvariant cost L A ((b : ℚ) / commonDenominator L A cost) s := by
  intro s hs
  let D := commonDenominator L A cost
  let U := upperBudget L A (scaledCosts L A cost)
  let oracle := decidePrefix R cost ops threshold
  let initial := fun b : ℕ => budgetState L A ((b : ℚ) / D)
  let p := fun b => oracle (initial b)
  change s ∈ (leastBudgetQueries p U).map initial ++
    (match leastBudget p U with | none => [] | some b => recoverQueries R cost oracle L.card (initial b)) at hs
  rcases List.mem_append.mp hs with hs | hs
  · rcases List.mem_map.mp hs with ⟨b, hb, rfl⟩
    exact ⟨b, leastBudgetQueries_le p U b hb, residualInvariant_initial cost L A _⟩
  · cases hb : leastBudget p U with
    | none => simp [hb] at hs
    | some b =>
      simp only [hb] at hs
      refine ⟨b, leastBudget_result_le p U b hb, ?_⟩
      exact recoverQueries_invariant R cost oracle
        (ResidualInvariant cost L A ((b : ℚ) / D))
        (fun _ h i hi v hv => h.child R cost i hi v hv) L.card (initial b)
        (residualInvariant_initial cost L A _) s hs

/-- Combined query and interpreter trace: this directly covers every state
expanded by every decision call made by exact optimization. -/
def optimizeExecutionTrace (L : Finset ι) (A : ι → Finset V) : List (State ι V) :=
  (optimizeQueries R cost ops threshold L A).flatMap fun s =>
    runTrace (prefixStep R cost ops threshold) s.labels.card s

theorem optimizeExecutionTrace_invariant (L : Finset ι) (A : ι → Finset V)
    (s : State ι V) (hs : s ∈ optimizeExecutionTrace R cost ops threshold L A) :
    ∃ b ≤ upperBudget L A (scaledCosts L A cost),
      ResidualInvariant cost L A ((b : ℚ) / commonDenominator L A cost) s := by
  rcases List.mem_flatMap.mp hs with ⟨q, hq, hs⟩
  rcases optimizeQueries_invariant R cost ops threshold L A q hq with ⟨b, hb, hq⟩
  exact ⟨b, hb, residualInvariant_runTrace R cost ops threshold hq q.labels.card s hs⟩

theorem optimizeExecutionTrace_budget_bits (nonneg : ∀ i v, 0 ≤ cost i v)
    (L : Finset ι) (A : ι → Finset V) (s : State ι V)
    (hs : s ∈ optimizeExecutionTrace R cost ops threshold L A) :
    rationalBits s.budget ≤ 4 * numericSize L A cost + 2 := by
  rcases optimizeExecutionTrace_invariant R cost ops threshold L A s hs with ⟨b, hb, hs⟩
  exact residualInvariant_budget_bits cost nonneg hb hs

/-- Every intermediate maximum is zero or one of the examined input costs. -/
theorem prefixMax_eq_zero_or_mem (c : V → ℚ) (P : Finset V) :
    prefixMax c P = 0 ∨ ∃ v ∈ P, prefixMax c P = c v := by
  induction P using Finset.induction_on with
  | empty => left; simp [prefixMax]
  | @insert v P hv ih =>
    rw [prefixMax, Finset.fold_insert hv]
    change max (c v) (prefixMax c P) = 0 ∨
      ∃ u ∈ insert v P, max (c v) (prefixMax c P) = c u
    by_cases h : c v ≤ prefixMax c P
    · rw [max_eq_right h]
      rcases ih with ih | ⟨u, hu, heq⟩
      · exact Or.inl ih
      · exact Or.inr ⟨u, Finset.mem_insert_of_mem hu, heq⟩
    · rw [max_eq_left (le_of_not_ge h)]
      exact Or.inr ⟨v, Finset.mem_insert_self _ _, rfl⟩

/-- A sum containing at most one original cost per label (with zero allowed)
is a genuine partial assignment sum. This includes partial prefix-total folds. -/
theorem sparseCostSum_representation (L J : Finset ι) (A : ι → Finset V)
    (q : ι → ℚ) (hJ : J ⊆ L)
    (hq : ∀ i ∈ J, q i = 0 ∨ ∃ v ∈ A i, q i = cost i v) :
    ∃ (K : Finset ι) (x : ι → V), K ⊆ L ∧
      (∀ i ∈ K, x i ∈ A i) ∧ (∑ i ∈ J, q i) = ∑ i ∈ K, cost i (x i) := by
  classical
  let K := J.filter fun i => q i ≠ 0
  have hK : K ⊆ J := Finset.filter_subset _ _
  have hex : ∀ i ∈ K, ∃ v ∈ A i, q i = cost i v := by
    intro i hi
    exact (hq i (hK hi)).resolve_left (Finset.mem_filter.mp hi).2
  let x := fun i => if h : ∃ v ∈ A i, q i = cost i v then Classical.choose h else default
  have hx : ∀ i ∈ K, x i ∈ A i ∧ q i = cost i (x i) := by
    intro i hi
    dsimp only [x]
    rw [dif_pos (hex i hi)]
    exact Classical.choose_spec (hex i hi)
  refine ⟨K, x, hK.trans hJ, fun i hi => (hx i hi).1, ?_⟩
  calc
    (∑ i ∈ J, q i) = ∑ i ∈ K, q i := by
      symm
      apply Finset.sum_subset hK
      intro i hi hn
      by_contra h
      exact hn (Finset.mem_filter.mpr ⟨hi, h⟩)
    _ = _ := Finset.sum_congr rfl (fun i hi => (hx i hi).2)

theorem partialCostSum_rationalBits (nonneg : ∀ i v, 0 ≤ cost i v)
    (L K : Finset ι) (A : ι → Finset V) (hK : K ⊆ L)
    (x : ι → V) (hx : ∀ i ∈ K, x i ∈ A i) :
    rationalBits (∑ i ∈ K, cost i (x i)) ≤ 4 * numericSize L A cost + 2 := by
  have h := residualBudget_rationalBits L K A cost nonneg hK 0 (Nat.zero_le _) x hx
  simpa [rationalBits] using h

/-- All partial prefix-sum accumulators and all partial maximum scans have
linear normalized encoding size. `J` may be any subset of active labels and
`P i` any subset already scanned, so this includes all loop intermediates. -/
theorem residualInvariant_prefixSum_bits (nonneg : ∀ i v, 0 ≤ cost i v)
    {L : Finset ι} {A : ι → Finset V} {B : ℚ} {s : State ι V}
    (hs : ResidualInvariant cost L A B s) (J : Finset ι) (hJ : J ⊆ s.labels)
    (P : ι → Finset V) (hP : ∀ i ∈ J, P i ⊆ s.candidates i) :
    rationalBits (∑ i ∈ J, prefixMax (cost i) (P i)) ≤ 4 * numericSize L A cost + 2 := by
  have hq : ∀ i ∈ J, prefixMax (cost i) (P i) = 0 ∨
      ∃ v ∈ A i, prefixMax (cost i) (P i) = cost i v := by
    intro i hi
    rcases prefixMax_eq_zero_or_mem (cost i) (P i) with h | ⟨v, hv, heq⟩
    · exact Or.inl h
    · exact Or.inr ⟨v, hs.candidates_subset cost i (hP i hi hv), heq⟩
  rcases sparseCostSum_representation cost L J A (fun i => prefixMax (cost i) (P i))
      (hJ.trans (hs.labels_subset cost)) hq with ⟨K, x, hK, hx, heq⟩
  rw [heq]
  exact partialCostSum_rationalBits cost nonneg L K A hK x hx

theorem residualInvariant_prefixTotal_bits (nonneg : ∀ i v, 0 ≤ cost i v)
    {L : Finset ι} {A : ι → Finset V} {B : ℚ} {s : State ι V}
    (hs : ResidualInvariant cost L A B s) :
    rationalBits (prefixTotal cost costPrefixOperations threshold s) ≤
      4 * numericSize L A cost + 2 := by
  exact residualInvariant_prefixSum_bits cost nonneg hs s.labels (Finset.Subset.refl _)
    (prefixes cost costPrefixOperations threshold s)
    (fun i _ => cheapPrefix_subset _ _ _)

include R in
/-- A tentative subtraction used while materializing a child already has the
same residual bound, whether or not the child's budget is negative. -/
theorem residualInvariant_childBudget_bits (nonneg : ∀ i v, 0 ≤ cost i v)
    {L : Finset ι} {A : ι → Finset V} {b : ℕ}
    (hb : b ≤ upperBudget L A (scaledCosts L A cost)) {s : State ι V}
    (hs : ResidualInvariant cost L A ((b : ℚ) / commonDenominator L A cost) s)
    (i : ι) (hi : i ∈ s.labels) (v : V) (hv : v ∈ s.candidates i) :
    rationalBits (s.budget - cost i v) ≤ 4 * numericSize L A cost + 2 :=
  residualInvariant_budget_bits cost nonneg hb (hs.child R cost i hi v hv)

/-- The entire actual optimizer execution satisfies the rational operand
bounds needed by the concrete prefix implementation. -/
theorem optimizeExecutionTrace_operands_bits (nonneg : ∀ i v, 0 ≤ cost i v)
    (L : Finset ι) (A : ι → Finset V) (s : State ι V)
    (hs : s ∈ optimizeExecutionTrace R cost costPrefixOperations threshold L A) :
    rationalBits s.budget ≤ 4 * numericSize L A cost + 2 ∧
    rationalBits (prefixTotal cost costPrefixOperations threshold s) ≤ 4 * numericSize L A cost + 2 ∧
    (∀ i ∈ s.labels, ∀ v ∈ s.candidates i, rationalBits (cost i v) ≤ numericSize L A cost) ∧
    (∀ i ∈ s.labels, ∀ v ∈ s.candidates i,
      rationalBits (s.budget - cost i v) ≤ 4 * numericSize L A cost + 2) := by
  rcases optimizeExecutionTrace_invariant R cost costPrefixOperations threshold L A s hs with
    ⟨b, hb, hs⟩
  exact ⟨residualInvariant_budget_bits cost nonneg hb hs,
    residualInvariant_prefixTotal_bits cost threshold nonneg hs,
    residualInvariant_candidate_bits cost hs,
    residualInvariant_childBudget_bits R cost nonneg hb hs⟩

/-- Traces refine the already defined exact oracle-work counters, not merely
a superset of possible queries. -/
theorem firstYesTrace_work (p : α → Bool) (work : α → ℕ) (xs : List α) :
    ((firstYesTrace p xs).map work).sum = firstYesWork p work xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases hp : p x <;> simp [firstYesTrace, firstYesWork, hp, ih]

theorem recoverQueries_work (oracle : State ι V → Bool) (work : State ι V → ℕ) :
    ∀ fuel s, ((recoverQueries R cost oracle fuel s).map work).sum =
      recoverWork R cost oracle work fuel s := by
  intro fuel
  induction fuel with
  | zero => intro s; rfl
  | succ fuel ih =>
    intro s
    by_cases h : s.labels.Nonempty
    · simp only [recoverQueries, recoverWork, dif_pos h]
      split <;> simp_all [List.map_append, List.sum_append, List.map_map,
        firstYesTrace_work, Function.comp_def]
    · simp [recoverQueries, recoverWork, h]

theorem bisectQueries_work (p : ℕ → Bool) (work : ℕ → ℕ) : ∀ fuel lo hi,
    ((bisectQueries p fuel lo hi).map work).sum = bisectWork p work fuel lo hi := by
  intro fuel
  induction fuel with
  | zero => intro lo hi; rfl
  | succ fuel ih => intro lo hi; simp [bisectQueries, bisectWork]; split <;> simp [ih]

theorem leastBudgetQueries_work (p : ℕ → Bool) (work : ℕ → ℕ) (U : ℕ) :
    ((leastBudgetQueries p U).map work).sum = leastBudgetWork p work U := by
  unfold leastBudgetQueries leastBudgetWork
  cases hp : p U <;> simp [hp, bisectQueries_work]

theorem leastBudgetQueries_length (p : ℕ → Bool) (U : ℕ) :
    (leastBudgetQueries p U).length = (leastBudgetCounted p U).2 := by
  unfold leastBudgetQueries leastBudgetCounted
  cases hp : p U <;> simp [hp, bisectQueries_length, Nat.add_comm]

theorem optimizeQueries_length (L : Finset ι) (A : ι → Finset V) :
    (optimizeQueries R cost ops threshold L A).length =
      (optimizeCounted R cost ops threshold L A).2 := by
  unfold optimizeQueries optimizeCounted
  simp only [leastBudgetCounted_value, List.length_append, List.length_map,
    leastBudgetQueries_length]
  split <;> simp_all [recoverQueries_length]

theorem optimizeQueries_work (work : State ι V → ℕ) (L : Finset ι) (A : ι → Finset V) :
    ((optimizeQueries R cost ops threshold L A).map work).sum =
      optimizeOracleWork R cost ops threshold work L A := by
  unfold optimizeQueries optimizeOracleWork
  simp only [List.map_append, List.sum_append, List.map_map]
  rw [leastBudgetQueries_work]
  split <;> simp_all [recoverQueries_work, Function.comp_def]

/-- Membership-sensitive bounded-work composition. No bound on unqueried
budgets or on arbitrary vertices outside their candidate sets is required. -/
theorem optimizeOracleWork_le_actual_queries (work : State ι V → ℕ)
    (L : Finset ι) (A : ι → Finset V) (C : ℕ)
    (hwork : ∀ s ∈ optimizeQueries R cost ops threshold L A, work s ≤ C) :
    optimizeOracleWork R cost ops threshold work L A ≤
      (optimizeCounted R cost ops threshold L A).2 * C := by
  rw [← optimizeQueries_work]
  have h := list_sum_le_length_mul hwork
  rwa [optimizeQueries_length] at h

theorem optimizeOracleWork_le_residual (work : State ι V → ℕ)
    (L : Finset ι) (A : ι → Finset V) (C : ℕ)
    (hwork : ∀ b ≤ upperBudget L A (scaledCosts L A cost), ∀ s,
      ResidualInvariant cost L A ((b : ℚ) / commonDenominator L A cost) s → work s ≤ C) :
    optimizeOracleWork R cost ops threshold work L A ≤
      (optimizeCounted R cost ops threshold L A).2 * C := by
  apply optimizeOracleWork_le_actual_queries R cost ops threshold work L A C
  intro s hs
  rcases optimizeQueries_invariant R cost ops threshold L A s hs with ⟨b, hb, hs⟩
  exact hwork b hb s hs

/-- Direct decision also permits arbitrarily large or negative supplied
budgets. Its encoding is included explicitly rather than bounded by `U`. -/
theorem residualInvariant_arbitraryBudget_bits (nonneg : ∀ i v, 0 ≤ cost i v)
    {L : Finset ι} {A : ι → Finset V} {B : ℚ} {s : State ι V}
    (hs : ResidualInvariant cost L A B s) :
    rationalBits s.budget ≤ 2 * rationalBits B + 8 * numericSize L A cost + 7 := by
  rcases hs with ⟨K, x, hK, hlabels, hA, hx, hb⟩
  have hsum := partialCostSum_rationalBits cost nonneg L K A hK x hx
  have hsub := rationalBits_sub_le B (∑ i ∈ K, cost i (x i))
  rw [hb]
  omega

theorem decidePrefix_runTrace_budget_bits (nonneg : ∀ i v, 0 ≤ cost i v)
    (L : Finset ι) (A : ι → Finset V) (B : ℚ) (fuel : ℕ) (s : State ι V)
    (hs : s ∈ runTrace (prefixStep R cost ops threshold) fuel (budgetState L A B)) :
    rationalBits s.budget ≤ 2 * rationalBits B + 8 * numericSize L A cost + 7 :=
  residualInvariant_arbitraryBudget_bits cost nonneg
    (residualInvariant_runTrace R cost ops threshold
      (residualInvariant_initial cost L A B) fuel s hs)

/-- Even the unnormalized integer cross-products in the comparison of the
prefix total to the residual budget have linear input-bit length. -/
theorem optimizeExecutionTrace_comparison_bits (nonneg : ∀ i v, 0 ≤ cost i v)
    (L : Finset ι) (A : ι → Finset V) (s : State ι V)
    (hs : s ∈ optimizeExecutionTrace R cost costPrefixOperations threshold L A) :
    let p := prefixTotal cost costPrefixOperations threshold s
    binaryLength (p.num * (s.budget.den : ℤ)).natAbs ≤ 8 * numericSize L A cost + 5 ∧
    binaryLength (s.budget.num * (p.den : ℤ)).natAbs ≤ 8 * numericSize L A cost + 5 ∧
    binaryLength (p.num * (s.budget.den : ℤ) - s.budget.num * (p.den : ℤ)).natAbs ≤
      8 * numericSize L A cost + 6 ∧
    binaryLength (p.den * s.budget.den) ≤ 8 * numericSize L A cost + 5 := by
  dsimp only
  have h := optimizeExecutionTrace_operands_bits R cost threshold nonneg L A s hs
  have hb := rational_arithmetic_intermediates
    (prefixTotal cost costPrefixOperations threshold s) s.budget
  omega

/-- The midpoint calculation adds two endpoint integers before division by
2. That temporary sum also has linear bit size, including singleton intervals. -/
theorem optimization_midpoint_temporary_bits (L : Finset ι) (A : ι → Finset V)
    (lo hi : ℕ) (hlo : lo ≤ upperBudget L A (scaledCosts L A cost))
    (hhi : hi ≤ upperBudget L A (scaledCosts L A cost)) :
    binaryLength (lo + hi) ≤ 3 * numericSize L A cost + 2 ∧
    binaryLength ((lo + hi) / 2) ≤ 3 * numericSize L A cost + 2 := by
  have hU := upperBudget_le_numeric_pow L A cost
  have hsum : lo + hi ≤ 2 ^ (3 * numericSize L A cost + 1) := by
    rw [pow_succ]
    omega
  have h := binaryLength_le_of_le_pow hsum
  exact ⟨by omega, (binaryLength_mono (Nat.div_le_self _ _)).trans (by omega)⟩

/-- The actual sorted-label prefix-total accumulator after any number of
iterations, including the empty accumulator. -/
theorem residualInvariant_prefixAccumulator_bits (nonneg : ∀ i v, 0 ≤ cost i v)
    {L : Finset ι} {A : ι → Finset V} {B : ℚ} {s : State ι V}
    (hs : ResidualInvariant cost L A B s) (n : ℕ) :
    rationalBits ((((s.labels.sort (· ≤ ·)).take n).map
      (fun i => prefixMax (cost i) (prefixes cost costPrefixOperations threshold s i))).sum) ≤
      4 * numericSize L A cost + 2 := by
  rw [← List.sum_toFinset _ ((s.labels.sort_nodup (· ≤ ·)).take)]
  apply residualInvariant_prefixSum_bits cost nonneg hs
  · intro i hi
    have hi' := List.mem_of_mem_take (List.mem_toFinset.mp hi)
    simpa using hi'
  · intro i hi
    exact cheapPrefix_subset _ _ _

/-- Refinement of a maximum-scan accumulator to the finite-set maximum. -/
theorem maximumScan_eq_prefixMax (c : V → ℚ) (xs : List V) (hn : xs.Nodup) :
    (xs.map c).foldl max 0 = prefixMax c xs.toFinset := by
  simp [prefixMax, Finset.fold, hn.dedup, List.foldl_eq_foldr]

/-- Every intermediate maximum scan over actual remaining candidates uses
an original cost or zero, so it fits the same uniform bit envelope. -/
theorem residualInvariant_maximumAccumulator_bits
    {L : Finset ι} {A : ι → Finset V} {B : ℚ} {s : State ι V}
    (hs : ResidualInvariant cost L A B s) (i : ι) (hi : i ∈ s.labels)
    (xs : List V) (hn : xs.Nodup) (hx : ∀ v ∈ xs, v ∈ s.candidates i) (n : ℕ) :
    rationalBits (((xs.take n).map (cost i)).foldl max 0) ≤ 4 * numericSize L A cost + 2 := by
  rw [maximumScan_eq_prefixMax _ _ hn.take]
  rcases prefixMax_eq_zero_or_mem (cost i) (xs.take n).toFinset with h | ⟨v, hv, heq⟩
  · rw [h, show rationalBits (0 : ℚ) = 2 from by decide]
    omega
  · rw [heq]
    have hcost := residualInvariant_candidate_bits cost hs i hi v
      (hx v (List.mem_of_mem_take (List.mem_toFinset.mp hv)))
    omega

end IndependentSetDiscovery.Algorithms
