import IndependentSetDiscovery.Algorithms.State

namespace IndependentSetDiscovery.Algorithms

variable {ι V : Type*} [LinearOrder ι] [LinearOrder V] [Inhabited V]

/-- Computational prefix data with its elementary sorted-cost specifications. -/
structure PrefixOperations (V : Type*) [LinearOrder V] where
  takeCheap : (V → ℚ) → Finset V → ℕ → Finset V
  peak : (V → ℚ) → Finset V → ℚ
  subset : ∀ c A t, takeCheap c A t ⊆ A
  card : ∀ c A t, (takeCheap c A t).card = min t A.card
  below_peak : ∀ c A v, v ∈ A → c v ≤ peak c A
  outside : ∀ c A t v, (∀ u, 0 ≤ c u) → 0 < t → t ≤ A.card →
    v ∈ A → v ∉ takeCheap c A t → peak c (takeCheap c A t) ≤ c v

variable (R : V → V → Prop) [DecidableRel R] (cost : ι → V → ℚ)
variable (ops : PrefixOperations V) (threshold : ℕ → ℕ)

def prefixes (s : State ι V) (i : ι) : Finset V :=
  ops.takeCheap (cost i) (s.candidates i) (threshold s.labels.card)

def prefixTotal (s : State ι V) : ℚ :=
  ∑ i ∈ s.labels, ops.peak (cost i) (prefixes cost ops threshold s i)

def smallLabels (s : State ι V) : Finset ι :=
  s.labels.filter fun i => (s.candidates i).card < threshold s.labels.card

/-- The only graph-specific input to cheap-prefix branching. -/
def TransversalCertificate : Prop :=
  ∀ (L : Finset ι) (A : ι → Finset V), L.Nonempty →
    (∀ i ∈ L, (A i).card = threshold L.card) →
    ∃ x : ι → V, (∀ i ∈ L, x i ∈ A i) ∧
      (∀ i ∈ L, ∀ j ∈ L, i ≠ j → R (x i) (x j))

def allPrefixBranches (s : State ι V) : List (State ι V) :=
  (s.labels.sort (· ≤ ·)).flatMap fun i =>
    ((prefixes cost ops threshold s i).sort (· ≤ ·)).map fun v => child R cost s i v

/-- The actual deterministic cheap-prefix decision step, including all three cases. -/
def prefixStep (s : State ι V) : Instruction (State ι V) :=
  if s.budget < 0 then .no
  else if s.labels = ∅ then .yes
  else if h : (smallLabels threshold s).Nonempty then
    let i := (smallLabels threshold s).min' h
    .branch (((s.candidates i).sort (· ≤ ·)).map fun v => child R cost s i v)
  else if prefixTotal cost ops threshold s ≤ s.budget then .yes
  else .branch (allPrefixBranches R cost ops threshold s)

theorem full_prefixes (s : State ι V) (hsmall : ¬(smallLabels threshold s).Nonempty) :
    ∀ i ∈ s.labels, (prefixes cost ops threshold s i).card = threshold s.labels.card := by
  intro i hi
  have hle : threshold s.labels.card ≤ (s.candidates i).card := by
    by_contra h
    have : i ∈ smallLabels threshold s := Finset.mem_filter.mpr ⟨hi, by omega⟩
    exact hsmall ⟨i, this⟩
  simp [prefixes, ops.card, Nat.min_eq_left hle]

theorem affordable_prefixes (certificate : TransversalCertificate (ι := ι) R threshold)
    (s : State ι V) (hne : s.labels.Nonempty)
    (hsmall : ¬(smallLabels threshold s).Nonempty)
    (hbudget : prefixTotal cost ops threshold s ≤ s.budget) : Feasible R cost s := by
  rcases certificate s.labels (prefixes cost ops threshold s) hne
      (full_prefixes cost ops threshold s hsmall) with ⟨x, hmem, hpair⟩
  refine ⟨x, ?_, hpair, ?_⟩
  · intro i hi
    exact ops.subset _ _ _ (hmem i hi)
  · calc
      (∑ i ∈ s.labels, cost i (x i)) ≤ prefixTotal cost ops threshold s := by
        apply Finset.sum_le_sum
        intro i hi
        exact ops.below_peak _ _ _ (hmem i hi)
      _ ≤ s.budget := hbudget

theorem overbudget_meets_prefix (nonneg : ∀ i v, 0 ≤ cost i v)
    (positive : ∀ r, 0 < threshold r) (s : State ι V)
    (hsmall : ¬(smallLabels threshold s).Nonempty)
    (hover : s.budget < prefixTotal cost ops threshold s)
    (x : ι → V) (hx : Completion R cost s x) :
    ∃ i ∈ s.labels, x i ∈ prefixes cost ops threshold s i := by
  by_contra h
  have hav : ∀ i ∈ s.labels, x i ∉ prefixes cost ops threshold s i := by aesop
  have hlower : prefixTotal cost ops threshold s ≤ ∑ i ∈ s.labels, cost i (x i) := by
    apply Finset.sum_le_sum
    intro i hi
    have hle : threshold s.labels.card ≤ (s.candidates i).card := by
      have := full_prefixes cost ops threshold s hsmall i hi
      rw [prefixes, ops.card] at this
      omega
    exact ops.outside _ _ _ _ (nonneg i) (positive _) hle (hx.1 i hi) (hav i hi)
  exact (not_lt_of_ge (hlower.trans hx.2.2)) hover

theorem mem_allPrefixBranches (s t : State ι V) :
    t ∈ allPrefixBranches R cost ops threshold s ↔
      ∃ i ∈ s.labels, ∃ v ∈ prefixes cost ops threshold s i, t = child R cost s i v := by
  simp only [allPrefixBranches, List.mem_flatMap, Finset.mem_sort, List.mem_map]
  aesop

theorem allPrefixBranches_length_le (s : State ι V) :
    (allPrefixBranches R cost ops threshold s).length ≤ s.labels.card * threshold s.labels.card := by
  simp only [allPrefixBranches, List.length_flatMap, List.length_map, Finset.length_sort]
  calc
    ((s.labels.sort (· ≤ ·)).map (fun i => (prefixes cost ops threshold s i).card)).sum ≤
        (s.labels.sort (· ≤ ·)).length * threshold s.labels.card := by
      apply list_sum_le_length_mul
      intro i hi
      simp only [prefixes, ops.card]
      exact Nat.min_le_left _ _
    _ = _ := by rw [Finset.length_sort]

theorem prefixStep_correct
    (symm : Symmetric R) (nonneg : ∀ i v, 0 ≤ cost i v)
    (positive : ∀ r, 0 < threshold r)
    (certificate : TransversalCertificate (ι := ι) R threshold) :
    CorrectStep (prefixStep R cost ops threshold) (Feasible R cost)
      (fun s => s.labels.card) := by
  constructor
  · intro s hstep
    unfold prefixStep at hstep
    split_ifs at hstep with hb he hs ha
    · refine ⟨fun _ => default, ?_⟩
      simp [Completion, he, le_of_not_gt hb]
    · exact affordable_prefixes R cost ops threshold certificate s
        (Finset.nonempty_iff_ne_empty.mpr he) hs ha
  · intro s hstep
    unfold prefixStep at hstep
    split_ifs at hstep with hb he hs ha
    · rintro ⟨x, hx⟩
      have hn : 0 ≤ ∑ i ∈ s.labels, cost i (x i) :=
        Finset.sum_nonneg (fun i _ => nonneg i (x i))
      linarith [hx.2.2]
  · intro s children hstep
    unfold prefixStep at hstep
    split_ifs at hstep with hb he hs ha
    · injection hstep with hc
      subst children
      let i := (smallLabels threshold s).min' hs
      have hi : i ∈ s.labels :=
        (Finset.mem_filter.mp ((smallLabels threshold s).min'_mem hs)).1
      rw [feasible_iff_some_child R cost symm nonneg s i hi]
      simp only [List.mem_map, Finset.mem_sort]
      constructor
      · rintro ⟨v, hv, hchild⟩
        exact ⟨child R cost s i v, ⟨v, hv, rfl⟩, hchild⟩
      · rintro ⟨t, ⟨v, hv, rfl⟩, hchild⟩
        exact ⟨v, hv, hchild⟩
    · injection hstep with hc
      subst children
      constructor
      · rintro ⟨x, hx⟩
        rcases overbudget_meets_prefix R cost ops threshold nonneg positive s hs
            (lt_of_not_ge ha) x hx with ⟨i, hi, hp⟩
        refine ⟨child R cost s i (x i), ?_, x,
          completion_child_of_fixed R cost nonneg s i (x i) hi x hx rfl⟩
        exact (mem_allPrefixBranches R cost ops threshold s _).mpr ⟨i, hi, x i, hp, rfl⟩
      · rintro ⟨t, ht, x, hx⟩
        rcases (mem_allPrefixBranches R cost ops threshold s t).mp ht with ⟨i, hi, v, hv, rfl⟩
        refine ⟨Function.update x i v, completion_extend R cost symm s i v hi ?_ x hx⟩
        exact ops.subset _ _ _ hv
  · intro s children hstep t ht
    unfold prefixStep at hstep
    split_ifs at hstep with hb he hs ha
    · injection hstep with hc
      subst children
      rcases List.mem_map.mp ht with ⟨v, hv, rfl⟩
      apply child_rank_lt
      exact (Finset.mem_filter.mp ((smallLabels threshold s).min'_mem hs)).1
    · injection hstep with hc
      subst children
      rcases (mem_allPrefixBranches R cost ops threshold s t).mp ht with ⟨i, hi, v, hv, rfl⟩
      exact child_rank_lt R cost s i v hi
  · intro s children hstep
    by_contra h
    have he : s.labels = ∅ := Finset.card_eq_zero.mp (by omega)
    simp [prefixStep, he] at hstep
    split at hstep <;> contradiction

/-- Complete executable decision procedure. -/
def decidePrefix (s : State ι V) : Bool :=
  (run (prefixStep R cost ops threshold) s.labels.card s).1

theorem decidePrefix_correct
    (symm : Symmetric R) (nonneg : ∀ i v, 0 ≤ cost i v)
    (positive : ∀ r, 0 < threshold r)
    (certificate : TransversalCertificate (ι := ι) R threshold) (s : State ι V) :
    decidePrefix R cost ops threshold s = true ↔ Feasible R cost s :=
  run_correct _ _ _ (prefixStep_correct R cost ops threshold symm nonneg positive certificate)
    _ _ (le_refl _)

theorem prefixStep_branching (s : State ι V) (children : List (State ι V))
    (hstep : prefixStep R cost ops threshold s = .branch children) :
    children.length ≤ s.labels.card * threshold s.labels.card := by
  unfold prefixStep at hstep
  split_ifs at hstep with hb he hs ha
  · injection hstep with hc
    subst children
    rw [List.length_map, Finset.length_sort]
    have hi := (smallLabels threshold s).min'_mem hs
    have hsmall := (Finset.mem_filter.mp hi).2
    have hcard : 1 ≤ s.labels.card := by
      exact Finset.card_pos.mpr ⟨_, (Finset.mem_filter.mp hi).1⟩
    nlinarith
  · injection hstep with hc
    subst children
    exact allPrefixBranches_length_le R cost ops threshold s

/-- Explicit finite search bound, depending only on `k` and a maximum threshold. -/
theorem decidePrefix_cost_le
    (symm : Symmetric R) (nonneg : ∀ i v, 0 ≤ cost i v)
    (positive : ∀ r, 0 < threshold r)
    (certificate : TransversalCertificate (ι := ι) R threshold)
    (k maxThreshold : ℕ) (hthreshold : ∀ r ≤ k, threshold r ≤ maxThreshold)
    (s : State ι V) (hs : s.labels.card ≤ k) :
    (run (prefixStep R cost ops threshold) s.labels.card s).2 ≤
      treeBound (k * maxThreshold) s.labels.card := by
  apply run_cost_le_of_rank _ (fun s => s.labels.card) (k * maxThreshold) k
    (prefixStep_correct R cost ops threshold symm nonneg positive certificate).decreases
  · intro t children ht hstep
    calc
      children.length ≤ t.labels.card * threshold t.labels.card :=
        prefixStep_branching R cost ops threshold t children hstep
      _ ≤ k * maxThreshold := Nat.mul_le_mul ht (hthreshold _ ht)
  · exact hs

end IndependentSetDiscovery.Algorithms
