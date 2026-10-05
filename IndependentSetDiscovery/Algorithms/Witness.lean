import IndependentSetDiscovery.Algorithms.State
import IndependentSetDiscovery.Algorithms.FirstWitness

namespace IndependentSetDiscovery.Algorithms

variable {ι V : Type*} [LinearOrder ι] [LinearOrder V] [Inhabited V]
variable (R : V → V → Prop) [DecidableRel R] (cost : ι → V → ℚ)

/-- Witness extraction calls the decision procedure on one tentative assignment at a time.
The second output counts decision calls, including failed tentative assignments. -/
def recover (oracle : State ι V → Bool) : ℕ → State ι V → Option (ι → V) × ℕ
  | 0, s => if s.labels = ∅ ∧ 0 ≤ s.budget then (some (fun _ => default), 0) else (none, 0)
  | fuel + 1, s =>
    if h : s.labels.Nonempty then
      let i := s.labels.min' h
      let probe := firstYes (fun v => oracle (child R cost s i v))
        ((s.candidates i).sort (· ≤ ·))
      match probe.1 with
      | none => (none, probe.2)
      | some v =>
        let tail := recover oracle fuel (child R cost s i v)
        (tail.1.map (fun x => Function.update x i v), probe.2 + tail.2)
    else if 0 ≤ s.budget then (some (fun _ => default), 0) else (none, 0)

def totalCandidates (s : State ι V) : ℕ := ∑ i ∈ s.labels, (s.candidates i).card

theorem totalCandidates_child_le (s : State ι V) (i : ι) (v : V) (hi : i ∈ s.labels) :
    totalCandidates (child R cost s i v) + (s.candidates i).card ≤ totalCandidates s := by
  have hfilter : (∑ j ∈ s.labels.erase i, ((child R cost s i v).candidates j).card) ≤
      ∑ j ∈ s.labels.erase i, (s.candidates j).card := by
    apply Finset.sum_le_sum
    intro j hj
    exact Finset.card_filter_le _ _
  have heq := Finset.sum_erase_add s.labels (fun j => (s.candidates j).card) hi
  dsimp only at heq
  change (∑ j ∈ s.labels.erase i, ((child R cost s i v).candidates j).card) +
    (s.candidates i).card ≤ ∑ j ∈ s.labels, (s.candidates j).card
  omega

/-- Across all extraction rounds, at most the original number of candidates are tested. -/
theorem recover_calls_le (oracle : State ι V → Bool) :
    ∀ fuel s, (recover R cost oracle fuel s).2 ≤ totalCandidates s := by
  intro fuel
  induction fuel with
  | zero => intro s; simp [recover]; split <;> simp
  | succ fuel ih =>
    intro s
    by_cases h : s.labels.Nonempty
    · simp only [recover, dif_pos h]
      let i := s.labels.min' h
      let probe := firstYes (fun v => oracle (child R cost s i v))
        ((s.candidates i).sort (· ≤ ·))
      have hprobe : probe.2 ≤ (s.candidates i).card := by
        simpa [probe] using firstYes_calls_le
          (fun v => oracle (child R cost s i v)) ((s.candidates i).sort (· ≤ ·))
      cases hp : probe.1 with
      | none =>
        simp only [show (firstYes (fun v => oracle (child R cost s (s.labels.min' h) v))
          ((s.candidates (s.labels.min' h)).sort (· ≤ ·))).1 = none from hp]
        have hc : (s.candidates i).card ≤ totalCandidates s :=
          Finset.single_le_sum (f := fun j => (s.candidates j).card)
            (fun _ _ => Nat.zero_le _) (s.labels.min'_mem h)
        exact hprobe.trans hc
      | some v =>
        simp only [show (firstYes (fun v => oracle (child R cost s (s.labels.min' h) v))
          ((s.candidates (s.labels.min' h)).sort (· ≤ ·))).1 = some v from hp]
        have ht := ih (child R cost s i v)
        have hc := totalCandidates_child_le R cost s i v (s.labels.min'_mem h)
        change probe.2 + (recover R cost oracle fuel (child R cost s i v)).2 ≤ totalCandidates s
        omega
    · simp [recover, h]; split <;> simp

/-- Empty residual states are completed by the fixed default map. -/
theorem completion_empty (s : State ι V) (he : s.labels = ∅) (hb : 0 ≤ s.budget)
    (x : ι → V) : Completion R cost s x := by
  simp [Completion, he, hb]

theorem feasible_budget_nonneg (nonneg : ∀ i v, 0 ≤ cost i v)
    (s : State ι V) (hs : Feasible R cost s) : 0 ≤ s.budget := by
  rcases hs with ⟨x, hx⟩
  exact le_trans (Finset.sum_nonneg (fun i _ => nonneg i (x i))) hx.2.2

/-- Exact witness reconstruction from any decision oracle already proved correct.
No independent-transversal construction is assumed at affordable-prefix leaves. -/
theorem recover_correct (symm : Symmetric R) (nonneg : ∀ i v, 0 ≤ cost i v)
    (oracle : State ι V → Bool)
    (horacle : ∀ s, Affordable cost s → (oracle s = true ↔ Feasible R cost s)) :
    ∀ fuel s, s.labels.card ≤ fuel → Feasible R cost s →
      ∃ x, (recover R cost oracle fuel s).1 = some x ∧ Completion R cost s x := by
  intro fuel
  induction fuel with
  | zero =>
    intro s hcard hs
    have he : s.labels = ∅ := Finset.card_eq_zero.mp (by omega)
    have hb := feasible_budget_nonneg R cost nonneg s hs
    exact ⟨fun _ => default, by simp [recover, he, hb], completion_empty R cost s he hb _⟩
  | succ fuel ih =>
    intro s hcard hs
    by_cases h : s.labels.Nonempty
    · let i := s.labels.min' h
      have hi : i ∈ s.labels := s.labels.min'_mem h
      have hex := (feasible_iff_some_child R cost symm nonneg s i hi).mp hs
      have hprobe : ∃ v, (firstYes (fun v => oracle (child R cost s i v))
          ((s.candidates i).sort (· ≤ ·))).1 = some v := by
        apply firstYes_exists
        rcases hex with ⟨v, hv, hchild⟩
        exact ⟨v, (Finset.mem_sort (· ≤ ·)).mpr hv,
          (horacle _ (child_affordable R cost s i v)).mpr hchild⟩
      rcases hprobe with ⟨v, hp⟩
      have hvs := firstYes_some _ _ _ hp
      have hv : v ∈ s.candidates i := (Finset.mem_sort (· ≤ ·)).mp hvs.1
      have hchild := (horacle _ (child_affordable R cost s i v)).mp hvs.2
      have hchildcard : (child R cost s i v).labels.card ≤ fuel := by
        have := child_rank_lt R cost s i v hi
        omega
      rcases ih (child R cost s i v) hchildcard hchild with ⟨x, hx, hcompletion⟩
      refine ⟨Function.update x i v, ?_, completion_extend R cost symm s i v hi hv x hcompletion⟩
      simp only [recover, dif_pos h]
      change (match (firstYes (fun v => oracle (child R cost s i v))
          ((s.candidates i).sort (· ≤ ·))).1 with
        | none => (none, _)
        | some v => ((recover R cost oracle fuel (child R cost s i v)).1.map
            (fun x => Function.update x i v), _)).1 = some (Function.update x i v)
      simp [hp, hx]
    · have he : s.labels = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
      have hb := feasible_budget_nonneg R cost nonneg s hs
      exact ⟨fun _ => default, by simp [recover, h, hb], completion_empty R cost s he hb _⟩

end IndependentSetDiscovery.Algorithms
