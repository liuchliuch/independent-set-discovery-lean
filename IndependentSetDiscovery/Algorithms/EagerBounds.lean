import IndependentSetDiscovery.Algorithms.EagerMachine
import IndependentSetDiscovery.Algorithms.MeasuredExecution

/-!
# Bounds for the concrete eager machine

The node counter is the second component returned by `eagerStepCounted`.
The recursive bounds sum this counter over the actual computed children.
-/
namespace IndependentSetDiscovery.Algorithms

variable (R : Fin n → Fin n → Prop) [DecidableRel R]
variable (cost : Fin k → Fin n → ℚ) (threshold : ℕ → ℕ)

/-- The finite-table polynomial envelope, independent of the threshold. -/
def eagerPolynomial (k n : ℕ) : ℕ := (k+1)^2 * (n+1)^2

private theorem eagerPolynomial_facts (k n : ℕ) :
    1 ≤ eagerPolynomial k n ∧
    (k+1)^2 ≤ eagerPolynomial k n ∧
    (k+1)*(n+1) ≤ eagerPolynomial k n ∧
    k*(n+1)^2 ≤ eagerPolynomial k n ∧
    k^2 ≤ eagerPolynomial k n ∧ k ≤ eagerPolynomial k n := by
  have hk : k+1 ≤ (k+1)^2 := by nlinarith
  have hn : n+1 ≤ (n+1)^2 := by nlinarith
  have hk' : k ≤ (k+1)^2 := by omega
  have hn' : 1 ≤ (n+1)^2 := by nlinarith
  have hkk : (k+1)^2 ≤ eagerPolynomial k n := by
    unfold eagerPolynomial
    calc
      (k+1)^2 = (k+1)^2 * 1 := by omega
      _ ≤ _ := Nat.mul_le_mul_left ((k+1)^2) hn'
  refine ⟨?_, hkk, ?_, ?_, ?_, ?_⟩
  · nlinarith
  · exact Nat.mul_le_mul hk hn
  · exact Nat.mul_le_mul_right _ hk'
  · nlinarith
  · omega

theorem eagerBaseWork_le (s : EagerState k n) :
    eagerBaseWork s ≤ 16 * eagerPolynomial k n := by
  have hl : s.labels.card ≤ k := by simpa using Finset.card_le_univ s.labels
  have hp := eagerPolynomial_facts k n
  have hs : (s.labels.card+1)^2 ≤ eagerPolynomial k n :=
    (Nat.pow_le_pow_left (by omega : s.labels.card+1 ≤ k+1) 2).trans hp.2.1
  have hm : (k+1)*(n+3) ≤ 3*eagerPolynomial k n := by
    have : (k+1)*(n+3) ≤ 3*((k+1)*(n+1)) := by nlinarith
    exact this.trans (Nat.mul_le_mul_left 3 hp.2.2.1)
  unfold eagerBaseWork
  omega

theorem eagerChildWork_add_one_le (s : EagerState k n) :
    eagerChildWork s + 1 ≤ 4*(k+1)*(n+1) := by
  have := eagerChildWork_le s
  nlinarith

private theorem measuredPrefix_card_le (i : Fin k) (s : EagerState k n) :
    (measuredPrefix (cost i) (s.rows[i]) (threshold s.labels.card)).1.card ≤ n := by
  simpa using Finset.card_le_univ
    (measuredPrefix (cost i) (s.rows[i]) (threshold s.labels.card)).1

private theorem eagerPrefixWork_le (s : EagerState k n) :
    (∑ i : Fin k, (measuredPrefix (cost i) (s.rows[i])
      (threshold s.labels.card)).2.2) ≤ 12 * eagerPolynomial k n := by
  calc
    _ ≤ ∑ _i : Fin k, 12*(n+1)^2 := by
      apply Finset.sum_le_sum
      intro i hi
      have hc : (s.rows[i]).card ≤ n := by simpa using Finset.card_le_univ (s.rows[i])
      exact (measuredPrefix_spec (cost i) (s.rows[i]) _).2.2.trans
        (Nat.mul_le_mul_left 12 (Nat.pow_le_pow_left (by omega) 2))
    _ = 12*(k*(n+1)^2) := by simp; ring
    _ ≤ _ := Nat.mul_le_mul_left 12 (eagerPolynomial_facts k n).2.2.2.1

private theorem eagerPrefixSortWork_le (s : EagerState k n) :
    (∑ i ∈ s.labels, 4*(measuredPrefix (cost i) (s.rows[i])
      (threshold s.labels.card)).1.card^2) ≤ 4 * eagerPolynomial k n := by
  have hl : s.labels.card ≤ k := by simpa using Finset.card_le_univ s.labels
  calc
    _ ≤ ∑ _i ∈ s.labels, 4*(n+1)^2 := by
      apply Finset.sum_le_sum
      intro i hi
      exact Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left
        ((measuredPrefix_card_le cost threshold i s).trans (Nat.le_succ n)) 2)
    _ = 4*(s.labels.card*(n+1)^2) := by simp; ring
    _ ≤ 4*(k*(n+1)^2) := by gcongr
    _ ≤ _ := Nat.mul_le_mul_left 4 (eagerPolynomial_facts k n).2.2.2.1

private theorem eagerChoices_length_le (s : EagerState k n) :
    ((s.labels.sort (· ≤ ·)).flatMap fun i =>
      ((measuredPrefix (cost i) (s.rows[i]) (threshold s.labels.card)).1.sort
        (· ≤ ·)).map fun v => eagerChild R cost s i v).length ≤ k*n := by
  have hl : s.labels.card ≤ k := by simpa using Finset.card_le_univ s.labels
  simp only [List.length_flatMap, List.length_map, Finset.length_sort]
  calc
    _ ≤ (s.labels.sort (· ≤ ·)).length * n :=
      list_sum_le_length_mul (fun i _ => measuredPrefix_card_le cost threshold i s)
    _ ≤ k*n := by rw [Finset.length_sort]; exact Nat.mul_le_mul_right n hl

private theorem eagerChildrenWork_le (s : EagerState k n) (a : ℕ) (ha : a ≤ k*n) :
    a*(eagerChildWork s+1) ≤ 4*eagerPolynomial k n := by
  have hkn : k*n ≤ (k+1)*(n+1) := Nat.mul_le_mul (Nat.le_succ _) (Nat.le_succ _)
  calc
    _ ≤ ((k+1)*(n+1))*(4*(k+1)*(n+1)) :=
      Nat.mul_le_mul (ha.trans hkn) (eagerChildWork_add_one_le s)
    _ = _ := by unfold eagerPolynomial; ring

/-- Every branch of the concrete counted program has a polynomial node cost. -/
theorem eagerStepCounted_cost_le (s : EagerState k n) :
    (eagerStepCounted R cost threshold s).2 ≤ 128*(k+1)^2*(n+1)^2 := by
  have hl : s.labels.card ≤ k := by simpa using Finset.card_le_univ s.labels
  have hp := eagerPolynomial_facts k n
  have hb := eagerBaseWork_le s
  have hpre := eagerPrefixWork_le cost threshold s
  have hsort := eagerPrefixSortWork_le cost threshold s
  have hc := eagerChildrenWork_le s _ (eagerChoices_length_le R cost threshold s)
  have hl2 : s.labels.card^2 ≤ eagerPolynomial k n :=
    (Nat.pow_le_pow_left hl 2).trans hp.2.2.2.2.1
  have hlast : 128*eagerPolynomial k n = 128*(k+1)^2*(n+1)^2 := by
    unfold eagerPolynomial; ring
  rw [← hlast]
  have hvec (i : Fin k) : (Vector.ofFn fun j : Fin k =>
      measuredPrefix (cost j) (s.rows[j]) (threshold s.labels.card))[i] =
      measuredPrefix (cost i) (s.rows[i]) (threshold s.labels.card) := by simp
  unfold eagerStepCounted
  split_ifs with hbudget hempty hsmall
  · dsimp; omega
  · dsimp; omega
  · dsimp only
    rw [Finset.length_sort]
    have hrow : (s.rows[(smallLabels threshold s.toState).min' hsmall]).card ≤ n := by
      simpa using Finset.card_le_univ (s.rows[(smallLabels threshold s.toState).min' hsmall])
    have hk : 1 ≤ k := by
      have : (smallLabels threshold s.toState).min' hsmall ∈ s.labels :=
        (Finset.mem_filter.mp ((smallLabels threshold s.toState).min'_mem hsmall)).1
      have : 0 < s.labels.card := Finset.card_pos.mpr ⟨_, this⟩
      omega
    have hr2 : (s.rows[(smallLabels threshold s.toState).min' hsmall]).card^2 ≤
        eagerPolynomial k n := by
      have : n^2 ≤ (k+1)^2*(n+1)^2 := by
        have hnp : n^2 ≤ (n+1)^2 := Nat.pow_le_pow_left (Nat.le_succ _) 2
        have hkp : 1 ≤ (k+1)^2 := by nlinarith
        exact hnp.trans (by
          calc
            (n+1)^2 = 1*((n+1)^2) := by omega
            _ ≤ _ := Nat.mul_le_mul_right ((n+1)^2) hkp)
      exact (Nat.pow_le_pow_left hrow 2).trans this
    have hcc := eagerChildrenWork_le s
      (s.rows[(smallLabels threshold s.toState).min' hsmall]).card
      (hrow.trans (by nlinarith : n ≤ k*n))
    omega
  · dsimp only
    split_ifs with haffordable <;> simp only [hvec] <;> omega

/-- Uniform node bounds compose on the exact recursive instruction tree. -/
theorem runWork_le_uniform (step : σ → Instruction σ) (charge : σ → ℕ)
    (bound : ℕ) (hcharge : ∀ s, charge s ≤ bound) :
    ∀ fuel s, runWork step charge fuel s ≤ bound * (run step fuel s).2 := by
  intro fuel
  induction fuel with
  | zero =>
    intro s
    cases hs : step s <;> simpa [runWork, run, hs] using hcharge s
  | succ fuel ih =>
    intro s
    cases hs : step s with
    | yes => simpa [runWork, run, hs] using hcharge s
    | no => simpa [runWork, run, hs] using hcharge s
    | branch children =>
      have hsum : (children.map (runWork step charge fuel)).sum ≤
          bound * (children.map (fun t => (run step fuel t).2)).sum := by
        rw [← List.sum_map_mul_left]
        exact List.sum_le_sum (fun t _ => ih t)
      simp only [runWork, run, hs, List.map_map, Function.comp_def]
      nlinarith [hcharge s]

/-- The eager program obeys precisely the cheap-prefix branching bound. -/
theorem eagerStep_branching (s : EagerState k n)
    (children : List (EagerState k n))
    (hstep : eagerStep R cost threshold s = .branch children) :
    children.length ≤ s.labels.card * threshold s.labels.card := by
  have hpref (i : Fin k) := (measuredPrefix_spec (cost i) (s.rows[i])
    (threshold s.labels.card)).1
  have hvec (i : Fin k) : (Vector.ofFn fun j : Fin k =>
      measuredPrefix (cost j) (s.rows[j]) (threshold s.labels.card))[i] =
      measuredPrefix (cost i) (s.rows[i]) (threshold s.labels.card) := by simp
  unfold eagerStep eagerStepCounted at hstep
  simp only [hvec, hpref] at hstep
  split_ifs at hstep with hb he hs ha
  · injection hstep with hc
    subst children
    rw [List.length_map, Finset.length_sort]
    have hi := (smallLabels threshold s.toState).min'_mem hs
    have hsmall := (Finset.mem_filter.mp hi).2
    have hcard : 1 ≤ s.labels.card :=
      Finset.card_pos.mpr ⟨_, (Finset.mem_filter.mp hi).1⟩
    change (s.rows[(smallLabels threshold s.toState).min' hs]).card <
      threshold s.labels.card at hsmall
    nlinarith
  · injection hstep with hc
    subst children
    simp only [List.length_flatMap, List.length_map, Finset.length_sort]
    calc
      _ ≤ (s.labels.sort (· ≤ ·)).length * threshold s.labels.card := by
        apply list_sum_le_length_mul
        intro i hi
        rw [card_cheapPrefix]
        exact Nat.min_le_left _ _
      _ = _ := by rw [Finset.length_sort]

/-- The returned work is bounded on its actual execution tree, with no oracle
cost or assumed implementation of prefix operations. -/
theorem eagerExecute_cost_le (maxThreshold : ℕ)
    (hthreshold : ∀ r ≤ k, threshold r ≤ maxThreshold)
    (fuel : ℕ) (s : EagerState k n) :
    (execute (eagerStepCounted R cost threshold) fuel s).2 ≤
      (128*(k+1)^2*(n+1)^2) * treeBound (k*maxThreshold) fuel := by
  rw [(execute_spec _ _ _).2]
  change runWork (eagerStep R cost threshold)
    (fun t => (eagerStepCounted R cost threshold t).2) fuel s ≤ _
  have hnodes : (run (eagerStep R cost threshold) fuel s).2 ≤
      treeBound (k*maxThreshold) fuel := by
    apply run_cost_le
    intro t children hstep
    have hl : t.labels.card ≤ k := by simpa using Finset.card_le_univ t.labels
    exact (eagerStep_branching R cost threshold t children hstep).trans
      (Nat.mul_le_mul hl (hthreshold _ hl))
  exact (runWork_le_uniform _ _ _ (eagerStepCounted_cost_le R cost threshold) fuel s).trans
    (Nat.mul_le_mul_left _ hnodes)

/-- Complete concrete decision cost with the standard finite tree bound. -/
theorem eagerDecide_cost_le (maxThreshold : ℕ)
    (hthreshold : ∀ r ≤ k, threshold r ≤ maxThreshold) (s : EagerState k n) :
    (eagerDecide R cost threshold s).2 ≤
      (128*(k+1)^2*(n+1)^2) * treeBound (k*maxThreshold) s.labels.card :=
  eagerExecute_cost_le R cost threshold maxThreshold hthreshold _ s

/-- A closed bound, valid also for branching factors zero and one. -/
theorem eagerDecide_cost_le_power (maxThreshold : ℕ)
    (hthreshold : ∀ r ≤ k, threshold r ≤ maxThreshold) (s : EagerState k n) :
    (eagerDecide R cost threshold s).2 ≤
      (128*(k+1)^2*(n+1)^2) * (k*maxThreshold+1)^s.labels.card :=
  (eagerDecide_cost_le R cost threshold maxThreshold hthreshold s).trans
    (Nat.mul_le_mul_left _ (treeBound_le_power _ _))

/-- The paper's geometric-tree form when branching is at least two. -/
theorem eagerDecide_cost_le_geometric (maxThreshold : ℕ)
    (hthreshold : ∀ r ≤ k, threshold r ≤ maxThreshold)
    (hbranching : 2 ≤ k*maxThreshold) (s : EagerState k n) :
    (eagerDecide R cost threshold s).2 ≤
      (256*(k+1)^2*(n+1)^2) * (k*maxThreshold)^s.labels.card := by
  have ht := treeBound_add_one_le (k*maxThreshold) s.labels.card hbranching
  have hb := eagerDecide_cost_le R cost threshold maxThreshold hthreshold s
  calc
    _ ≤ (128*(k+1)^2*(n+1)^2) * (2*(k*maxThreshold)^s.labels.card) :=
      hb.trans (Nat.mul_le_mul_left _ (by omega))
    _ = _ := by ring

end IndependentSetDiscovery.Algorithms
