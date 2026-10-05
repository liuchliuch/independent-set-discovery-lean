import IndependentSetDiscovery.Algorithms.EagerBounds
import IndependentSetDiscovery.Algorithms.EagerOptimization
import IndependentSetDiscovery.Algorithms.OptimizationWork

/-! Bounds on the counters returned by the measured optimization programs. -/
namespace IndependentSetDiscovery.Algorithms

theorem probeMeasured_cost_le (p : α → Bool × ℕ) (C : ℕ)
    (hp : ∀ a, (p a).2 ≤ C) (xs : List α) :
    (probeMeasured p xs).2 ≤ xs.length*(C+1) := by
  induction xs with
  | nil => simp [probeMeasured]
  | cons a as ih =>
    have ha := hp a
    cases h : (p a).1 <;> simp only [probeMeasured, h, Bool.false_eq_true,
      ↓reduceIte, List.length_cons, Nat.add_mul] <;> omega

theorem bisectMeasured_cost_le (p : ℕ → Bool × ℕ) (C : ℕ)
    (hp : ∀ a, (p a).2 ≤ C) : ∀ fuel lo hi,
    (bisectMeasured p fuel lo hi).2 ≤ fuel*(C+4) := by
  intro fuel
  induction fuel with
  | zero => intro lo hi; simp [bisectMeasured]
  | succ fuel ih =>
    intro lo hi
    have hm := hp ((lo+hi)/2)
    have hl := ih lo ((lo+hi)/2)
    have hr := ih ((lo+hi)/2+1) hi
    cases h : (p ((lo+hi)/2)).1 <;>
      simp only [bisectMeasured, h, Bool.false_eq_true, ↓reduceIte, Nat.add_mul] <;> omega

theorem leastBudgetMeasured_cost_le (p : ℕ → Bool × ℕ) (C : ℕ)
    (hp : ∀ a, (p a).2 ≤ C) (U : ℕ) :
    (leastBudgetMeasured p U).2 ≤ (Nat.log2 U+2)*(C+4) := by
  have hu := hp U
  have hb := bisectMeasured_cost_le p C hp (Nat.log2 U+1) 0 U
  cases h : (p U).1 <;>
    simp only [leastBudgetMeasured, h, Bool.false_eq_true, ↓reduceIte] <;> nlinarith

/-- The cost of one self-reduction level, including all attempted children. -/
def recoveryNodeBound (k n C : ℕ) : ℕ :=
  n*(4*(k+1)*(n+1)+C+1) + 4*(n+1)^2 + 2*(k+1) +
    4*(k+1)*(n+1) + 3

variable (R : Fin n → Fin n → Prop) [DecidableRel R]
variable (cost : Fin k → Fin n → ℚ)

theorem recoverMeasured_cost_le [Inhabited (Fin n)]
    (oracle : EagerState k n → Bool × ℕ) (C : ℕ)
    (horacle : ∀ s, (oracle s).2 ≤ C) : ∀ fuel s,
    (recoverMeasured R cost oracle fuel s).2 ≤ (fuel+1)*recoveryNodeBound k n C := by
  have hbound : 2 ≤ recoveryNodeBound k n C := by unfold recoveryNodeBound; omega
  intro fuel
  induction fuel with
  | zero =>
    intro s
    simp only [recoverMeasured]
    split_ifs <;> simp only [Nat.zero_add, Nat.one_mul] <;> exact hbound
  | succ fuel ih =>
    intro s
    have hbase : 2 ≤ (fuel+1+1)*recoveryNodeBound k n C := by nlinarith
    by_cases hs : s.labels.Nonempty
    · let i := s.labels.min' hs
      have hrow : (s.rows[i]).card ≤ n := by simpa using Finset.card_le_univ (s.rows[i])
      have hl : s.labels.card ≤ k := by simpa using Finset.card_le_univ s.labels
      have hchild : eagerChildWork s ≤ 4*(k+1)*(n+1) := by
        have := eagerChildWork_add_one_le s
        omega
      have hprobe := probeMeasured_cost_le
        (fun v => let answer := oracle (eagerChild R cost s i v)
          (answer.1, eagerChildWork s+answer.2)) (4*(k+1)*(n+1)+C)
        (fun v => Nat.add_le_add hchild (horacle _)) ((s.rows[i]).sort (· ≤ ·))
      rw [Finset.length_sort] at hprobe
      have hprobe' : (probeMeasured
          (fun v => let answer := oracle (eagerChild R cost s i v)
            (answer.1, eagerChildWork s+answer.2)) ((s.rows[i]).sort (· ≤ ·))).2 ≤
            n*(4*(k+1)*(n+1)+C+1) :=
        hprobe.trans (Nat.mul_le_mul_right _ hrow)
      have hoverhead : 4*((s.rows[i]).card+1)^2 + 2*(s.labels.card+1) ≤
          4*(n+1)^2+2*(k+1) := by gcongr
      simp only [recoverMeasured, dif_pos hs]
      split
      · dsimp only
        unfold recoveryNodeBound at *
        nlinarith
      · rename_i v hv
        have ht := ih (eagerChild R cost s i v)
        dsimp only
        change _ ≤ (fuel+1+1)*recoveryNodeBound k n C
        unfold recoveryNodeBound at *
        nlinarith
    · simp only [recoverMeasured, dif_neg hs]
      split_ifs <;> exact hbase

/-- A uniform oracle bound for all residual states of the encoded instance. -/
def eagerOracleBound (k n maxThreshold : ℕ) : ℕ :=
  128*(k+1)^2*(n+1)^2 * treeBound (k*maxThreshold) k

theorem eagerDecide_uniform_cost_le (threshold : ℕ → ℕ) (maxThreshold : ℕ)
    (hthreshold : ∀ r ≤ k, threshold r ≤ maxThreshold) (s : EagerState k n) :
    (eagerDecide R cost threshold s).2 ≤ eagerOracleBound k n maxThreshold := by
  have hl : s.labels.card ≤ k := by simpa using Finset.card_le_univ s.labels
  exact (eagerDecide_cost_le R cost threshold maxThreshold hthreshold s).trans
    (Nat.mul_le_mul_left _ (treeBound_mono_depth _ hl))

/-- The elementary self-reduction passes are absorbed by one decision's
polynomial factor per scanned vertex. -/
theorem recoveryNodeBound_le_oracle (k n C : ℕ)
    (hC : 128*(k+1)^2*(n+1)^2 ≤ C) :
    recoveryNodeBound k n C ≤ (n+1)*C := by
  let P := (k+1)^2*(n+1)^2
  have hk : k+1 ≤ (k+1)^2 := by nlinarith
  have hn : n+1 ≤ (n+1)^2 := by nlinarith
  have hk1 : 1 ≤ (k+1)^2 := by nlinarith
  have hn1 : 1 ≤ (n+1)^2 := by nlinarith
  have hA : (k+1)^2 ≤ P := by
    calc
      _ = (k+1)^2*1 := by omega
      _ ≤ _ := Nat.mul_le_mul_left _ hn1
  have hB : (n+1)^2 ≤ P := by
    calc
      _ = 1*(n+1)^2 := by omega
      _ ≤ _ := Nat.mul_le_mul_right _ hk1
  have hAB : (k+1)*(n+1) ≤ P := Nat.mul_le_mul hk hn
  have hnAB : n*(k+1)*(n+1) ≤ P := by
    calc
      _ ≤ (n+1)*(k+1)*(n+1) := by gcongr; omega
      _ ≤ (n+1)*((k+1)^2)*(n+1) := by gcongr
      _ = _ := by dsimp [P]; ring
  have hCP : 128*P ≤ C := by simpa only [P, Nat.mul_assoc] using hC
  unfold recoveryNodeBound
  nlinarith

/-- A measured self-reduction takes at most `fuel+1` vertex scans, with the
concrete eager decision cost charged for every attempted child. -/
theorem recoverEager_cost_le [Inhabited (Fin n)] (threshold : ℕ → ℕ)
    (maxThreshold : ℕ) (hthreshold : ∀ r ≤ k, threshold r ≤ maxThreshold)
    (fuel : ℕ) (s : EagerState k n) :
    (recoverMeasured R cost (eagerDecide R cost threshold) fuel s).2 ≤
      (fuel+1)*(n+1)*eagerOracleBound k n maxThreshold := by
  have hC : 128*(k+1)^2*(n+1)^2 ≤ eagerOracleBound k n maxThreshold := by
    exact Nat.le_mul_of_pos_right _ (one_le_treeBound _ _)
  calc
    _ ≤ (fuel+1)*recoveryNodeBound k n (eagerOracleBound k n maxThreshold) :=
      recoverMeasured_cost_le R cost _ _
        (eagerDecide_uniform_cost_le R cost threshold maxThreshold hthreshold) fuel s
    _ ≤ (fuel+1)*((n+1)*eagerOracleBound k n maxThreshold) :=
      Nat.mul_le_mul_left _ (recoveryNodeBound_le_oracle k n _ hC)
    _ = _ := by ring

/-- Binary optimization and measured witness extraction have one fixed
polynomial factor times the same bounded search tree. -/
theorem optimizeEager_search_cost_le [Inhabited (Fin n)] (threshold : ℕ → ℕ)
    (maxThreshold : ℕ) (hthreshold : ∀ r ≤ k, threshold r ≤ maxThreshold)
    (L : Finset (Fin k)) (rows : Vector (Finset (Fin n)) k) :
    (optimizeEager R cost threshold L rows).2 ≤
      ((Nat.log2 (upperBudget L (fun i => rows[i])
          (scaledCosts L (fun i => rows[i]) cost))+2)*2 + (k+1)*(n+1)) *
        eagerOracleBound k n maxThreshold := by
  let U := upperBudget L (fun i => rows[i]) (scaledCosts L (fun i => rows[i]) cost)
  let D := commonDenominator L (fun i => rows[i]) cost
  let C := eagerOracleBound k n maxThreshold
  let initial := fun b : ℕ => EagerState.mk L rows ((b : ℚ)/D)
  let p := fun b => eagerDecide R cost threshold (initial b)
  have hp : ∀ b, (p b).2 ≤ C :=
    fun b => eagerDecide_uniform_cost_le R cost threshold maxThreshold hthreshold (initial b)
  have hc : 4 ≤ C := by
    have hT := one_le_treeBound (k*maxThreshold) k
    have hk : 1 ≤ (k+1)^2 := Nat.one_le_pow _ _ (by omega)
    have hn : 1 ≤ (n+1)^2 := Nat.one_le_pow _ _ (by omega)
    dsimp [C, eagerOracleBound]
    calc
      4 ≤ 128*1*1*1 := by norm_num
      _ ≤ _ := by gcongr
  have hsearch : (leastBudgetMeasured p U).2 ≤ (Nat.log2 U+2)*2*C := by
    exact (leastBudgetMeasured_cost_le p C hp U).trans
      (by have := Nat.mul_le_mul_left (Nat.log2 U+2) (by omega : C+4 ≤ 2*C); nlinarith)
  have hl : L.card ≤ k := by simpa using Finset.card_le_univ L
  have hw (b : ℕ) :
      (recoverMeasured R cost (eagerDecide R cost threshold) L.card (initial b)).2 ≤
        (k+1)*(n+1)*C := by
    exact (recoverEager_cost_le R cost threshold maxThreshold hthreshold _ _).trans
      (by gcongr)
  change (match (leastBudgetMeasured p U).1 with
    | none => (none, (leastBudgetMeasured p U).2)
    | some b => ((recoverMeasured R cost (eagerDecide R cost threshold) L.card (initial b)).1,
      (leastBudgetMeasured p U).2+
        (recoverMeasured R cost (eagerDecide R cost threshold) L.card (initial b)).2)).2 ≤ _
  split
  · dsimp only
    change _ ≤ ((Nat.log2 U+2)*2+(k+1)*(n+1))*C
    exact hsearch.trans (Nat.mul_le_mul_right C (Nat.le_add_right _ _))
  · rename_i b hb
    dsimp only
    have hh := hw b
    change _ ≤ ((Nat.log2 U+2)*2+(k+1)*(n+1))*C
    nlinarith

/-- The binary numeric input size bounds the complete measured search,
including every unsuccessful witness probe. -/
theorem optimizeEager_cost_le [Inhabited (Fin n)] (threshold : ℕ → ℕ)
    (maxThreshold : ℕ) (hthreshold : ∀ r ≤ k, threshold r ≤ maxThreshold)
    (L : Finset (Fin k)) (rows : Vector (Finset (Fin n)) k) :
    (optimizeEager R cost threshold L rows).2 ≤
      (6*numericSize L (fun i => rows[i]) cost+4+(k+1)*(n+1)) *
        (128*(k+1)^2*(n+1)^2) * treeBound (k*maxThreshold) k := by
  have hnum := optimizationCalls_le_numericSize L (fun i => rows[i]) cost
  have hsearch := optimizeEager_search_cost_le R cost threshold maxThreshold hthreshold L rows
  calc
    _ ≤ (6*numericSize L (fun i => rows[i]) cost+4+(k+1)*(n+1)) *
        eagerOracleBound k n maxThreshold := by
      apply hsearch.trans
      apply Nat.mul_le_mul_right
      unfold optimizationCalls at hnum
      omega
    _ = _ := by unfold eagerOracleBound; ring

end IndependentSetDiscovery.Algorithms
